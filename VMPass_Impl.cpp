#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/Twine.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include "llvm/Transforms/Obfuscator/VMPass_Impl.h"
#include "llvm/Transforms/Obfuscator/VMPass_ISA.h"
#include "llvm/Transforms/Obfuscator/VMPass_Emitter.h"
#include "llvm/Transforms/Obfuscator/VMPass_Verifier.h"
#include "llvm/Transforms/Obfuscator/ObfuscationOptions.h"

#include <functional>
using namespace llvm;

#define DEBUG_TYPE "vm"

STATISTIC(VMFunctions, "Functions virtualised by VMPass");



bool VMImpl::run() {
	// Demote PHI nodes to memory
	SmallVector<PHINode*, 32> Phis;
	for (BasicBlock& BB : F)
		for (Instruction& I : BB)
			if (auto* PN = dyn_cast<PHINode>(&I)) Phis.push_back(PN);
	for (PHINode* PN : Phis) DemotePHIToStack(PN);






	//     Lower/strip intrinsics that clang emits at -O0 but the VM cannot
	//      encode.  Three tiers:
	//        A) Strip  — debug, lifetime, assume, expect, freeze: zero/identity.
	//        B) Memory — memcpy/memset/memmove const size ≤ 1024: chunked
	//                    i64/i32/i16/i8 load+store (or store-of-fill). memmove
	//                    uses an entry alloca temp then two forward copies.
	//        C) Float  — fabs, fmuladd, fma, minnum, maxnum, copysign:
	//                    expand to FNeg/FMul/FAdd/FCmp/Select the VM handles.
	//        D) Int    — abs; umul.with.overflow (i32/i64); ctpop (i32/i64):
	//                    expand to IR the VM already encodes.
	//      Also: load {i64,i64} with extractvalue-only users → two i64 loads.
	//      Anything else stays and isize() will markUnsupported gracefully.
	{
		constexpr uint64_t kMemExpandMax = 1024;

		auto emitMemChunks = [&](IRBuilder<>& B, Value* Dst, Value* Src,
			uint64_t Sz, uint8_t FillByte, bool IsSet) {
			uint64_t Off = 0;
			auto chunk = [&](Type* Ty, unsigned Bytes) {
				while (Sz - Off >= Bytes) {
					Value* DPtr = Off ? B.CreateGEP(I8Ty, Dst, B.getInt64(Off), "mc.dp")
						: Dst;
					if (IsSet) {
						uint64_t Pat = 0;
						for (unsigned i = 0; i < Bytes; ++i)
							Pat |= ((uint64_t)FillByte << (i * 8));
						B.CreateStore(ConstantInt::get(Ty, Pat), DPtr);
					} else {
						Value* SPtr = Off ? B.CreateGEP(I8Ty, Src, B.getInt64(Off), "mc.sp")
							: Src;
						B.CreateStore(B.CreateLoad(Ty, SPtr, "mc.ld"), DPtr);
					}
					Off += Bytes;
				}
			};
			chunk(I64Ty, 8);
			chunk(I32Ty, 4);
			chunk(I16Ty, 2);
			chunk(I8Ty, 1);
		};

		// Tier A: freeze → identity (covers freeze i32 and other legal SSA types).
		{
			SmallVector<FreezeInst*, 16> Freezes;
			for (BasicBlock& BB : F)
				for (Instruction& I : BB)
					if (auto* FI = dyn_cast<FreezeInst>(&I))
						Freezes.push_back(FI);
			for (FreezeInst* FI : Freezes) {
				FI->replaceAllUsesWith(FI->getOperand(0));
				FI->eraseFromParent();
			}
		}

		SmallVector<CallInst*, 32> Intrinsics;
		for (BasicBlock& BB : F)
			for (Instruction& I : BB)
				if (auto* CI = dyn_cast<CallInst>(&I))
					if (auto* CF = CI->getCalledFunction(); CF && CF->isIntrinsic())
						Intrinsics.push_back(CI);

		for (CallInst* CI : Intrinsics) {
			Intrinsic::ID IID = CI->getCalledFunction()->getIntrinsicID();
			IRBuilder<> B(CI);

			//  Tier A: strip ─
			switch (IID) {
			case Intrinsic::lifetime_start:
			case Intrinsic::lifetime_end:
			case Intrinsic::dbg_declare:
			case Intrinsic::dbg_value:
			case Intrinsic::dbg_assign:
			case Intrinsic::assume:
				CI->eraseFromParent();
				continue;
			case Intrinsic::expect:
			        CI->replaceAllUsesWith(CI->getArgOperand(0));
			        CI->eraseFromParent();
			        continue;
			default: break;
			}

			//  Tier B: memcpy / memmove (≤1024 chunked)
			if (IID == Intrinsic::memcpy || IID == Intrinsic::memmove) {
				if (auto* SzC = dyn_cast<ConstantInt>(CI->getArgOperand(2))) {
					uint64_t Sz = SzC->getZExtValue();
					if (Sz > 0 && Sz <= kMemExpandMax) {
						Value* Dst = CI->getArgOperand(0);
						Value* Src = CI->getArgOperand(1);
						if (IID == Intrinsic::memmove) {
							// Overlap-safe: entry temp, then src→tmp→dst.
							IRBuilder<> EB(&F.getEntryBlock(),
								F.getEntryBlock().getFirstInsertionPt());
							AllocaInst* Tmp = EB.CreateAlloca(
								ArrayType::get(I8Ty, Sz), nullptr, "mm.tmp");
							emitMemChunks(B, Tmp, Src, Sz, 0, /*IsSet=*/false);
							emitMemChunks(B, Dst, Tmp, Sz, 0, /*IsSet=*/false);
						} else {
							emitMemChunks(B, Dst, Src, Sz, 0, /*IsSet=*/false);
						}
						CI->eraseFromParent();
						continue;
					}
				}
				continue; // non-constant / too large → markUnsupported later
			}

			//  Tier B: memset (≤1024 chunked)
			if (IID == Intrinsic::memset) {
				auto* SzC = dyn_cast<ConstantInt>(CI->getArgOperand(2));
				auto* ValC = dyn_cast<ConstantInt>(CI->getArgOperand(1));
				if (SzC && ValC) {
					uint64_t Sz = SzC->getZExtValue();
					if (Sz > 0 && Sz <= kMemExpandMax) {
						emitMemChunks(B, CI->getArgOperand(0), nullptr, Sz,
							(uint8_t)ValC->getZExtValue(), /*IsSet=*/true);
						CI->eraseFromParent();
						continue;
					}
				}
				continue;
			}

			//  Tier C: fabs(x) → x >= 0.0 ? x : -x 
			if (IID == Intrinsic::fabs) {
				Value* X = CI->getArgOperand(0);
				Type* FT = X->getType();
				Value* Neg = B.CreateFNeg(X, "fabs.neg");
				Value* Cmp = B.CreateFCmpOGE(X, ConstantFP::get(FT, 0.0), "fabs.cmp");
				Value* R = B.CreateSelect(Cmp, X, Neg, "fabs.r");
				CI->replaceAllUsesWith(R);
				CI->eraseFromParent();
				continue;
			}

			//  Tier C: fmuladd / fma → a*b + c ─
			if (IID == Intrinsic::fmuladd || IID == Intrinsic::fma) {
				Value* A = CI->getArgOperand(0);
				Value* Bv = CI->getArgOperand(1);
				Value* C = CI->getArgOperand(2);
				Value* R = B.CreateFAdd(B.CreateFMul(A, Bv, "fma.mul"), C, "fma.add");
				CI->replaceAllUsesWith(R);
				CI->eraseFromParent();
				continue;
			}

			//  Tier C: minnum / maxnum 
			if (IID == Intrinsic::minnum) {
				Value* A = CI->getArgOperand(0), * Bv = CI->getArgOperand(1);
				Value* R = B.CreateSelect(B.CreateFCmpOLT(A, Bv, "min.cmp"), A, Bv, "min.r");
				CI->replaceAllUsesWith(R);
				CI->eraseFromParent();
				continue;
			}
			if (IID == Intrinsic::maxnum) {
				Value* A = CI->getArgOperand(0), * Bv = CI->getArgOperand(1);
				Value* R = B.CreateSelect(B.CreateFCmpOGT(A, Bv, "max.cmp"), A, Bv, "max.r");
				CI->replaceAllUsesWith(R);
				CI->eraseFromParent();
				continue;
			}

			//  Tier C: copysign(mag, sgn)
			if (IID == Intrinsic::copysign) {
				Value* Mag = CI->getArgOperand(0);
				Value* Sgn = CI->getArgOperand(1);
				Type* FT = Mag->getType();
				Value* Zero = ConstantFP::get(FT, 0.0);
				Value* NegM = B.CreateFNeg(Mag, "cs.nm");
				Value* AbsM = B.CreateSelect(B.CreateFCmpOGE(Mag, Zero, "cs.ac"), Mag, NegM, "cs.am");
				Value* R = B.CreateSelect(B.CreateFCmpOGE(Sgn, Zero, "cs.sc"),
					AbsM, B.CreateFNeg(AbsM, "cs.na"), "cs.r");
				CI->replaceAllUsesWith(R);
				CI->eraseFromParent();
				continue;
			}

			//  Tier D: abs(x, _) → x < 0 ? -x : x ─
			if (IID == Intrinsic::abs) {
				Value* X = CI->getArgOperand(0);
				Type* IT = X->getType();
				Value* Zero = ConstantInt::get(IT, 0);
				Value* Neg = B.CreateSub(Zero, X, "abs.neg");
				Value* R = B.CreateSelect(B.CreateICmpSLT(X, Zero, "abs.cmp"), Neg, X, "abs.r");
				CI->replaceAllUsesWith(R);
				CI->eraseFromParent();
				continue;
			}

			//  Tier D: umul.with.overflow → {mul, ov} via extractvalue rewrite.
			//  {iN,i1} is not a VM slot type; expand before emit. Only i32/i64.
			if (IID == Intrinsic::umul_with_overflow) {
				Value* A = CI->getArgOperand(0);
				Value* Bv = CI->getArgOperand(1);
				Type* IT = A->getType();
				unsigned BW = IT->isIntegerTy() ? IT->getIntegerBitWidth() : 0;
				if (BW == 32 || BW == 64) {
					bool Ok = true;
					for (User* U : CI->users()) {
						auto* EV = dyn_cast<ExtractValueInst>(U);
						if (!EV || EV->getNumIndices() != 1 || EV->getIndices()[0] > 1) {
							Ok = false;
							break;
						}
					}
					if (Ok) {
						Value* Mul = B.CreateMul(A, Bv, "umul.mul");
						Value* Zero = ConstantInt::get(IT, 0);
						Value* One = ConstantInt::get(IT, 1);
						Value* Max = ConstantInt::get(IT, -1); // UINT_MAX
						// ov = (B != 0) && (A > umax/B); use BSafe so udiv never ÷0.
						Value* BSafe = B.CreateSelect(
							B.CreateICmpEQ(Bv, Zero, "umul.bz"), One, Bv, "umul.bs");
						Value* Ov = B.CreateAnd(
							B.CreateICmpNE(Bv, Zero, "umul.bnz"),
							B.CreateICmpUGT(A, B.CreateUDiv(Max, BSafe, "umul.lim"),
								"umul.gt"),
							"umul.ov");
						SmallVector<ExtractValueInst*, 4> Extracts;
						for (User* U : CI->users())
							Extracts.push_back(cast<ExtractValueInst>(U));
						for (ExtractValueInst* EV : Extracts) {
							EV->replaceAllUsesWith(
								EV->getIndices()[0] == 0 ? Mul : Ov);
							EV->eraseFromParent();
						}
						CI->eraseFromParent();
						continue;
					}
				}
			}

			//  Tier D: ctpop → SWAR parallel bitcount (OP_BINOP-friendly).
			if (IID == Intrinsic::ctpop) {
				Value* X = CI->getArgOperand(0);
				Type* IT = X->getType();
				unsigned BW = IT->isIntegerTy() ? IT->getIntegerBitWidth() : 0;
				if (BW == 32 || BW == 64) {
					auto C = [&](uint64_t V) { return ConstantInt::get(IT, V); };
					auto shr = [&](Value* V, unsigned S, const Twine& N) {
						return B.CreateLShr(V, C(S), N);
					};
					// x = x - ((x >> 1) & 0x5555...)
					Value* T = B.CreateSub(X,
						B.CreateAnd(shr(X, 1, "ct.pop.s1"),
							C(BW == 32 ? 0x55555555ull : 0x5555555555555555ull),
							"ct.pop.a1"),
						"ct.pop.t1");
					// x = (x & 0x3333...) + ((x >> 2) & 0x3333...)
					T = B.CreateAdd(
						B.CreateAnd(T, C(BW == 32 ? 0x33333333ull : 0x3333333333333333ull),
							"ct.pop.a2"),
						B.CreateAnd(shr(T, 2, "ct.pop.s2"),
							C(BW == 32 ? 0x33333333ull : 0x3333333333333333ull),
							"ct.pop.a3"),
						"ct.pop.t2");
					// x = (x + (x >> 4)) & 0x0F0F...
					T = B.CreateAnd(
						B.CreateAdd(T, shr(T, 4, "ct.pop.s4"), "ct.pop.t3"),
						C(BW == 32 ? 0x0F0F0F0Full : 0x0F0F0F0F0F0F0F0Full),
						"ct.pop.t4");
					T = B.CreateAdd(T, shr(T, 8, "ct.pop.s8"), "ct.pop.t5");
					T = B.CreateAdd(T, shr(T, 16, "ct.pop.s16"), "ct.pop.t6");
					if (BW == 64)
						T = B.CreateAdd(T, shr(T, 32, "ct.pop.s32"), "ct.pop.t7");
					Value* R = B.CreateAnd(T, C(BW == 32 ? 0x3Full : 0x7Full), "ct.pop.r");
					CI->replaceAllUsesWith(R);
					CI->eraseFromParent();
					continue;
				}
			}

			// Anything else: leave in place, isize() will markUnsupported.
		}
	}

	// load {i64,i64} is not a VM slot type. When every use is extractvalue
	// 0/1, split into two i64 loads and rewrite the extracts.
	{
		const DataLayout& DL = F.getParent()->getDataLayout();
		SmallVector<LoadInst*, 16> AggLoads;
		for (BasicBlock& BB : F)
			for (Instruction& I : BB) {
				auto* LI = dyn_cast<LoadInst>(&I);
				if (!LI) continue;
				auto* ST = dyn_cast<StructType>(LI->getType());
				if (!ST || ST->getNumElements() != 2) continue;
				if (!ST->getElementType(0)->isIntegerTy(64) ||
					!ST->getElementType(1)->isIntegerTy(64))
					continue;
				bool Ok = !LI->user_empty();
				for (User* U : LI->users()) {
					auto* EV = dyn_cast<ExtractValueInst>(U);
					if (!EV || EV->getNumIndices() != 1 || EV->getIndices()[0] > 1) {
						Ok = false;
						break;
					}
				}
				if (Ok) AggLoads.push_back(LI);
			}
		for (LoadInst* LI : AggLoads) {
			IRBuilder<> B(LI);
			Value* Base = LI->getPointerOperand();
			Type* I64 = Type::getInt64Ty(Ctx);
			Align A = LI->getAlign();
			Value* V0 = B.CreateAlignedLoad(I64, Base, A, LI->isVolatile(), "ldi64.0");
			uint64_t Off1 = DL.getStructLayout(cast<StructType>(LI->getType()))
				->getElementOffset(1);
			Value* P1 = Off1
				? B.CreateGEP(I8Ty, Base, B.getInt64(Off1), "ldi64.p1")
				: Base;
			Value* V1 = B.CreateAlignedLoad(I64, P1, A, LI->isVolatile(), "ldi64.1");
			SmallVector<ExtractValueInst*, 4> Extracts;
			for (User* U : LI->users())
				Extracts.push_back(cast<ExtractValueInst>(U));
			for (ExtractValueInst* EV : Extracts) {
				EV->replaceAllUsesWith(EV->getIndices()[0] == 0 ? V0 : V1);
				EV->eraseFromParent();
			}
			LI->eraseFromParent();
		}
	}

	// Widen f32 allocas to f64 so OP_LOAD_F / OP_STORE_F (which always
	// operate on 8 bytes) never read/write past the end of a 4-byte slot.
	// At -O0 each float local is an alloca used only by load/store float;
	// widening is semantics-preserving: fpext on stores, fptrunc on loads.
	{
		SmallVector<AllocaInst*, 16> FloatAllocas;
		for (BasicBlock& BB : F)
			for (Instruction& I : BB)
				if (auto* AI = dyn_cast<AllocaInst>(&I))
					if (AI->getAllocatedType()->isFloatTy())
						FloatAllocas.push_back(AI);

		for (AllocaInst* AI : FloatAllocas) {
			IRBuilder<> AB(AI);
			auto* NewAI = AB.CreateAlloca(DoubleTy, nullptr, AI->getName() + ".f2d");
			NewAI->setAlignment(Align(8));

			SmallVector<Instruction*, 16> ToErase;
			SmallVector<std::pair<Use*, Value*>, 16> ToReplace;

			for (Use& U : AI->uses()) {
				auto* User = cast<Instruction>(U.getUser());
				if (auto* SI = dyn_cast<StoreInst>(User)) {
					IRBuilder<> B(SI);
					B.CreateStore(B.CreateFPExt(SI->getValueOperand(), DoubleTy, "f2d.ext"), NewAI);
					ToErase.push_back(SI);
				}
				else if (auto* LI = dyn_cast<LoadInst>(User)) {
					IRBuilder<> B(LI);
					Value* Dbl = B.CreateLoad(DoubleTy, NewAI, "f2d.ld");
					Value* Trn = B.CreateFPTrunc(Dbl, Type::getFloatTy(Ctx), "f2d.trn");
					LI->replaceAllUsesWith(Trn);
					ToErase.push_back(LI);
				}
				else {
					ToReplace.push_back({ &U, NewAI });
				}
			}
			for (Instruction* I : ToErase)  I->eraseFromParent();
			for (auto& [U, V] : ToReplace)  U->set(V);
			AI->eraseFromParent();
		}
	}



	// Compile function body to bytecode
	E.setOpcodeMap(&OpMap);
	E.setTargetBlind(SaltConst, BlindTargets);
	E.setConstInStream(ConstInStream);
	E.setKeyedDispatch(SaltConst, KeyedDispatch);
	E.setSuperOps(SuperOps);
	E.setISAEnc(&IsaEnc);
	if (!E.run(F, CTSalt, M.getDataLayout())) {
		FailReason = E.getFailReason().str();
		if (FailReason.empty()) FailReason = "bytecode emission failed";
		return false;
	}

	if (ObfVerify) {
		std::string VErr;
		uint32_t BadIP = 0;
		if (!verifyBytecode(E, CTSalt, OpMap, VErr, BadIP, SaltConst, BlindTargets, KeyedDispatch)) {
			FailReason = ("bytecode verify failed at ip " + std::to_string(BadIP) + ": " + VErr);
			return false;
		}
	}

	// Compute power-of-2 padded register file sizes 
	NVRAlloc = nextPow2(E.NVR);
	NVR64Alloc = nextPow2(E.NVR64);
	NPRAlloc = nextPow2(E.NPR);
	NFRAlloc = nextPow2(E.NFR);


	// generate per-slot XOR keys for register encryption ————
	// Keys are compile-time constants derived from a forked RNG with a
	// distinct label ("vm.regkeys") so they do not perturb any existing
	// RNG sequence.  One key per allocated slot (power-of-2 padded).
	if (RegEncrypt) {
		auto KeyRng = R.fork("vm.regkeys");
		RegKeys.resize(NVRAlloc);
		for (auto& K : RegKeys)   K = (uint32_t)KeyRng.u32();
		Reg64Keys.resize(NVR64Alloc);
		for (auto& K : Reg64Keys) K = KeyRng.u64();
		FRegKeys.resize(NFRAlloc);
		for (auto& K : FRegKeys)  K = KeyRng.u64();

		LLVM_DEBUG(dbgs() << "[vm] generated register keys for '"
			<< F.getName() << "' [vreg=" << NVRAlloc
			<< " vreg64=" << NVR64Alloc
			<< " freg=" << NFRAlloc << "]\n");
	}


	// Generate per-function engine-pointer XOR mask 
	// Uses a forked RNG so it does not perturb any existing sequence.
	{
		auto EngRng = R.fork("vm.engine.mask");
		EngineMask = ((uint64_t)EngRng.u32() << 32) | EngRng.u32();
		// Ensure mask is non-zero to avoid storing the raw pointer.
		if (EngineMask == 0) EngineMask = 0xDEADBEEFCAFEBABEULL;
	}

	// generate anti-debug poison key + init TargetInfo 
	{
		auto ADRng = R.fork("vm.antidebug");
		ADPoisonKey = ADRng.u32();
		if (ADPoisonKey == 0) ADPoisonKey = 0xDEAD07u;
	}
	TI = obf::TargetInfo::fromModule(M);

	// generate per-function callee XOR mask 
	{
		auto CMRng = R.fork("vm.callee.mask");
		CalleeMask = ((uint64_t)CMRng.u32() << 32) | CMRng.u32();
		if (CalleeMask == 0) CalleeMask = 0xCAFEBABE08080808ULL;
	}


	// Record return slot before stripping body
	computeReturnInfo();


	// Erase original body
	stripBody();

	// Emit globals
	buildBytecodeGlobal();
	buildCalleeGlobal();

	// Nested-VM: each eligible opcode's helper Function* must exist before
	// buildOpcodeHandlers (inside populateVMEngine, below) can emit a call to
	// it. See the sequencing note above virtualizeNestedHelpersOnce().
	if (NestedVM) {
		for (const auto& H : kNestedHelperOrder)
			if (opcodeNests(H.Op))
				getOrCreateNestedHelper(H.Op);
	}

	// Populate shared vm_engine (first function only)
	populateVMEngine();

	// Nested-VM: inner-virtualize the helper(s), once per module. Must run
	// AFTER populateVMEngine() above -- see sequencing note.
	if (NestedVM)
		virtualizeNestedHelpersOnce();

	// Extend CALL handler switches if this function introduced new FTys
	ensureCallFTyCases();

	// Build per-function handler table (uses shared OpcBB with per-function permutation)
	VMEngine::getSharedState(M, EngineId); // ensure shared state exists before table build
	SharedEngineMode = true;
	buildHandlerTable();
	SharedEngineMode = false;


	// Build thin wrapper that tail-calls vm_engine
	buildWrapper();

	// Split wrapper into phases + insert junk (hardened only)
	hardenWrapper();

	// switch-dispatch flattening of wrapper (hardened only)
	flattenWrapper();

	// MBA substitutions on wrapper arithmetic (hardened only)
	mbaHardenWrapper();

	// Encryption constructor (per-function, targets GVBytecodeRT)
	buildEncryptCtor();

	// .init_array anti-debug key-mask fold (bindAntiDebug only; must be
	// registered at a lower .init_array priority than buildEncryptCtor's
	// AES ctor above so it runs first at startup and corrupts the masked
	// key global before the AES ctor unmasks it)
	buildAntiDebugKeyBindCtor();

	// .init_array bytecode integrity hash (hardened + antiDebug)
	buildIntegrityHashCtor();

	// .init_array callee XOR masking (hardened only)
	buildCalleeXorCtor();

	++VMFunctions;
	return true;
}
