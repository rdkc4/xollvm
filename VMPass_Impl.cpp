#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/Twine.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/AttributeMask.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/IR/ValueMap.h"

#include "llvm/Transforms/Obfuscator/VMPass_Impl.h"
#include "llvm/Transforms/Obfuscator/VMPass_ISA.h"
#include "llvm/Transforms/Obfuscator/VMPass_Emitter.h"
#include "llvm/Transforms/Obfuscator/VMPass_Verifier.h"
#include "llvm/Transforms/Obfuscator/ObfuscationOptions.h"

#include <algorithm>
#include <cctype>
#include <functional>
#include <string>
using namespace llvm;

#define DEBUG_TYPE "vm"

STATISTIC(VMFunctions, "Functions virtualised by VMPass");



bool VMImpl::run() {
	// ── Auto-split: native public shell + virtualized core ─────────────
	// va_start must run in the varargs frame (public F). Odd-pair returns of
	// F itself are not a single WrapRetKind slot — demote to sret core.
	auto wipeBody = [&](Function& Fn) {
		SmallVector<BasicBlock*, 32> BBs;
		for (BasicBlock& BB : Fn) BBs.push_back(&BB);
		for (BasicBlock* BB : BBs) BB->dropAllReferences();
		for (BasicBlock* BB : BBs) BB->eraseFromParent();
	};

	// CloneFunctionInto copies Src's dso_local/visibility onto NewFunc and
	// replaces fn/ret/param attrs — InternalLinkage helpers must be fixed up.
	auto finalizeInternalHelper = [&](Function* H) {
		H->setLinkage(GlobalValue::InternalLinkage);
		H->setVisibility(GlobalValue::DefaultVisibility);
		H->setDLLStorageClass(GlobalValue::DefaultStorageClass);
		H->setDSOLocal(true);
		H->addFnAttr(Attribute::NoInline);
		H->addFnAttr(Attribute::NoUnwind);
		stripDebugInfo(*H);
	};

	auto captureShellDebugLoc = [&]() -> DebugLoc {
		if (DISubprogram* SP = F.getSubprogram()) {
			for (BasicBlock& BB : F)
				for (Instruction& I : BB)
					if (I.getDebugLoc())
						return I.getDebugLoc();
			return DILocation::get(Ctx, SP->getScopeLine(), 0, SP);
		}
		return DebugLoc();
	};

	auto virtualizeCore = [&](Function* Core) -> bool {
		unsigned PoolIdx = computePoolIdx(F, Cfg, MasterSeed);
		VMImpl Inner(*Core, Cfg, R, MasterSeed, PoolIdx);
		if (!Inner.run()) {
			FailReason = Inner.FailReason;
			return false;
		}
		// Outer Impl.E never ran — steal Inner stats so VMPass verbose log
		// is not "0B bytecode" for the public shell name.
		E.BC = std::move(Inner.E.BC);
		E.NVR = Inner.E.NVR;
		E.NVR64 = Inner.E.NVR64;
		E.NPR = Inner.E.NPR;
		E.NFR = Inner.E.NFR;
		return true;
	};

	// (1) Varargs + llvm.va_start → shell keeps va_start/end; core gets va_list*.
	{
		SmallVector<CallInst*, 4> VaStarts;
		for (BasicBlock& BB : F)
			for (Instruction& I : BB)
				if (auto* CI = dyn_cast<CallInst>(&I))
					if (Function* CF = CI->getCalledFunction();
						CF && CF->getIntrinsicID() == Intrinsic::vastart)
						VaStarts.push_back(CI);

		if (!VaStarts.empty() && F.isVarArg()) {
			SmallVector<Type*, 8> Params;
			for (Argument& A : F.args())
				Params.push_back(A.getType());
			Params.push_back(PtrTy);
			FunctionType* CoreTy = FunctionType::get(F.getReturnType(), Params, false);
			std::string CoreName = ("__vm_core_va_" + F.getName()).str();
			for (char& C : CoreName)
				if (!std::isalnum((unsigned char)C) && C != '_') C = '_';
			Function* Core = Function::Create(
				CoreTy, GlobalValue::InternalLinkage, CoreName, &M);

			ValueToValueMapTy VMap;
			auto CA = Core->arg_begin();
			for (Argument& A : F.args()) {
				CA->setName(A.getName());
				VMap[&A] = &*CA++;
			}
			Argument* ValistArg = &*CA;
			ValistArg->setName("valist");

			SmallVector<ReturnInst*, 8> Returns;
			CloneFunctionInto(Core, &F, VMap,
				CloneFunctionChangeType::LocalChangesOnly, Returns);
			finalizeInternalHelper(Core);

			// Capture shell material before F's body is wiped (VaStarts dangle after).
			auto vaListAllocaTy = [&](Value* VaStartArg) -> Type* {
				Value* Base = VaStartArg;
				if (auto* GEP = dyn_cast<GEPOperator>(Base))
					Base = GEP->getPointerOperand();
				Base = Base->stripPointerCasts();
				if (auto* AI = dyn_cast<AllocaInst>(Base))
					return AI->getAllocatedType();
				return nullptr;
			};
			Type* VaListTy = vaListAllocaTy(VaStarts[0]->getArgOperand(0));
			if (!VaListTy)
				VaListTy = ArrayType::get(
					StructType::get(Ctx, { I32Ty, I32Ty, PtrTy, PtrTy }), 1);

			Function* VaStartF = VaStarts[0]->getCalledFunction();
			Function* VaEndF = nullptr;
			for (BasicBlock& BB : F) {
				for (Instruction& I : BB) {
					if (auto* CI = dyn_cast<CallInst>(&I))
						if (Function* CF = CI->getCalledFunction();
							CF && CF->getIntrinsicID() == Intrinsic::vaend) {
							VaEndF = CF;
							break;
						}
				}
				if (VaEndF) break;
			}
			if (!VaEndF)
				VaEndF = VaStartF; // last resort; should not happen with clang IR

			// Drop va_start / va_end in core; redirect the va_list alloca to the arg.
			SmallVector<AllocaInst*, 4> DeadAllocas;
			for (BasicBlock& BB : *Core) {
				for (Instruction& I : llvm::make_early_inc_range(BB)) {
					auto* CI = dyn_cast<CallInst>(&I);
					if (!CI) continue;
					Function* CF = CI->getCalledFunction();
					if (!CF) continue;
					Intrinsic::ID IID = CF->getIntrinsicID();
					if (IID == Intrinsic::vastart) {
						Value* Op = CI->getArgOperand(0);
						Value* Base = Op;
						if (auto* GEP = dyn_cast<GEPOperator>(Base))
							Base = GEP->getPointerOperand();
						Base = Base->stripPointerCasts();
						CI->eraseFromParent();
						if (auto* AI = dyn_cast<AllocaInst>(Base)) {
							AI->replaceAllUsesWith(ValistArg);
							DeadAllocas.push_back(AI);
						}
					} else if (IID == Intrinsic::vaend) {
						CI->eraseFromParent();
					}
				}
			}
			for (AllocaInst* AI : DeadAllocas)
				if (AI->use_empty())
					AI->eraseFromParent();

			DebugLoc ShellDL = captureShellDebugLoc();
			LLVM_DEBUG(dbgs() << "[vm] varargs auto-split '" << F.getName()
				<< "' → core '" << Core->getName() << "'\n");
			if (!virtualizeCore(Core)) {
				Core->eraseFromParent();
				return false;
			}

			wipeBody(F);
			BasicBlock* Entry = BasicBlock::Create(Ctx, "entry", &F);
			IRBuilder<> B(Entry);
			if (ShellDL)
				B.SetCurrentDebugLocation(ShellDL);
			AllocaInst* Ap = B.CreateAlloca(VaListTy, nullptr, "ap");
			// Clang passes gep(array_alloca,0,0) to va_start/va_end.
			Value* ApArg = Ap;
			if (VaListTy->isArrayTy())
				ApArg = B.CreateConstInBoundsGEP2_64(VaListTy, Ap, 0, 0, "ap.el");
			B.CreateCall(VaStartF, { ApArg });
			SmallVector<Value*, 8> CallArgs;
			for (Argument& A : F.args())
				CallArgs.push_back(&A);
			// Core expects the same base the original alloca occupied (array ptr).
			CallArgs.push_back(Ap);
			CallInst* CR = F.getReturnType()->isVoidTy()
				? B.CreateCall(Core, CallArgs)
				: B.CreateCall(Core, CallArgs, "core.r");
			B.CreateCall(VaEndF, { ApArg });
			if (F.getReturnType()->isVoidTy())
				B.CreateRetVoid();
			else
				B.CreateRet(CR);
			return true;
		}
	}

	auto isVmScalarTy = [&](Type* T) -> bool {
		if (T->isPointerTy()) return true;
		if (!T->isIntegerTy()) return false;
		unsigned W = T->getIntegerBitWidth();
		return W == 1 || W == 8 || W == 16 || W == 32 || W == 64;
	};
	auto isSupportedPairElem = [&](Type* T) -> bool {
		if (T->isPointerTy()) return true;
		if (!T->isIntegerTy()) return false;
		unsigned W = T->getIntegerBitWidth();
		return W <= 32 || W == 64;
	};
	auto isPtrI64Pair = [&](Type* T) -> bool {
		auto* ST = dyn_cast<StructType>(T);
		return ST && ST->getNumElements() == 2 &&
			ST->getElementType(0)->isPointerTy() &&
			ST->getElementType(1)->isIntegerTy(64);
	};

	// (2) Odd-pair return of F → sret core + insertvalue shell.
	{
		auto* ST = dyn_cast<StructType>(F.getReturnType());
		if (ST && ST->getNumElements() == 2 && !isPtrI64Pair(ST) &&
			isSupportedPairElem(ST->getElementType(0)) &&
			isSupportedPairElem(ST->getElementType(1))) {
			SmallVector<Type*, 8> Params;
			Params.push_back(PtrTy);
			for (Argument& A : F.args())
				Params.push_back(A.getType());
			FunctionType* CoreTy = FunctionType::get(Type::getVoidTy(Ctx), Params, false);
			std::string CoreName = ("__vm_core_sret_" + F.getName()).str();
			for (char& C : CoreName)
				if (!std::isalnum((unsigned char)C) && C != '_') C = '_';
			Function* Core = Function::Create(
				CoreTy, GlobalValue::InternalLinkage, CoreName, &M);

			// Clone into a temp with same signature, then rewrite rets to sret.
			Function* Tmp = Function::Create(
				F.getFunctionType(), GlobalValue::InternalLinkage,
				CoreName + ".tmp", &M);
			ValueToValueMapTy VMap;
			auto TA = Tmp->arg_begin();
			for (Argument& A : F.args()) {
				TA->setName(A.getName());
				VMap[&A] = &*TA++;
			}
			SmallVector<ReturnInst*, 8> Returns;
			CloneFunctionInto(Tmp, &F, VMap,
				CloneFunctionChangeType::LocalChangesOnly, Returns);

			Argument* SretArg = Core->getArg(0);
			SretArg->setName("sret");
			{
				ValueToValueMapTy VMap2;
				auto CA = Core->arg_begin();
				++CA; // skip sret
				for (Argument& A : Tmp->args()) {
					CA->setName(A.getName());
					VMap2[&A] = &*CA++;
				}
				SmallVector<ReturnInst*, 8> Returns2;
				CloneFunctionInto(Core, Tmp, VMap2,
					CloneFunctionChangeType::LocalChangesOnly, Returns2);
			}
			Tmp->eraseFromParent();
			finalizeInternalHelper(Core);
			// CloneFunctionInto replaced param/ret attrs — drop ret attrs
			// cloned from value-returning Tmp onto void Core; restore sret.
			if (AttributeSet RAS = Core->getAttributes().getRetAttrs();
				RAS.hasAttributes()) {
				AttributeMask AM;
				for (Attribute A : RAS)
					AM.addAttribute(A);
				Core->removeRetAttrs(AM);
			}
			Core->addParamAttr(0, Attribute::getWithStructRetType(Ctx, ST));

			// Rewrite returns in Core: field stores to sret, ret void.
			const DataLayout& DL0 = M.getDataLayout();
			const StructLayout* SL0 = DL0.getStructLayout(ST);
			SmallVector<ReturnInst*, 8> CoreRets;
			for (BasicBlock& BB : *Core)
				if (auto* RI = dyn_cast<ReturnInst>(BB.getTerminator()))
					CoreRets.push_back(RI);
			for (ReturnInst* RI : CoreRets) {
				IRBuilder<> RB(RI);
				if (Value* RV = RI->getReturnValue()) {
					for (unsigned Idx = 0; Idx < 2; ++Idx) {
						Value* Field = RB.CreateExtractValue(RV, Idx, "sret.ev");
						Type* FT = ST->getElementType(Idx);
						uint64_t Off = SL0->getElementOffset(Idx);
						Value* Ptr = Off
							? RB.CreateGEP(I8Ty, SretArg, RB.getInt64(Off), "sret.p")
							: SretArg;
						if (FT->isPointerTy() || FT->isIntegerTy(64)) {
							RB.CreateStore(Field, Ptr);
						} else {
							unsigned W = FT->getIntegerBitWidth();
							Type* StTy = (W <= 8) ? I8Ty : (W <= 16) ? I16Ty : I32Ty;
							Value* SV = Field;
							if (SV->getType() != StTy)
								SV = RB.CreateZExtOrTrunc(SV, StTy, "sret.tr");
							RB.CreateStore(SV, Ptr);
						}
					}
				}
				RB.CreateRetVoid();
				RI->eraseFromParent();
			}

			DebugLoc ShellDL = captureShellDebugLoc();
			LLVM_DEBUG(dbgs() << "[vm] odd-pair-ret auto-split '" << F.getName()
				<< "' → core '" << Core->getName() << "'\n");
			if (!virtualizeCore(Core)) {
				Core->eraseFromParent();
				return false;
			}

			wipeBody(F);
			BasicBlock* Entry = BasicBlock::Create(Ctx, "entry", &F);
			IRBuilder<> B(Entry);
			if (ShellDL)
				B.SetCurrentDebugLocation(ShellDL);
			AllocaInst* TmpAgg = B.CreateAlloca(ST, nullptr, "sret.tmp");
			SmallVector<Value*, 8> CallArgs;
			CallArgs.push_back(TmpAgg);
			for (Argument& A : F.args())
				CallArgs.push_back(&A);
			B.CreateCall(Core, CallArgs);
			const DataLayout& DL = M.getDataLayout();
			const StructLayout* SL = DL.getStructLayout(ST);
			auto loadField = [&](unsigned Idx) -> Value* {
				Type* FT = ST->getElementType(Idx);
				uint64_t Off = SL->getElementOffset(Idx);
				Value* Ptr = Off
					? B.CreateGEP(I8Ty, TmpAgg, B.getInt64(Off), "sf.p")
					: TmpAgg;
				if (FT->isPointerTy())
					return B.CreateLoad(PtrTy, Ptr, "sf.ld");
				if (FT->isIntegerTy(64))
					return B.CreateLoad(I64Ty, Ptr, "sf.ld");
				unsigned W = FT->getIntegerBitWidth();
				Type* LoadTy = (W <= 8) ? I8Ty : (W <= 16) ? I16Ty : I32Ty;
				Value* V = B.CreateLoad(LoadTy, Ptr, "sf.ld");
				if (V->getType() != FT)
					V = B.CreateZExtOrTrunc(V, FT, "sf.x");
				return V;
			};
			Value* V0 = loadField(0);
			Value* V1 = loadField(1);
			Value* Agg = UndefValue::get(ST);
			Agg = B.CreateInsertValue(Agg, V0, 0, "sf.i0");
			Agg = B.CreateInsertValue(Agg, V1, 1, "sf.i1");
			B.CreateRet(Agg);
			return true;
		}
	}

	// Demote PHI nodes to memory
	SmallVector<PHINode*, 32> Phis;
	for (BasicBlock& BB : F)
		for (Instruction& I : BB)
			if (auto* PN = dyn_cast<PHINode>(&I)) Phis.push_back(PN);
	for (PHINode* PN : Phis) DemotePHIToStack(PN);






	//     Lower/strip intrinsics that clang emits at -O0 but the VM cannot
	//      encode.  Three tiers:
	//        A) Strip  — debug, lifetime, assume, expect, freeze: zero/identity.
	//        B) Memory — memcpy/memset/memmove const size ≤ 4096: chunked;
	//                    else rewrite to libc @memcpy/@memset/@memmove.
	//        C) Float  — fabs, fmuladd, fma, minnum, maxnum, copysign;
	//                    ceil/floor/… → native thunks.
	//        D) Int    — abs; umul.with.overflow; ctpop/cttz.
	//        E) trap / ceil-family → native thunks (__vm_nat_*).
	//           (va_* not thunked — must stay in the varargs frame.)
	//      Also: aggregate loads, odd pair calls, switch/int legalize (below).
	{
		constexpr uint64_t kMemExpandMax = 4096;
		// Fully unrolling large copies blows the u8 vreg file; keep a small
		// unroll budget and use a fixed-slot looped helper above it.
		constexpr uint64_t kMemUnrollMax = 128;

		auto emitMemChunksUnrolled = [&](IRBuilder<>& B, Value* Dst, Value* Src,
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

		// Looped memcpy/memset helpers — O(1) slots at the call site.
		auto getOrCreateMemCpyLoop = [&]() -> Function* {
			constexpr char Name[] = "__vm_memcpy_loop";
			if (Function* E = M.getFunction(Name)) return E;
			FunctionType* FT = FunctionType::get(Type::getVoidTy(Ctx),
				{ PtrTy, PtrTy, I64Ty }, false);
			Function* NF = Function::Create(FT, GlobalValue::InternalLinkage, Name, &M);
			NF->addFnAttr(Attribute::NoInline);
			NF->addFnAttr(Attribute::NoUnwind);
			Argument* Dst = NF->getArg(0);
			Argument* Src = NF->getArg(1);
			Argument* N = NF->getArg(2);
			BasicBlock* Entry = BasicBlock::Create(Ctx, "entry", NF);
			BasicBlock* Loop = BasicBlock::Create(Ctx, "loop", NF);
			BasicBlock* Rest = BasicBlock::Create(Ctx, "rest", NF);
			BasicBlock* Done = BasicBlock::Create(Ctx, "done", NF);
			IRBuilder<> EB(Entry);
			Value* N64 = EB.CreateAnd(N, ConstantInt::get(I64Ty, ~7ull), "n64");
			EB.CreateCondBr(EB.CreateICmpNE(N64, ConstantInt::get(I64Ty, 0)), Loop, Rest);
			IRBuilder<> LB(Loop);
			PHINode* I = LB.CreatePHI(I64Ty, 2, "i");
			I->addIncoming(ConstantInt::get(I64Ty, 0), Entry);
			Value* DP = LB.CreateGEP(I8Ty, Dst, I, "dp");
			Value* SP = LB.CreateGEP(I8Ty, Src, I, "sp");
			LB.CreateStore(LB.CreateLoad(I64Ty, SP, "ld"), DP);
			Value* I2 = LB.CreateAdd(I, ConstantInt::get(I64Ty, 8), "i2");
			I->addIncoming(I2, Loop);
			LB.CreateCondBr(LB.CreateICmpULT(I2, N64), Loop, Rest);
			IRBuilder<> RB(Rest);
			PHINode* ROff = RB.CreatePHI(I64Ty, 2, "roff");
			ROff->addIncoming(N64, Entry);
			ROff->addIncoming(N64, Loop);
			BasicBlock* BLoop = BasicBlock::Create(Ctx, "byte", NF);
			RB.CreateCondBr(RB.CreateICmpULT(ROff, N), BLoop, Done);
			IRBuilder<> BB(BLoop);
			PHINode* BI = BB.CreatePHI(I64Ty, 2, "bi");
			BI->addIncoming(ROff, Rest);
			Value* BDP = BB.CreateGEP(I8Ty, Dst, BI, "bdp");
			Value* BSP = BB.CreateGEP(I8Ty, Src, BI, "bsp");
			BB.CreateStore(BB.CreateLoad(I8Ty, BSP, "bld"), BDP);
			Value* BI2 = BB.CreateAdd(BI, ConstantInt::get(I64Ty, 1), "bi2");
			BI->addIncoming(BI2, BLoop);
			BB.CreateCondBr(BB.CreateICmpULT(BI2, N), BLoop, Done);
			IRBuilder<> DB(Done);
			DB.CreateRetVoid();
			return NF;
		};
		auto getOrCreateMemSetLoop = [&]() -> Function* {
			constexpr char Name[] = "__vm_memset_loop";
			if (Function* E = M.getFunction(Name)) return E;
			FunctionType* FT = FunctionType::get(Type::getVoidTy(Ctx),
				{ PtrTy, I8Ty, I64Ty }, false);
			Function* NF = Function::Create(FT, GlobalValue::InternalLinkage, Name, &M);
			NF->addFnAttr(Attribute::NoInline);
			NF->addFnAttr(Attribute::NoUnwind);
			Argument* Dst = NF->getArg(0);
			Argument* Val = NF->getArg(1);
			Argument* N = NF->getArg(2);
			BasicBlock* Entry = BasicBlock::Create(Ctx, "entry", NF);
			BasicBlock* Loop = BasicBlock::Create(Ctx, "loop", NF);
			BasicBlock* Rest = BasicBlock::Create(Ctx, "rest", NF);
			BasicBlock* Done = BasicBlock::Create(Ctx, "done", NF);
			IRBuilder<> EB(Entry);
			Value* Val64 = EB.CreateZExt(Val, I64Ty, "v64");
			// splat byte into i64 pattern
			Value* Pat = Val64;
			Pat = EB.CreateOr(Pat, EB.CreateShl(Pat, ConstantInt::get(I64Ty, 8)));
			Pat = EB.CreateOr(Pat, EB.CreateShl(Pat, ConstantInt::get(I64Ty, 16)));
			Pat = EB.CreateOr(Pat, EB.CreateShl(Pat, ConstantInt::get(I64Ty, 32)));
			Value* N64 = EB.CreateAnd(N, ConstantInt::get(I64Ty, ~7ull), "n64");
			EB.CreateCondBr(EB.CreateICmpNE(N64, ConstantInt::get(I64Ty, 0)), Loop, Rest);
			IRBuilder<> LB(Loop);
			PHINode* I = LB.CreatePHI(I64Ty, 2, "i");
			I->addIncoming(ConstantInt::get(I64Ty, 0), Entry);
			Value* DP = LB.CreateGEP(I8Ty, Dst, I, "dp");
			LB.CreateStore(Pat, DP);
			Value* I2 = LB.CreateAdd(I, ConstantInt::get(I64Ty, 8), "i2");
			I->addIncoming(I2, Loop);
			LB.CreateCondBr(LB.CreateICmpULT(I2, N64), Loop, Rest);
			IRBuilder<> RB(Rest);
			PHINode* ROff = RB.CreatePHI(I64Ty, 2, "roff");
			ROff->addIncoming(N64, Entry);
			ROff->addIncoming(N64, Loop);
			BasicBlock* BLoop = BasicBlock::Create(Ctx, "byte", NF);
			RB.CreateCondBr(RB.CreateICmpULT(ROff, N), BLoop, Done);
			IRBuilder<> BB(BLoop);
			PHINode* BI = BB.CreatePHI(I64Ty, 2, "bi");
			BI->addIncoming(ROff, Rest);
			Value* BDP = BB.CreateGEP(I8Ty, Dst, BI, "bdp");
			BB.CreateStore(Val, BDP);
			Value* BI2 = BB.CreateAdd(BI, ConstantInt::get(I64Ty, 1), "bi2");
			BI->addIncoming(BI2, BLoop);
			BB.CreateCondBr(BB.CreateICmpULT(BI2, N), BLoop, Done);
			IRBuilder<> DB(Done);
			DB.CreateRetVoid();
			return NF;
		};

		auto emitMemChunks = [&](IRBuilder<>& B, Value* Dst, Value* Src,
			uint64_t Sz, uint8_t FillByte, bool IsSet) {
			if (Sz <= kMemUnrollMax) {
				emitMemChunksUnrolled(B, Dst, Src, Sz, FillByte, IsSet);
				return;
			}
			if (IsSet) {
				B.CreateCall(getOrCreateMemSetLoop(),
					{ Dst, ConstantInt::get(I8Ty, FillByte),
					  ConstantInt::get(I64Ty, Sz) });
			} else {
				B.CreateCall(getOrCreateMemCpyLoop(),
					{ Dst, Src, ConstantInt::get(I64Ty, Sz) });
			}
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

		// Native thunk: keep the intrinsic inside an internal helper so the
		// VM emits a normal CALL and the LLVM backend lowers the intrinsic.
		auto getOrCreateNatThunk = [&](Function* IntrF) -> Function* {
			std::string Name = ("__vm_nat." + IntrF->getName()).str();
			for (char& C : Name)
				if (C == '.' || C == '@') C = '_';
			if (Function* E = M.getFunction(Name))
				return E;
			FunctionType* FT = IntrF->getFunctionType();
			Function* NF = Function::Create(FT, GlobalValue::InternalLinkage, Name, &M);
			NF->addFnAttr(Attribute::NoInline);
			NF->addFnAttr(Attribute::NoUnwind);
			BasicBlock* BB = BasicBlock::Create(Ctx, "entry", NF);
			IRBuilder<> TB(BB);
			SmallVector<Value*, 4> Args;
			for (Argument& A : NF->args())
				Args.push_back(&A);
			CallInst* IC = TB.CreateCall(FT, IntrF, Args);
			if (FT->getReturnType()->isVoidTy())
				TB.CreateRetVoid();
			else
				TB.CreateRet(IC);
			return NF;
		};

		auto rewriteToNatThunk = [&](CallInst* CI) {
			Function* Thunk = getOrCreateNatThunk(CI->getCalledFunction());
			IRBuilder<> B(CI);
			SmallVector<Value*, 4> Args(CI->args().begin(), CI->args().end());
			CallInst* NC = B.CreateCall(Thunk, Args, CI->getName());
			NC->setTailCall(CI->isTailCall());
			CI->replaceAllUsesWith(NC);
			CI->eraseFromParent();
		};

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

			//  Tier B: memcpy / memmove (≤4096 chunked, else libc)
			if (IID == Intrinsic::memcpy || IID == Intrinsic::memmove) {
				if (auto* SzC = dyn_cast<ConstantInt>(CI->getArgOperand(2))) {
					uint64_t Sz = SzC->getZExtValue();
					if (Sz > 0 && Sz <= kMemExpandMax) {
						Value* Dst = CI->getArgOperand(0);
						Value* Src = CI->getArgOperand(1);
						if (IID == Intrinsic::memmove) {
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
				const char* Name = (IID == Intrinsic::memmove) ? "memmove" : "memcpy";
				FunctionType* LTy = FunctionType::get(PtrTy, { PtrTy, PtrTy, I64Ty }, false);
				FunctionCallee LC = M.getOrInsertFunction(Name, LTy);
				Value* Sz = CI->getArgOperand(2);
				if (!Sz->getType()->isIntegerTy(64))
					Sz = B.CreateZExtOrTrunc(Sz, I64Ty, "mc.sz64");
				B.CreateCall(LC, { CI->getArgOperand(0), CI->getArgOperand(1), Sz });
				CI->eraseFromParent();
				continue;
			}

			//  Tier B: memset (≤4096 chunked, else libc)
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
				FunctionType* LTy = FunctionType::get(PtrTy,
					{ PtrTy, I32Ty, I64Ty }, false);
				FunctionCallee LC = M.getOrInsertFunction("memset", LTy);
				Value* Val = CI->getArgOperand(1);
				Value* Val32 = B.CreateZExt(Val, I32Ty, "ms.v32");
				Value* Sz = CI->getArgOperand(2);
				if (!Sz->getType()->isIntegerTy(64))
					Sz = B.CreateZExtOrTrunc(Sz, I64Ty, "ms.sz64");
				B.CreateCall(LC, { CI->getArgOperand(0), Val32, Sz });
				CI->eraseFromParent();
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

			//  Tier D: ctpop / cttz → SWAR (OP_BINOP-friendly).
			auto expandCtpop = [&](IRBuilder<>& IB, Value* X) -> Value* {
				Type* IT = X->getType();
				unsigned BW = IT->getIntegerBitWidth();
				auto C = [&](uint64_t V) { return ConstantInt::get(IT, V); };
				auto shr = [&](Value* V, unsigned S, const Twine& N) {
					return IB.CreateLShr(V, C(S), N);
				};
				Value* T = IB.CreateSub(X,
					IB.CreateAnd(shr(X, 1, "ct.pop.s1"),
						C(BW == 32 ? 0x55555555ull : 0x5555555555555555ull),
						"ct.pop.a1"),
					"ct.pop.t1");
				T = IB.CreateAdd(
					IB.CreateAnd(T, C(BW == 32 ? 0x33333333ull : 0x3333333333333333ull),
						"ct.pop.a2"),
					IB.CreateAnd(shr(T, 2, "ct.pop.s2"),
						C(BW == 32 ? 0x33333333ull : 0x3333333333333333ull),
						"ct.pop.a3"),
					"ct.pop.t2");
				T = IB.CreateAnd(
					IB.CreateAdd(T, shr(T, 4, "ct.pop.s4"), "ct.pop.t3"),
					C(BW == 32 ? 0x0F0F0F0Full : 0x0F0F0F0F0F0F0F0Full),
					"ct.pop.t4");
				T = IB.CreateAdd(T, shr(T, 8, "ct.pop.s8"), "ct.pop.t5");
				T = IB.CreateAdd(T, shr(T, 16, "ct.pop.s16"), "ct.pop.t6");
				if (BW == 64)
					T = IB.CreateAdd(T, shr(T, 32, "ct.pop.s32"), "ct.pop.t7");
				return IB.CreateAnd(T, C(BW == 32 ? 0x3Full : 0x7Full), "ct.pop.r");
			};

			if (IID == Intrinsic::ctpop) {
				Value* X = CI->getArgOperand(0);
				Type* IT = X->getType();
				unsigned BW = IT->isIntegerTy() ? IT->getIntegerBitWidth() : 0;
				if (BW == 32 || BW == 64) {
					CI->replaceAllUsesWith(expandCtpop(B, X));
					CI->eraseFromParent();
					continue;
				}
			}

			// cttz(x) = (x == 0) ? BW : ctpop((x & -x) - 1).
			// is_zero_poison: returning BW on zero refines poison and matches
			// the defined-on-zero intrinsic.
			if (IID == Intrinsic::cttz) {
				Value* X = CI->getArgOperand(0);
				Type* IT = X->getType();
				unsigned BW = IT->isIntegerTy() ? IT->getIntegerBitWidth() : 0;
				if (BW == 32 || BW == 64) {
					Value* Zero = ConstantInt::get(IT, 0);
					Value* Lowest = B.CreateAnd(X, B.CreateSub(Zero, X, "ct.tz.neg"),
						"ct.tz.low");
					Value* Count = expandCtpop(B,
						B.CreateSub(Lowest, ConstantInt::get(IT, 1), "ct.tz.m1"));
					Value* R = B.CreateSelect(
						B.CreateICmpEQ(X, Zero, "ct.tz.z"),
						ConstantInt::get(IT, BW), Count, "ct.tz.r");
					CI->replaceAllUsesWith(R);
					CI->eraseFromParent();
					continue;
				}
			}

			//  Tier E: trap / ceil family → native thunks.
			//  va_* handled by auto-split at run() entry (native shell).
			if (IID == Intrinsic::trap ||
				IID == Intrinsic::ceil || IID == Intrinsic::floor ||
				IID == Intrinsic::trunc || IID == Intrinsic::nearbyint ||
				IID == Intrinsic::rint || IID == Intrinsic::round) {
				rewriteToNatThunk(CI);
				continue;
			}

			// Anything else: leave in place, isize() will markUnsupported.
		}
	}

	const DataLayout& DL = M.getDataLayout();

	// Non-i32 switches: zext/trunc cond into i32 when cases fit; else icmp/br.
	{
		SmallVector<SwitchInst*, 16> Switches;
		for (BasicBlock& BB : F)
			for (Instruction& I : BB)
				if (auto* SI = dyn_cast<SwitchInst>(&I))
					if (!SI->getCondition()->getType()->isIntegerTy(32))
						Switches.push_back(SI);

		for (SwitchInst* SI : Switches) {
			Value* Cond = SI->getCondition();
			Type* CT = Cond->getType();
			if (!CT->isIntegerTy()) continue;
			unsigned BW = CT->getIntegerBitWidth();
			bool CasesFitI32 = true;
			for (auto& C : SI->cases()) {
				if (C.getCaseValue()->getValue().getSignificantBits() > 32) {
					CasesFitI32 = false;
					break;
				}
			}
			IRBuilder<> B(SI);
			if (BW < 32 || (BW > 32 && CasesFitI32)) {
				Value* C32 = (BW < 32)
					? B.CreateZExt(Cond, I32Ty, "sw.z")
					: B.CreateTrunc(Cond, I32Ty, "sw.t");
				auto* NSw = SwitchInst::Create(C32, SI->getDefaultDest(),
					SI->getNumCases(), SI->getIterator());
				for (auto& C : SI->cases())
					NSw->addCase(
						ConstantInt::get(cast<IntegerType>(I32Ty),
							C.getCaseValue()->getZExtValue()),
						C.getCaseSuccessor());
				SI->eraseFromParent();
				continue;
			}
			// icmp/br chain for wide case values
			auto retargetPhis = [](BasicBlock* Succ, BasicBlock* From, BasicBlock* To) {
				for (PHINode& Phi : Succ->phis()) {
					for (unsigned i = 0, e = Phi.getNumIncomingValues(); i < e; ++i)
						if (Phi.getIncomingBlock(i) == From)
							Phi.setIncomingBlock(i, To);
				}
			};
			BasicBlock* OrigBB = SI->getParent();
			BasicBlock* DefBB = SI->getDefaultDest();
			SmallVector<std::pair<ConstantInt*, BasicBlock*>, 8> Cases;
			for (auto& C : SI->cases())
				Cases.push_back({ C.getCaseValue(), C.getCaseSuccessor() });
			SI->eraseFromParent();
			BasicBlock* Fall = DefBB;
			for (auto It = Cases.rbegin(); It != Cases.rend(); ++It) {
				BasicBlock* CmpBB = BasicBlock::Create(Ctx, "sw.cmp", &F, Fall);
				IRBuilder<> CB(CmpBB);
				Value* Eq = CB.CreateICmpEQ(Cond, It->first, "sw.eq");
				CB.CreateCondBr(Eq, It->second, Fall);
				retargetPhis(It->second, OrigBB, CmpBB);
				retargetPhis(Fall, OrigBB, CmpBB);
				Fall = CmpBB;
			}
			IRBuilder<> OB(OrigBB);
			OB.CreateBr(Fall);
		}
	}

	// Odd-width ints (not 1/8/16/32/64).
	//   Reads:  load → [lshr] → [and] → trunc/zext  → __vm_il_extract
	//   RMW:    store or(and(load,clear), insert)     → __vm_il_deposit
	//   ≤64 leftover trunc/load/and/or/shl/store      → masked i64 SSA
	{
		{
			SmallVector<FreezeInst*, 8> FZ;
			for (BasicBlock& BB : F)
				for (Instruction& I : BB)
					if (auto* FI = dyn_cast<FreezeInst>(&I))
						FZ.push_back(FI);
			for (FreezeInst* FI : FZ) {
				FI->replaceAllUsesWith(FI->getOperand(0));
				FI->eraseFromParent();
			}
		}
		auto illegalInt = [&](Type* T) -> unsigned {
			if (!T || !T->isIntegerTy()) return 0;
			unsigned W = T->getIntegerBitWidth();
			if (W == 1 || W == 8 || W == 16 || W == 32 || W == 64) return 0;
			return W;
		};
		auto i64Mask = [&](unsigned W) -> Constant* {
			assert(W > 0 && W <= 64);
			uint64_t M = (W == 64) ? ~0ull : ((1ull << W) - 1ull);
			return ConstantInt::get(I64Ty, M);
		};
		FunctionType* MemCpyTy = FunctionType::get(PtrTy, { PtrTy, PtrTy, I64Ty }, false);
		FunctionCallee MemCpy = M.getOrInsertFunction("memcpy", MemCpyTy);

		auto getOrCreateBfExtract = [&]() -> Function* {
			constexpr char Name[] = "__vm_il_extract";
			if (Function* E = M.getFunction(Name)) return E;
			FunctionType* FT = FunctionType::get(I64Ty, { PtrTy, I64Ty, I64Ty }, false);
			Function* NF = Function::Create(FT, GlobalValue::InternalLinkage, Name, &M);
			NF->addFnAttr(Attribute::NoInline);
			NF->addFnAttr(Attribute::NoUnwind);
			Argument* Base = NF->getArg(0);
			Argument* BitOff = NF->getArg(1);
			Argument* BitWidth = NF->getArg(2);
			BasicBlock* BB = BasicBlock::Create(Ctx, "entry", NF);
			IRBuilder<> HB(BB);
			AllocaInst* Tmp = HB.CreateAlloca(I64Ty, nullptr, "t");
			HB.CreateStore(ConstantInt::get(I64Ty, 0), Tmp);
			Value* ByteOff = HB.CreateUDiv(BitOff, ConstantInt::get(I64Ty, 8));
			Value* Skip = HB.CreateURem(BitOff, ConstantInt::get(I64Ty, 8));
			Value* Src = HB.CreateGEP(I8Ty, Base, ByteOff, "src");
			HB.CreateCall(MemCpy, { Tmp, Src, ConstantInt::get(I64Ty, 8) });
			Value* V = HB.CreateLoad(I64Ty, Tmp, "ld");
			V = HB.CreateLShr(V, Skip, "sh");
			Value* ShAmt = HB.CreateZExtOrTrunc(BitWidth, I64Ty);
			Value* Mask = HB.CreateSub(
				HB.CreateShl(ConstantInt::get(I64Ty, 1), ShAmt),
				ConstantInt::get(I64Ty, 1), "msk");
			Value* Is64 = HB.CreateICmpEQ(BitWidth, ConstantInt::get(I64Ty, 64));
			Mask = HB.CreateSelect(Is64, ConstantInt::get(I64Ty, ~0ull), Mask);
			HB.CreateRet(HB.CreateAnd(V, Mask, "m"));
			return NF;
		};
		auto getOrCreateBfDeposit = [&]() -> Function* {
			constexpr char Name[] = "__vm_il_deposit";
			if (Function* E = M.getFunction(Name)) return E;
			// void deposit(ptr base, i64 bitoff, i64 width, i64 val)
			FunctionType* FT = FunctionType::get(Type::getVoidTy(Ctx),
				{ PtrTy, I64Ty, I64Ty, I64Ty }, false);
			Function* NF = Function::Create(FT, GlobalValue::InternalLinkage, Name, &M);
			NF->addFnAttr(Attribute::NoInline);
			NF->addFnAttr(Attribute::NoUnwind);
			Argument* Base = NF->getArg(0);
			Argument* BitOff = NF->getArg(1);
			Argument* BitWidth = NF->getArg(2);
			Argument* Val = NF->getArg(3);
			BasicBlock* BB = BasicBlock::Create(Ctx, "entry", NF);
			IRBuilder<> HB(BB);
			AllocaInst* Tmp = HB.CreateAlloca(I64Ty, nullptr, "t");
			HB.CreateStore(ConstantInt::get(I64Ty, 0), Tmp);
			Value* ByteOff = HB.CreateUDiv(BitOff, ConstantInt::get(I64Ty, 8));
			Value* Skip = HB.CreateURem(BitOff, ConstantInt::get(I64Ty, 8));
			Value* Dst = HB.CreateGEP(I8Ty, Base, ByteOff, "dst");
			HB.CreateCall(MemCpy, { Tmp, Dst, ConstantInt::get(I64Ty, 8) });
			Value* Cur = HB.CreateLoad(I64Ty, Tmp, "ld");
			Value* ShAmt = HB.CreateZExtOrTrunc(BitWidth, I64Ty);
			Value* Ones = HB.CreateSub(
				HB.CreateShl(ConstantInt::get(I64Ty, 1), ShAmt),
				ConstantInt::get(I64Ty, 1));
			Value* Is64 = HB.CreateICmpEQ(BitWidth, ConstantInt::get(I64Ty, 64));
			Ones = HB.CreateSelect(Is64, ConstantInt::get(I64Ty, ~0ull), Ones);
			Value* Field = HB.CreateShl(Ones, Skip, "fld");
			Value* Cleared = HB.CreateAnd(Cur, HB.CreateNot(Field), "clr");
			Value* Ins = HB.CreateAnd(Val, Ones, "ins");
			Ins = HB.CreateShl(Ins, Skip, "inssh");
			HB.CreateStore(HB.CreateOr(Cleared, Ins, "m"), Tmp);
			HB.CreateCall(MemCpy, { Dst, Tmp, ConstantInt::get(I64Ty, 8) });
			HB.CreateRetVoid();
			return NF;
		};
		Function* BfExtractFn = getOrCreateBfExtract();
		Function* BfDepositFn = getOrCreateBfDeposit();
		auto extractBits = [&](IRBuilder<>& B, Value* Base, unsigned BitOff,
			unsigned BitWidth) -> Value* {
			return B.CreateCall(BfExtractFn,
				{ Base, ConstantInt::get(I64Ty, BitOff),
				  ConstantInt::get(I64Ty, BitWidth) }, "il.x");
		};
		auto depositBits = [&](IRBuilder<>& B, Value* Base, unsigned BitOff,
			unsigned BitWidth, Value* Val) {
			if (!Val->getType()->isIntegerTy(64))
				Val = B.CreateZExtOrTrunc(Val, I64Ty, "il.dv");
			B.CreateCall(BfDepositFn,
				{ Base, ConstantInt::get(I64Ty, BitOff),
				  ConstantInt::get(I64Ty, BitWidth), Val });
		};

		AllocaInst* LdScratch = nullptr;
		AllocaInst* StScratch = nullptr;
		auto entryAllocaI64 = [&](AllocaInst*& Slot, const char* Name) -> AllocaInst* {
			if (!Slot) {
				IRBuilder<> EB(&F.getEntryBlock(),
					F.getEntryBlock().getFirstInsertionPt());
				Slot = EB.CreateAlloca(I64Ty, nullptr, Name);
			}
			return Slot;
		};

		// Contiguous zero-bits in Clear → field (Off, Width). Fail if non-contig.
		auto fieldFromClear = [&](const APInt& Clear, unsigned SrcW,
			unsigned& Off, unsigned& Width) -> bool {
			APInt Field = (~Clear).zextOrTrunc(SrcW);
			if (Field.isZero()) return false;
			Off = Field.countr_zero();
			// lshr — ashr sign-fills when MSB is in the field and inflates Ones.
			unsigned Ones = Field.lshr(Off).countr_one();
			if (Ones == 0 || Off + Ones > SrcW) return false;
			APInt Expect = APInt::getLowBitsSet(SrcW, Ones).shl(Off);
			if (Field != Expect) return false;
			Width = Ones;
			return Width <= 64;
		};

		// Peel insert tree → (ValI64, BitOff, Width); Val already shifted to field.
		// IP = insertion point (Store); Ins may be a ConstantInt.
		auto peelInsert = [&](Value* Ins, Instruction* IP, unsigned SrcW,
			unsigned& BitOff, unsigned& Width, Value*& ValI64) -> bool {
			BitOff = 0;
			Width = 0;
			ValI64 = nullptr;
			Value* V = Ins;
			unsigned Sh = 0;
			if (auto* BO = dyn_cast<BinaryOperator>(V)) {
				if (BO->getOpcode() == Instruction::Shl) {
					auto* CI = dyn_cast<ConstantInt>(BO->getOperand(1));
					if (!CI) return false;
					Sh = (unsigned)CI->getZExtValue();
					V = BO->getOperand(0);
				}
			}
			unsigned MaskW = SrcW;
			if (auto* BO = dyn_cast<BinaryOperator>(V)) {
				if (BO->getOpcode() == Instruction::And) {
					Value* Other = BO->getOperand(0);
					Value* MaskV = BO->getOperand(1);
					if (!isa<ConstantInt>(MaskV))
						std::swap(Other, MaskV);
					auto* MCI = dyn_cast<ConstantInt>(MaskV);
					if (!MCI) return false;
					MaskW = MCI->getValue().getActiveBits();
					if (MaskW == 0) MaskW = 1;
					V = Other;
				}
			}
			IRBuilder<> B(IP);
			if (auto* TI = dyn_cast<TruncInst>(V)) {
				Value* Src = TI->getOperand(0);
				if (!Src->getType()->isIntegerTy()) return false;
				if (Src->getType()->getIntegerBitWidth() > 64) return false;
				ValI64 = Src;
				if (!ValI64->getType()->isIntegerTy(64))
					ValI64 = B.CreateZExtOrTrunc(ValI64, I64Ty, "il.ins");
				if (MaskW < 64)
					ValI64 = B.CreateAnd(ValI64, i64Mask(MaskW), "il.insm");
			} else if (auto* ZI = dyn_cast<ZExtInst>(V)) {
				// zext i64 %v to iN  (bitfield insert into >64)
				Value* Src = ZI->getOperand(0);
				if (!Src->getType()->isIntegerTy()) return false;
				if (Src->getType()->getIntegerBitWidth() > 64) return false;
				ValI64 = Src;
				if (!ValI64->getType()->isIntegerTy(64))
					ValI64 = B.CreateZExtOrTrunc(ValI64, I64Ty, "il.ins");
				if (MaskW < 64)
					ValI64 = B.CreateAnd(ValI64, i64Mask(MaskW), "il.insm");
			} else if (auto* CI = dyn_cast<ConstantInt>(V)) {
				// Bare const (no and-mask): Width 0 → Pass 1 keeps clear-field width.
				ValI64 = ConstantInt::get(I64Ty, CI->getZExtValue());
				if (MaskW == SrcW)
					MaskW = 0;
			} else if (V->getType()->isIntegerTy(64)) {
				ValI64 = V;
			} else if (illegalInt(V->getType()) &&
				V->getType()->getIntegerBitWidth() <= 64) {
				ValI64 = B.CreateZExtOrTrunc(V, I64Ty, "il.ins");
			} else
				return false;
			BitOff = Sh;
			Width = MaskW;
			if (Width == 0) return true; // inherit clear width
			if (Width > 64 || BitOff + Width > SrcW) return false;
			return true;
		};

		// Pass 1: bitfield RMW  store or(and(load,clear), insert) → deposit
		{
			SmallVector<StoreInst*, 16> Stores;
			for (BasicBlock& BB : F)
				for (Instruction& I : BB)
					if (auto* SI = dyn_cast<StoreInst>(&I))
						if (illegalInt(SI->getValueOperand()->getType()))
							Stores.push_back(SI);
			for (StoreInst* SI : Stores) {
				if (!SI->getParent()) continue;
				unsigned W = illegalInt(SI->getValueOperand()->getType());
				if (!W) continue;
				auto* Or = dyn_cast<BinaryOperator>(SI->getValueOperand());
				if (!Or || Or->getOpcode() != Instruction::Or) continue;
				Value* A = Or->getOperand(0);
				Value* Bv = Or->getOperand(1);
				auto* AndClr = dyn_cast<BinaryOperator>(A);
				Value* Ins = Bv;
				if (!AndClr || AndClr->getOpcode() != Instruction::And) {
					AndClr = dyn_cast<BinaryOperator>(Bv);
					Ins = A;
				}
				if (!AndClr || AndClr->getOpcode() != Instruction::And) continue;
				Value* LdV = AndClr->getOperand(0);
				Value* ClrV = AndClr->getOperand(1);
				if (!isa<LoadInst>(LdV))
					std::swap(LdV, ClrV);
				auto* LI = dyn_cast<LoadInst>(LdV);
				auto* ClrCI = dyn_cast<ConstantInt>(ClrV);
				if (!LI || !ClrCI) continue;
				if (LI->getPointerOperand() != SI->getPointerOperand()) continue;
				unsigned Off = 0, Width = 0;
				if (!fieldFromClear(ClrCI->getValue(), W, Off, Width)) continue;
				unsigned InsOff = 0, InsW = 0;
				Value* ValI64 = nullptr;
				if (!peelInsert(Ins, SI, W, InsOff, InsW, ValI64)) continue;
				if (InsW == 0) {
					// Bare const already positioned; pull field from absolute bits.
					auto* CI = dyn_cast<ConstantInt>(Ins);
					if (!CI) continue;
					APInt Bits = CI->getValue().zextOrTrunc(W).lshr(Off);
					uint64_t M = Width == 64 ? ~uint64_t(0)
						: ((uint64_t(1) << Width) - 1);
					ValI64 = ConstantInt::get(I64Ty, Bits.getZExtValue() & M);
				} else {
					if (InsOff != Off) continue;
					if (InsW > Width) continue;
					Width = InsW;
				}
				IRBuilder<> B(SI);
				depositBits(B, SI->getPointerOperand(), Off, Width, ValI64);
				// Erase the whole RMW tree so dead odd-typed ops cannot
				// reach the emitter (or Pass 3 materialize).
				SmallVector<Instruction*, 8> Kill;
				auto track = [&](Value* V) {
					if (auto* I = dyn_cast<Instruction>(V))
						Kill.push_back(I);
				};
				track(SI);
				track(Or);
				track(AndClr);
				track(LI);
				track(Ins);
				if (auto* BO = dyn_cast<BinaryOperator>(Ins)) {
					track(BO->getOperand(0));
					track(BO->getOperand(1));
					for (Value* Op : { BO->getOperand(0), BO->getOperand(1) }) {
						if (auto* I2 = dyn_cast<BinaryOperator>(Op)) {
							track(I2->getOperand(0));
							track(I2->getOperand(1));
						} else if (auto* C = dyn_cast<CastInst>(Op))
							track(C);
					}
				} else if (auto* C = dyn_cast<CastInst>(Ins))
					track(C);
				SI->eraseFromParent();
				// Drop uses then delete bottom-up by emptying users.
				for (int Pass = 0; Pass < 6; ++Pass) {
					for (Instruction* I : Kill) {
						if (!I->getParent()) continue;
						if (I->use_empty() && !isa<StoreInst>(I))
							I->eraseFromParent();
					}
				}
			}
		}

		// Pass 2: bitfield reads  load → [lshr] → [and] → trunc/zext
		{
			SmallVector<LoadInst*, 16> Loads;
			for (BasicBlock& BB : F)
				for (Instruction& I : BB)
					if (auto* LI = dyn_cast<LoadInst>(&I))
						if (illegalInt(LI->getType()) && LI->getParent())
							Loads.push_back(LI);

			for (LoadInst* LI : Loads) {
				if (!LI->getParent() || LI->user_empty()) continue;
				struct FieldExt {
					Instruction* Anchor; // lshr or and or load-user start
					Instruction* KillLShr;
					Instruction* KillAnd;
					Instruction* KillOut; // trunc or zext
					Type* OutTy;
					unsigned ShAmt;
					unsigned OutBits;
				};
				SmallVector<FieldExt, 8> Fields;
				bool Ok = true;
				for (User* LU : LI->users()) {
					FieldExt FE{};
					FE.KillLShr = nullptr;
					FE.KillAnd = nullptr;
					FE.KillOut = nullptr;
					FE.OutTy = nullptr;
					FE.ShAmt = 0;
					FE.OutBits = 0;
					Value* Cur = LU;
					FE.Anchor = dyn_cast<Instruction>(LU);
					if (!FE.Anchor) { Ok = false; break; }

					if (auto* Sh = dyn_cast<BinaryOperator>(Cur)) {
						if (Sh->getOpcode() == Instruction::LShr ||
							Sh->getOpcode() == Instruction::AShr) {
							auto* ShCI = dyn_cast<ConstantInt>(Sh->getOperand(1));
							if (!ShCI || Sh->getOperand(0) != LI) {
								Ok = false; break;
							}
							FE.ShAmt = (unsigned)ShCI->getZExtValue();
							FE.KillLShr = Sh;
							if (!Sh->hasOneUse()) { Ok = false; break; }
							Cur = *Sh->user_begin();
						}
					}

					if (auto* AI = dyn_cast<BinaryOperator>(Cur)) {
						if (AI->getOpcode() == Instruction::And) {
							Value* MaskV = AI->getOperand(0) == (FE.KillLShr
								? (Value*)FE.KillLShr : (Value*)LI)
								? AI->getOperand(1) : AI->getOperand(0);
							auto* MCI = dyn_cast<ConstantInt>(MaskV);
							Value* Other = MaskV == AI->getOperand(0)
								? AI->getOperand(1) : AI->getOperand(0);
							Value* Expect = FE.KillLShr ? (Value*)FE.KillLShr : (Value*)LI;
							if (!MCI || Other != Expect) { Ok = false; break; }
							FE.OutBits = MCI->getValue().getActiveBits();
							if (FE.OutBits == 0) FE.OutBits = 1;
							if (FE.OutBits > 64) { Ok = false; break; }
							FE.KillAnd = AI;
							if (!AI->hasOneUse()) { Ok = false; break; }
							Cur = *AI->user_begin();
						}
					}

					if (auto* TI = dyn_cast<TruncInst>(Cur)) {
						FE.OutTy = TI->getType();
						if (!FE.OutBits)
							FE.OutBits = FE.OutTy->getIntegerBitWidth();
						FE.KillOut = TI;
					} else if (auto* ZI = dyn_cast<ZExtInst>(Cur)) {
						FE.OutTy = ZI->getType();
						if (!FE.OutBits) {
							// zext of shifted value: width = srcW - shamt
							unsigned SW = illegalInt(LI->getType());
							FE.OutBits = SW > FE.ShAmt ? SW - FE.ShAmt : 1;
							if (FE.OutBits > 64) FE.OutBits = 64;
						}
						FE.KillOut = ZI;
					} else {
						Ok = false; break;
					}
					if (!FE.OutTy || FE.OutBits == 0 || FE.OutBits > 64) {
						Ok = false; break;
					}
					Fields.push_back(FE);
				}
				if (!Ok || Fields.empty()) continue;
				Value* Base = LI->getPointerOperand();
				for (FieldExt& FE : Fields) {
					IRBuilder<> EB(FE.Anchor);
					Value* R = extractBits(EB, Base, FE.ShAmt, FE.OutBits);
					Value* Out = R;
					if (FE.OutTy != I64Ty)
						Out = EB.CreateZExtOrTrunc(R, FE.OutTy, "il.fld");
					FE.KillOut->replaceAllUsesWith(Out);
					FE.KillOut->eraseFromParent();
					if (FE.KillAnd) FE.KillAnd->eraseFromParent();
					if (FE.KillLShr) FE.KillLShr->eraseFromParent();
				}
				if (LI->use_empty())
					LI->eraseFromParent();
			}
		}

		// Pass 3: ≤64 odd SSA → masked i64 (all binops + icmp/select + mem/casts)
		{
			DenseMap<Value*, Value*> I64Of;
			DenseSet<Value*> MatInProg;
			std::function<Value*(Value*)> materialize;
			std::function<bool(Value*, Value*, unsigned)> rewriteUsers;
			std::function<Value*(IRBuilder<>&, Value*)> promotePeer;

			// Emit i64 op equivalent of an illegal-width binary operator.
			auto emitBinop64 = [&](IRBuilder<>& B, unsigned Op, Value* A64,
				Value* B64, unsigned Width, const Twine& Name) -> Value* {
				Value* R = nullptr;
				switch (Op) {
				case Instruction::Add:  R = B.CreateAdd(A64, B64, Name); break;
				case Instruction::Sub:  R = B.CreateSub(A64, B64, Name); break;
				case Instruction::Mul:  R = B.CreateMul(A64, B64, Name); break;
				case Instruction::And:  R = B.CreateAnd(A64, B64, Name); break;
				case Instruction::Or:   R = B.CreateOr(A64, B64, Name); break;
				case Instruction::Xor:  R = B.CreateXor(A64, B64, Name); break;
				case Instruction::Shl:  R = B.CreateShl(A64, B64, Name); break;
				case Instruction::LShr: R = B.CreateLShr(A64, B64, Name); break;
				case Instruction::AShr: {
					// Sign-extend within Width bits before arithmetic shift.
					Value* Sh = ConstantInt::get(I64Ty, 64 - Width);
					Value* S = B.CreateAShr(B.CreateShl(A64, Sh), Sh, Name + ".se");
					R = B.CreateAShr(S, B64, Name);
					break;
				}
				case Instruction::UDiv: R = B.CreateUDiv(A64, B64, Name); break;
				case Instruction::SDiv: {
					Value* Sh = ConstantInt::get(I64Ty, 64 - Width);
					Value* SA = B.CreateAShr(B.CreateShl(A64, Sh), Sh, Name + ".sa");
					Value* SB = B.CreateAShr(B.CreateShl(B64, Sh), Sh, Name + ".sb");
					R = B.CreateSDiv(SA, SB, Name);
					break;
				}
				case Instruction::URem: R = B.CreateURem(A64, B64, Name); break;
				case Instruction::SRem: {
					Value* Sh = ConstantInt::get(I64Ty, 64 - Width);
					Value* SA = B.CreateAShr(B.CreateShl(A64, Sh), Sh, Name + ".sa");
					Value* SB = B.CreateAShr(B.CreateShl(B64, Sh), Sh, Name + ".sb");
					R = B.CreateSRem(SA, SB, Name);
					break;
				}
				default:
					return nullptr;
				}
				return B.CreateAnd(R, i64Mask(Width), Name + ".m");
			};
			auto isPromotableBinop = [](unsigned Op) -> bool {
				switch (Op) {
				case Instruction::Add: case Instruction::Sub: case Instruction::Mul:
				case Instruction::And: case Instruction::Or: case Instruction::Xor:
				case Instruction::Shl: case Instruction::LShr: case Instruction::AShr:
				case Instruction::UDiv: case Instruction::SDiv:
				case Instruction::URem: case Instruction::SRem:
					return true;
				default:
					return false;
				}
			};

			promotePeer = [&](IRBuilder<>& B, Value* Peer) -> Value* {
				if (auto* C = dyn_cast<ConstantInt>(Peer))
					return ConstantInt::get(I64Ty, C->getZExtValue());
				if (Value* Cached = I64Of.lookup(Peer))
					return Cached;
				if (unsigned PW = illegalInt(Peer->getType())) {
					if (PW > 64) return nullptr;
					// Illegal binops: build i64 form from operands
					// (materialize() only roots load/trunc/zext/sext).
					if (auto* BO = dyn_cast<BinaryOperator>(Peer)) {
						unsigned Op = BO->getOpcode();
						if (!isPromotableBinop(Op))
							return nullptr;
						if (MatInProg.contains(BO))
							return nullptr;
						// Promote operands BEFORE marking MatInProg so a nested
						// path can complete this same BO (use-list order often
						// hits mul/xor before add has been cached).
						IRBuilder<> LocalB(BO);
						Value* A64 = promotePeer(LocalB, BO->getOperand(0));
						if (!A64) return nullptr;
						if (Value* Cached = I64Of.lookup(BO))
							return Cached;
						Value* B64 = promotePeer(LocalB, BO->getOperand(1));
						if (!B64) return nullptr;
						if (Value* Cached = I64Of.lookup(BO))
							return Cached;
						MatInProg.insert(BO);
						Value* R = emitBinop64(LocalB, Op, A64, B64, PW, "il.pr");
						if (!R) { MatInProg.erase(BO); return nullptr; }
						I64Of[BO] = R;
						MatInProg.erase(BO);
						// Only cache here. Caller rewriteUsers finishes consumers.
						return R;
					}
					return materialize(Peer);
				}
				if (Peer->getType()->isIntegerTy(64))
					return Peer;
				if (Peer->getType()->isIntegerTy()) {
					// Insert at Peer when it is an instruction so the cast
					// dominates Peer’s consumers; else use caller builder.
					if (auto* PI = dyn_cast<Instruction>(Peer)) {
						IRBuilder<> LocalB(PI);
						return LocalB.CreateZExtOrTrunc(Peer, I64Ty, "il.pr");
					}
					return B.CreateZExtOrTrunc(Peer, I64Ty, "il.pr");
				}
				return nullptr;
			};

			rewriteUsers = [&](Value* Old, Value* NewI64, unsigned OldW) -> bool {
				I64Of[Old] = NewI64;
				SmallVector<User*, 8> Users(Old->user_begin(), Old->user_end());
				for (User* U : Users) {
					if (auto* SI = dyn_cast<StoreInst>(U)) {
						if (SI->getValueOperand() != Old) return false;
						IRBuilder<> SB(SI);
						AllocaInst* Tmp = entryAllocaI64(StScratch, "il.st");
						SB.CreateStore(NewI64, Tmp);
						SB.CreateCall(MemCpy, { SI->getPointerOperand(), Tmp,
							ConstantInt::get(I64Ty, (OldW + 7) / 8) });
						SI->eraseFromParent();
						continue;
					}
					if (auto* TI = dyn_cast<TruncInst>(U)) {
						IRBuilder<> TB(TI);
						unsigned DW = TI->getType()->getIntegerBitWidth();
						if (illegalInt(TI->getType()) && DW <= 64) {
							Value* R = TB.CreateAnd(NewI64, i64Mask(DW), "il.tr");
							if (!rewriteUsers(TI, R, DW)) return false;
							if (TI->use_empty()) TI->eraseFromParent();
							continue;
						}
						if (!(DW == 1 || DW == 8 || DW == 16 || DW == 32 || DW == 64))
							return false;
						Value* R = NewI64;
						if (DW < 64)
							R = TB.CreateAnd(NewI64, i64Mask(DW), "il.tr");
						if (!TI->getType()->isIntegerTy(64))
							R = TB.CreateZExtOrTrunc(R, TI->getType(), "il.trty");
						TI->replaceAllUsesWith(R);
						TI->eraseFromParent();
						continue;
					}
					if (auto* ZI = dyn_cast<ZExtInst>(U)) {
						IRBuilder<> ZB(ZI);
						unsigned DW = ZI->getType()->getIntegerBitWidth();
						if (illegalInt(ZI->getType()) && DW <= 64) {
							Value* R = ZB.CreateAnd(NewI64, i64Mask(OldW), "il.ze");
							if (!rewriteUsers(ZI, R, DW)) return false;
							if (ZI->use_empty()) ZI->eraseFromParent();
							continue;
						}
						Value* Out = NewI64;
						if (!ZI->getType()->isIntegerTy(64))
							Out = ZB.CreateZExtOrTrunc(NewI64, ZI->getType(), "il.zety");
						ZI->replaceAllUsesWith(Out);
						ZI->eraseFromParent();
						continue;
					}
					if (auto* XI = dyn_cast<SExtInst>(U)) {
						IRBuilder<> XB(XI);
						Value* Sh = ConstantInt::get(I64Ty, 64 - OldW);
						Value* Sext64 = XB.CreateAShr(
							XB.CreateShl(NewI64, Sh), Sh, "il.se");
						unsigned DW = XI->getType()->getIntegerBitWidth();
						if (illegalInt(XI->getType()) && DW <= 64) {
							Value* R = XB.CreateAnd(Sext64, i64Mask(DW), "il.sem");
							if (!rewriteUsers(XI, R, DW)) return false;
							if (XI->use_empty()) XI->eraseFromParent();
							continue;
						}
						Value* Out = Sext64;
						if (!XI->getType()->isIntegerTy(64))
							Out = XB.CreateZExtOrTrunc(Sext64, XI->getType(), "il.sety");
						XI->replaceAllUsesWith(Out);
						XI->eraseFromParent();
						continue;
					}
					if (auto* BO = dyn_cast<BinaryOperator>(U)) {
						unsigned Op = BO->getOpcode();
						if (!isPromotableBinop(Op))
							return false;
						if (!BO->getParent())
							continue;
						if (MatInProg.contains(BO))
							continue;
						unsigned ResW = illegalInt(BO->getType());
						if (!ResW) ResW = OldW;
						if (ResW > 64) return false;
						Value* R = I64Of.lookup(BO);
						if (!R) {
							IRBuilder<> BB(BO);
							Value* Op0 = BO->getOperand(0);
							Value* Op1 = BO->getOperand(1);
							Value* A64 = (Op0 == Old) ? NewI64
								: promotePeer(BB, Op0);
							if (!A64) return false;
							if (!BO->getParent() || MatInProg.contains(BO))
								continue;
							if (Value* Cached = I64Of.lookup(BO)) {
								R = Cached;
							} else {
								Value* B64 = (Op1 == Old) ? NewI64
									: promotePeer(BB, Op1);
								if (!B64) return false;
								if (!BO->getParent() || MatInProg.contains(BO))
									continue;
								if (Value* Cached2 = I64Of.lookup(BO)) {
									R = Cached2;
								} else {
									R = emitBinop64(BB, Op, A64, B64, ResW, "il.bo");
									if (!R) return false;
									I64Of[BO] = R;
								}
							}
						}
						if (!illegalInt(BO->getType())) {
							IRBuilder<> BB(BO);
							Value* Out = R;
							if (BO->getType() != I64Ty)
								Out = BB.CreateZExtOrTrunc(R, BO->getType(), "il.boty");
							BO->replaceAllUsesWith(Out);
							BO->eraseFromParent();
							continue;
						}
						// Re-entrancy guard while rewriting this BO's consumers.
						MatInProg.insert(BO);
						bool Ok = rewriteUsers(BO, R, ResW);
						MatInProg.erase(BO);
						if (!Ok) return false;
						if (BO->getParent() && BO->use_empty())
							BO->eraseFromParent();
						continue;
					}
					if (auto* CmpI = dyn_cast<ICmpInst>(U)) {
						// icmp → i1 (legal). Compare masked i64 forms.
						if (!CmpI->getParent()) continue;
						Instruction* InsertBefore = CmpI;
						Value* Peer = CmpI->getOperand(0) == Old
							? CmpI->getOperand(1) : CmpI->getOperand(0);
						IRBuilder<> CB(InsertBefore);
						Value* PeerI64 = promotePeer(CB, Peer);
						if (!PeerI64) return false;
						// Nested promotePeer→rewriteUsers may have already
						// replaced this icmp; do not touch a dead instr.
						if (!CmpI->getParent()) continue;
						Value* A64 = (CmpI->getOperand(0) == Old) ? NewI64 : PeerI64;
						Value* B64 = (CmpI->getOperand(0) == Old) ? PeerI64 : NewI64;
						CmpInst::Predicate Pred = CmpI->getPredicate();
						CB.SetInsertPoint(CmpI);
						if (CmpI->isSigned()) {
							Value* Sh = ConstantInt::get(I64Ty, 64 - OldW);
							A64 = CB.CreateAShr(CB.CreateShl(A64, Sh), Sh, "il.icmp.sa");
							B64 = CB.CreateAShr(CB.CreateShl(B64, Sh), Sh, "il.icmp.sb");
						}
						Value* Cmp = CB.CreateICmp(Pred, A64, B64, "il.icmp");
						CmpI->replaceAllUsesWith(Cmp);
						CmpI->eraseFromParent();
						continue;
					}
					if (auto* SelI = dyn_cast<SelectInst>(U)) {
						// select i1, iN, iN  (N illegal ≤64) → select on i64 + mask
						if (SelI->getCondition() == Old)
							return false; // cond must be i1, not odd-int
						if (!SelI->getParent()) continue;
						unsigned ResW = illegalInt(SelI->getType());
						if (!ResW || ResW > 64) return false;
						if (I64Of.lookup(SelI)) continue;
						IRBuilder<> SB(SelI);
						Value* TrueV = SelI->getTrueValue();
						Value* FalseV = SelI->getFalseValue();
						Value* T64 = (TrueV == Old) ? NewI64 : promotePeer(SB, TrueV);
						Value* F64 = (FalseV == Old) ? NewI64 : promotePeer(SB, FalseV);
						if (!T64 || !F64) return false;
						if (!SelI->getParent() || I64Of.lookup(SelI)) continue;
						SB.SetInsertPoint(SelI);
						Value* R = SB.CreateSelect(SelI->getCondition(), T64, F64, "il.sel");
						R = SB.CreateAnd(R, i64Mask(ResW), "il.sel.m");
						I64Of[SelI] = R;
						if (!rewriteUsers(SelI, R, ResW)) {
							if (SelI->getParent() && SelI->use_empty())
								SelI->eraseFromParent();
							return SelI->getParent() ? false : true;
						}
						if (SelI->getParent() && SelI->use_empty())
							SelI->eraseFromParent();
						continue;
					}
					return false;
				}
				return true;
			};

			materialize = [&](Value* V) -> Value* {
				if (Value* Cached = I64Of.lookup(V)) return Cached;
				unsigned W = illegalInt(V->getType());
				if (!W || W > 64) return nullptr;
				if (!MatInProg.insert(V).second)
					return I64Of.lookup(V);
				IRBuilder<> B(cast<Instruction>(V));
				Value* R = nullptr;
				if (auto* LI = dyn_cast<LoadInst>(V)) {
					AllocaInst* Tmp = entryAllocaI64(LdScratch, "il.ldtmp");
					B.CreateStore(ConstantInt::get(I64Ty, 0), Tmp);
					B.CreateCall(MemCpy, { Tmp, LI->getPointerOperand(),
						ConstantInt::get(I64Ty, (W + 7) / 8) });
					R = B.CreateAnd(B.CreateLoad(I64Ty, Tmp, "il.ld"),
						i64Mask(W), "il.ldm");
				} else if (auto* TI = dyn_cast<TruncInst>(V)) {
					Value* Src = TI->getOperand(0);
					if (!Src->getType()->isIntegerTy(64))
						Src = B.CreateZExtOrTrunc(Src, I64Ty, "il.s64");
					R = B.CreateAnd(Src, i64Mask(W), "il.trunc");
				} else if (auto* ZI = dyn_cast<ZExtInst>(V)) {
					Value* Src = ZI->getOperand(0);
					if (unsigned SW = illegalInt(Src->getType())) {
						if (SW > 64) { MatInProg.erase(V); return nullptr; }
						Src = materialize(Src);
						if (!Src) { MatInProg.erase(V); return nullptr; }
					} else if (!Src->getType()->isIntegerTy(64))
						Src = B.CreateZExtOrTrunc(Src, I64Ty, "il.zs64");
					R = B.CreateAnd(Src, i64Mask(W), "il.zext");
				} else if (auto* XI = dyn_cast<SExtInst>(V)) {
					Value* Src = XI->getOperand(0);
					unsigned SrcW = Src->getType()->getIntegerBitWidth();
					if (unsigned SW = illegalInt(Src->getType())) {
						if (SW > 64) { MatInProg.erase(V); return nullptr; }
						Src = materialize(Src);
						if (!Src) { MatInProg.erase(V); return nullptr; }
						SrcW = SW;
					} else if (!Src->getType()->isIntegerTy(64))
						Src = B.CreateZExtOrTrunc(Src, I64Ty, "il.ss64");
					Value* Sh = ConstantInt::get(I64Ty, 64 - SrcW);
					R = B.CreateAnd(
						B.CreateAShr(B.CreateShl(Src, Sh), Sh, "il.sext"),
						i64Mask(W), "il.sextm");
				} else {
					MatInProg.erase(V);
					return nullptr;
				}
				I64Of[V] = R;
				MatInProg.erase(V);
				if (!rewriteUsers(V, R, W)) {
					// Nested promote/materialize may have finished rewriting
					// every use of V even though this call returned false
					// (e.g. peer binop order). Treat use-empty as success.
					if (auto* I = dyn_cast<Instruction>(V)) {
						if (I->use_empty()) {
							I->eraseFromParent();
							return R;
						}
					}
					return nullptr;
				}
				if (auto* I = dyn_cast<Instruction>(V))
					if (I->use_empty()) I->eraseFromParent();
				return R;
			};

			SmallVector<Instruction*, 32> Roots;
			for (BasicBlock& BB : F)
				for (Instruction& I : BB) {
					unsigned W = illegalInt(I.getType());
					if (!W || W > 64) continue;
					if (isa<LoadInst>(&I) || isa<TruncInst>(&I) ||
						isa<ZExtInst>(&I) || isa<SExtInst>(&I))
						Roots.push_back(&I);
				}
			for (Instruction* Root : Roots) {
				if (!Root->getParent() || Root->use_empty()) continue;
				materialize(Root);
			}
			// Post-promote DCE: illegal ops whose consumers were rewritten to
			// the i64 form can remain as a dead chain (e.g. add→sub with no
			// external uses). Erase use-empty only — live illegal values are
			// real failures left for the emitter to reject.
			bool IlDCE = true;
			while (IlDCE) {
				IlDCE = false;
				for (BasicBlock& BB : F) {
					for (Instruction& I : make_early_inc_range(BB)) {
						if (!illegalInt(I.getType()) || !I.use_empty())
							continue;
						I.eraseFromParent();
						IlDCE = true;
					}
				}
			}
		}
	}

	// 2-field aggregate loads with extractvalue-only users → scalar loads.
	{
		SmallVector<LoadInst*, 16> AggLoads;
		for (BasicBlock& BB : F)
			for (Instruction& I : BB) {
				auto* LI = dyn_cast<LoadInst>(&I);
				if (!LI) continue;
				auto* ST = dyn_cast<StructType>(LI->getType());
				if (!ST || ST->getNumElements() != 2) continue;
				if (!isSupportedPairElem(ST->getElementType(0)) ||
					!isSupportedPairElem(ST->getElementType(1)))
					continue;
				bool Ok = !LI->user_empty();
				for (User* U : LI->users()) {
					if (auto* EV = dyn_cast<ExtractValueInst>(U)) {
						if (EV->getNumIndices() != 1 || EV->getIndices()[0] > 1) {
							Ok = false; break;
						}
						continue;
					}
					if (auto* SI = dyn_cast<StoreInst>(U)) {
						if (SI->getValueOperand() != LI) { Ok = false; break; }
						continue;
					}
					Ok = false;
					break;
				}
				if (Ok) AggLoads.push_back(LI);
			}
		for (LoadInst* LI : AggLoads) {
			IRBuilder<> B(LI);
			auto* ST = cast<StructType>(LI->getType());
			Value* Base = LI->getPointerOperand();
			Align A0 = LI->getAlign();
			const StructLayout* SL = DL.getStructLayout(ST);
			auto loadField = [&](unsigned Idx) -> Value* {
				Type* FT = ST->getElementType(Idx);
				uint64_t Off = SL->getElementOffset(Idx);
				Value* Ptr = Off
					? B.CreateGEP(I8Ty, Base, B.getInt64(Off), "ag.p")
					: Base;
				Align A = commonAlignment(A0, Off);
				if (FT->isPointerTy())
					return B.CreateAlignedLoad(PtrTy, Ptr, A, LI->isVolatile(), "ag.ld");
				if (FT->isIntegerTy(64))
					return B.CreateAlignedLoad(I64Ty, Ptr, A, LI->isVolatile(), "ag.ld");
				unsigned W = FT->getIntegerBitWidth();
				if (W <= 32) {
					Type* LoadTy = (W <= 8) ? I8Ty : (W <= 16) ? I16Ty : I32Ty;
					Value* V = B.CreateAlignedLoad(LoadTy, Ptr, A, LI->isVolatile(), "ag.ld");
					if (LoadTy != I32Ty)
						V = B.CreateZExt(V, I32Ty, "ag.z");
					if (W == 1)
						V = B.CreateAnd(V, ConstantInt::get(I32Ty, 1), "ag.i1");
					return V;
				}
				return B.CreateAlignedLoad(I64Ty, Ptr, A, LI->isVolatile(), "ag.ld");
			};
			auto storeField = [&](IRBuilder<>& SB, Value* Dest, unsigned Idx, Value* V) {
				Type* FT = ST->getElementType(Idx);
				uint64_t Off = SL->getElementOffset(Idx);
				Value* Ptr = Off
					? SB.CreateGEP(I8Ty, Dest, SB.getInt64(Off), "ag.sp")
					: Dest;
				if (FT->isPointerTy()) {
					SB.CreateStore(V, Ptr); return;
				}
				if (FT->isIntegerTy(64)) {
					SB.CreateStore(V, Ptr); return;
				}
				unsigned W = FT->getIntegerBitWidth();
				Type* StTy = (W <= 8) ? I8Ty : (W <= 16) ? I16Ty : I32Ty;
				Value* SV = V;
				if (SV->getType() != StTy)
					SV = SB.CreateTrunc(SV, StTy, "ag.tr");
				SB.CreateStore(SV, Ptr);
			};
			Value* V0 = loadField(0);
			Value* V1 = loadField(1);
			SmallVector<Instruction*, 4> Dead;
			for (User* U : LI->users()) {
				if (auto* EV = dyn_cast<ExtractValueInst>(U)) {
					EV->replaceAllUsesWith(EV->getIndices()[0] == 0 ? V0 : V1);
					Dead.push_back(EV);
				} else if (auto* SI = dyn_cast<StoreInst>(U)) {
					IRBuilder<> SB(SI);
					storeField(SB, SI->getPointerOperand(), 0, V0);
					storeField(SB, SI->getPointerOperand(), 1, V1);
					Dead.push_back(SI);
				}
			}
			for (Instruction* D : Dead) D->eraseFromParent();
			LI->eraseFromParent();
		}
	}

	// Odd 2-field call returns (not {ptr,i64}): sret wrapper + field loads.
	{
		SmallVector<CallInst*, 16> PairCalls;
		for (BasicBlock& BB : F)
			for (Instruction& I : BB) {
				auto* CI = dyn_cast<CallInst>(&I);
				if (!CI) continue;
				if (Function* CF = CI->getCalledFunction(); CF && CF->isIntrinsic())
					continue;
				Type* RT = CI->getType();
				auto* ST = dyn_cast<StructType>(RT);
				if (!ST || ST->getNumElements() != 2) continue;
				if (isPtrI64Pair(RT)) continue;
				if (!isSupportedPairElem(ST->getElementType(0)) ||
					!isSupportedPairElem(ST->getElementType(1)))
					continue;
				bool Ok = !CI->user_empty();
				for (User* U : CI->users()) {
					if (auto* EV = dyn_cast<ExtractValueInst>(U)) {
						if (EV->getNumIndices() != 1 || EV->getIndices()[0] > 1) {
							Ok = false; break;
						}
						continue;
					}
					if (auto* SI = dyn_cast<StoreInst>(U)) {
						if (SI->getValueOperand() != CI) { Ok = false; break; }
						continue;
					}
					Ok = false;
					break;
				}
				if (Ok) PairCalls.push_back(CI);
			}

		unsigned SretId = 0;
		for (CallInst* CI : PairCalls) {
			auto* ST = cast<StructType>(CI->getType());
			Function* CalleeF = CI->getCalledFunction();
			Value* CalleeV = CI->getCalledOperand();

			SmallVector<Type*, 8> WParams;
			WParams.push_back(PtrTy);
			for (Value* A : CI->args())
				WParams.push_back(A->getType());
			if (!CalleeF)
				WParams.push_back(CalleeV->getType());
			FunctionType* WTy = FunctionType::get(Type::getVoidTy(Ctx), WParams, false);
			std::string WName = ("__vm_sret_" + std::to_string(SretId++) + "_" +
				(CalleeF ? CalleeF->getName() : "ind")).str();
			for (char& C : WName)
				if (!std::isalnum((unsigned char)C)) C = '_';

			Function* WF = Function::Create(WTy, GlobalValue::InternalLinkage, WName, &M);
			WF->addFnAttr(Attribute::NoInline);
			WF->addFnAttr(Attribute::NoUnwind);
			WF->addParamAttr(0, Attribute::getWithStructRetType(Ctx, ST));
			BasicBlock* WBB = BasicBlock::Create(Ctx, "entry", WF);
			IRBuilder<> WB(WBB);
			SmallVector<Value*, 8> CallArgs;
			unsigned ArgEnd = CalleeF ? WF->arg_size() : WF->arg_size() - 1;
			for (unsigned i = 1; i < ArgEnd; ++i)
				CallArgs.push_back(WF->getArg(i));
			CallInst* Inner = CalleeF
				? WB.CreateCall(CalleeF, CallArgs, "sret.r")
				: WB.CreateCall(CI->getFunctionType(), WF->getArg(ArgEnd), CallArgs, "sret.r");
			WB.CreateStore(Inner, WF->getArg(0));
			WB.CreateRetVoid();

			IRBuilder<> B(CI);
			IRBuilder<> EB(&F.getEntryBlock(),
				F.getEntryBlock().getFirstInsertionPt());
			AllocaInst* Tmp = EB.CreateAlloca(ST, nullptr, "sret.tmp");
			SmallVector<Value*, 8> SiteArgs;
			SiteArgs.push_back(Tmp);
			for (Value* A : CI->args())
				SiteArgs.push_back(A);
			if (!CalleeF)
				SiteArgs.push_back(CalleeV);
			B.CreateCall(WF, SiteArgs);

			const StructLayout* SL = DL.getStructLayout(ST);
			auto loadField = [&](unsigned Idx) -> Value* {
				Type* FT = ST->getElementType(Idx);
				uint64_t Off = SL->getElementOffset(Idx);
				Value* Ptr = Off
					? B.CreateGEP(I8Ty, Tmp, B.getInt64(Off), "sret.p")
					: Tmp;
				if (FT->isPointerTy())
					return B.CreateLoad(PtrTy, Ptr, "sret.ld");
				if (FT->isIntegerTy(64))
					return B.CreateLoad(I64Ty, Ptr, "sret.ld");
				unsigned W = FT->getIntegerBitWidth();
				Type* LoadTy = (W <= 8) ? I8Ty : (W <= 16) ? I16Ty : I32Ty;
				Value* V = B.CreateLoad(LoadTy, Ptr, "sret.ld");
				if (LoadTy != I32Ty)
					V = B.CreateZExt(V, I32Ty, "sret.z");
				return V;
			};
			Value* V0 = loadField(0);
			Value* V1 = loadField(1);
			auto storeField = [&](IRBuilder<>& SB, Value* Dest, unsigned Idx, Value* V) {
				Type* FT = ST->getElementType(Idx);
				uint64_t Off = SL->getElementOffset(Idx);
				Value* Ptr = Off
					? SB.CreateGEP(I8Ty, Dest, SB.getInt64(Off), "sret.sp")
					: Dest;
				if (FT->isPointerTy() || FT->isIntegerTy(64)) {
					SB.CreateStore(V, Ptr); return;
				}
				unsigned W = FT->getIntegerBitWidth();
				Type* StTy = (W <= 8) ? I8Ty : (W <= 16) ? I16Ty : I32Ty;
				Value* SV = (V->getType() == StTy) ? V : SB.CreateTrunc(V, StTy, "sret.tr");
				SB.CreateStore(SV, Ptr);
			};
			SmallVector<Instruction*, 4> Dead;
			for (User* U : CI->users()) {
				if (auto* EV = dyn_cast<ExtractValueInst>(U)) {
					EV->replaceAllUsesWith(EV->getIndices()[0] == 0 ? V0 : V1);
					Dead.push_back(EV);
				} else if (auto* SI = dyn_cast<StoreInst>(U)) {
					IRBuilder<> SB(SI);
					storeField(SB, SI->getPointerOperand(), 0, V0);
					storeField(SB, SI->getPointerOperand(), 1, V1);
					Dead.push_back(SI);
				}
			}
			for (Instruction* D : Dead) D->eraseFromParent();
			CI->eraseFromParent();
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
