#pragma once
// ============================================================================
// VMPass_Emitter.h — Code Virtualisation pass: BytecodeEmitter
//
// BytecodeEmitter is a two-pass IR → bytecode compiler:
//
//   Pass 1  (slots)
//       Assign register slots with liveness reuse: function arguments and
//       entry-block allocas are pinned for the whole function; remaining SSA
//       results allocate from a free-list (or bump the high-water mark) and
//       release their slot after their last use in walk order.  NVR/NPR/…
//       record the high-water mark (max live), not the instruction count.
//
//   Pass 2  (emit)
//       Walk every instruction again and write the actual opcode bytes into
//       the BC vector.  Every register-index byte is XOR'd with the low byte
//       of SaltConst when obfRegIdx=1.
//
// After a successful run() the public output fields are consumed by VMImpl
// to build the interpreter IR.
//
// Step 01.1 additions:
//   - FR   DenseMap<Value*, uint8_t>  — f64 SSA value → freg slot
//   - ImmLoadsF SmallVector            — constant-FP pre-loads into fregs
//   - NFR  uint8_t                    — total freg slots used
//   - newFR / fr                      — slot allocation helpers (private)
//   - f64() bytecode primitive        — emits an 8-byte IEEE-754 double LE
// ============================================================================

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Transforms/Obfuscator/VMPass_ISA.h"

#include <cstring>
#include <utility>

namespace llvm {

	class BasicBlock;
	class ConstantInt;
	class ConstantFP;
	class DataLayout;
	class Instruction;
	class Type;

	// ============================================================================
	// BytecodeEmitter
	// ============================================================================

	struct BytecodeEmitter {
		static constexpr uint8_t kInvalidSlot = 0xFF;
		// Soft cap under the u8 ISA index + kInvalidSlot. Overflow = max-live,
		// not instruction count (see free-list reuse in newVR*).
		static constexpr uint8_t kMaxSlots = 250;

		// ── Output fields — read by VMImpl after a successful run() ─────────

		SmallVector<uint8_t, 1024>       BC;         // raw bytecode bytes
		DenseMap<BasicBlock*, uint32_t>  BlockIP;    // first IP of each block
		DenseMap<Value*, uint8_t>        VR;         // i32  SSA value  → vreg   slot
		DenseMap<Value*, uint8_t>        VR64;       // i64  SSA value  → vreg64 slot
		DenseMap<Value*, uint8_t>        PR;         // ptr  SSA value  → preg   slot
		DenseMap<Value*, uint8_t>        FR;         // f64  SSA value  → freg   slot [Step 01.1]
		// OP_CALL_PAIR: CallInst → {preg, vreg64}; extractvalue aliases these slots.
		DenseMap<Value*, std::pair<uint8_t, uint8_t>> PairSlots;
		SmallVector<Value*, 8>           CalleeTab;  // callee table (CALL* targets)
		// 6.2: parallel FunctionType table -- one entry per CalleeTab slot.
		SmallVector<FunctionType*, 8>    CalleeFTyTab;
		// Indirect calls: one null placeholder per FunctionType. The runtime
		// callee is a preg (nargs bit 7); the slot exists only so GVFTyIndices
		// has a type. Never store the instruction itself — stripBody() frees it
		// before the callee global is emitted.
		DenseMap<FunctionType*, uint8_t> IndFTySlot;
		DenseSet<unsigned>               IndSlots;

		/// Metadata for an entry-block alloca created by PHI demotion.
		struct PhiAllocaDesc {
			uint8_t     Slot = 0;       // preg slot assigned to this alloca
			Type* AllocTy = nullptr;
			MaybeAlign  A;                // original alignment (if any)
			std::string Name;             // stable debug-friendly name
		};
		SmallVector<PhiAllocaDesc, 8>    PHIAllocas;  // demoted PHI allocas, in preg order

		// Pre-load lists built during slot assignment; consumed by VMImpl::buildVMEntry.
		SmallVector<std::pair<uint8_t, ConstantInt*>, 16>  ImmLoads;    // vreg   slot, ConstantInt (<=32-bit)
		SmallVector<std::pair<uint8_t, ConstantInt*>, 16>  ImmLoads64;  // vreg64 slot, ConstantInt (i64)
		SmallVector<std::pair<uint8_t, Value*>, 16> PtrLoads;    // preg   slot, global/null ptr
		SmallVector<std::pair<uint8_t, ConstantFP*>, 8>  ImmLoadsF;   // freg   slot, ConstantFP (f64/f32) [Step 01.1]

		uint8_t NVR = 0;  // vreg   high-water (max live)
		uint8_t NVR64 = 0;  // vreg64 high-water (max live)
		uint8_t NPR = 0;  // preg   high-water (max live)
		uint8_t NFR = 0;  // freg   high-water (max live)


		// When an instruction cannot be virtualised Unsupported is set and run()
		// returns false.  FailReason describes the first problem found.
		bool         Unsupported = false;
		Instruction* FirstUnsupportedInst = nullptr;
		Value* FirstUnsupportedVal = nullptr;
		std::string  FirstUnsupportedWhy;
		std::string  FailReason;

		// ── Public interface ─────────────────────────────────────────────────

		StringRef getFailReason() const { return FailReason; }

		/// Set the per-function opcode permutation map before calling run().
		void setOpcodeMap(const VMOpcodeMap* M) { OpMap = M; }

		/// P3-B: configure branch-target blinding. saltFull is the full 32-bit
		/// per-function salt (SaltConst); on is the blindTargets knob.
		void setTargetBlind(uint32_t saltFull, bool on) { SaltFull = saltFull; BlindTargets = on; }

		/// Move int/i64/fp constant slot seeding into the encrypted bytecode
		/// stream (as an OP_LOADI*/OP_LOADI64/OP_LOADI_F prologue) instead of
		/// leaving it for the wrapper's plaintext preload stores.
		void setConstInStream(bool on) { ConstInStream = on; }

		/// keyedDispatch: XOR each written opcode byte with a per-IP compile-time
		/// key derived from saltFull (see opKeyByteCT); on is the knob.
		void setKeyedDispatch(uint32_t saltFull, bool on) { KeyedSalt = saltFull; KeyedDispatch = on; }

		/// superOps: fuse eligible i32 `mul`+`add` chains into a single
		/// OP_MULADD opcode instead of two OP_BINOP opcodes.
		void setSuperOps(bool on) { SuperOps = on; }

		/// randISA (P9-A): module-uniform permutation of semantic operand-field
		/// byte encodings. When null (or identity), subop bytes are written raw
		/// (byte-identical to pre-feature). The pointed-to map must be the same
		/// module-wide instance the shared handler switch-cases were built from.
		void setISAEnc(const ISAEnc* E) { IsaEnc = E; }

		/// Compile F into bytecode.  Salt is the CTSalt byte used to XOR register
		/// index bytes (0 when obfRegIdx is disabled).
		/// Returns false on failure; FailReason is populated.
		bool run(Function& F, uint8_t Salt, const DataLayout& DL);

	private:
		uint8_t            Salt = 0;
		const DataLayout* DL = nullptr;
		const VMOpcodeMap* OpMap = nullptr;
		uint32_t           SaltFull = 0;
		bool               BlindTargets = false;
		bool               ConstInStream = false;
		uint32_t           KeyedSalt = 0;
		bool               KeyedDispatch = false;
		bool               SuperOps = false;
		const ISAEnc* IsaEnc = nullptr;

		/// Apply the RandISA BinSubop permutation (identity when off/null).
		uint8_t encBinSubop(uint8_t Logical) const {
			return IsaEnc ? IsaEnc->encBinSubop(Logical) : Logical;
		}

		/// Apply the RandISA ICmp-predicate permutation (identity when off/null).
		uint8_t encIcmpPred(uint8_t Pred) const {
			return IsaEnc ? IsaEnc->encIcmpPred(Pred) : Pred;
		}

		/// Apply the RandISA CastKind permutation (identity when off/null).
		uint8_t encCastKind(uint8_t Kind) const {
			return IsaEnc ? IsaEnc->encCastKind(Kind) : Kind;
		}

		/// Apply the RandISA FBinSubop permutation to the op part (identity when
		/// off/null). Caller masks off / re-applies the bit-7 f32 flag.
		uint8_t encFBinSubop(uint8_t Op) const {
			return IsaEnc ? IsaEnc->encFBinSubop(Op) : Op;
		}

		/// Apply the RandISA FCmp-predicate permutation (identity when off/null).
		uint8_t encFcmpPred(uint8_t Pred) const {
			return IsaEnc ? IsaEnc->encFcmpPred(Pred) : Pred;
		}

		// superOps: `add` -> the `mul` fused into it. The fused OP_MULADD is
		// emitted where the ADD naturally sits in program order (not the
		// mul's position) -- SSA dominance already guarantees every operand
		// of the add (including the mul's own inputs) is available there, in
		// any block relationship between the two, with no extra checks
		// needed. Populated by scanSuperOps() before slot pre-assignment;
		// consumed by emit(Instruction*).
		DenseMap<Instruction*, Instruction*> FusedAddToMul;
		// superOps: `mul` instructions folded away -- they get no vreg slot
		// (pre-assignment loop) and emit no bytes (emit(Instruction*));
		// their result is computed inline by the fused OP_MULADD instead.
		DenseSet<Instruction*> SkippedMuls;

		// superOps: `add` -> the `shl` fused into it (OP_SHLADD). Same
		// position/dominance argument as FusedAddToMul.
		DenseMap<Instruction*, Instruction*> FusedAddToShl;
		// superOps: `shl` folded away -- no vreg slot, emits no bytes.
		DenseSet<Instruction*> SkippedShls;

		// superOps: `select` -> the `icmp` fused into it as its condition
		// (OP_CMPSEL). The icmp (and any dead extra users of it) is folded
		// away (no slot, no bytes).
		DenseMap<Instruction*, Instruction*> FusedSelToCmp;
		DenseSet<Instruction*> SkippedCmps;

		// superOps: `icmp eq|ne %m,0` -> the `and` fused into it (OP_ANDCMPZ).
		// The `and` is folded away (no slot, no bytes); OP_ANDCMPZ is emitted
		// at the compare's position and yields the compare's i32 0/1 result.
		DenseMap<Instruction*, Instruction*> FusedCmpToAnd;
		DenseSet<Instruction*> SkippedAnds;

		// superOps: identify fusion candidates in F -- `%m = mul i32 %a,%b`
		// with exactly one use, that use being a direct `%d = add i32 %m,%c`
		// (i32, any block). No availability check is needed for %c: since
		// emission happens at %d's own position, every operand %d has in the
		// original program (including %m's inputs %a/%b, which dominate %m
		// and therefore %d) is already resolvable there.
		void scanSuperOps(Function& F);
		// keyedDispatch: pre-splice IP of every opcode byte written by bop(), in
		// emission order. Consumed by the constInStream prologue-splice step in
		// run() to re-key body opcode bytes once their final (post-splice) IP is
		// known; unused (and left empty) otherwise.
		SmallVector<uint32_t, 64> KeyedOpIPs;

		// keyedDispatch: per-IP opcode-byte XOR key mix. Mirrors VMImpl::opKeyByteIR
		// op-for-op and is duplicated verbatim in verifyBytecode() (VMPass_Verifier.cpp)
		// so all three sites decode the same physical byte the same way.
		static uint8_t opKeyByteCT(uint32_t salt, uint32_t ip) {
			uint32_t k = (salt * (ip + 1u)) ^ (salt >> 8);
			return (uint8_t)(k & 0xFFu);
		}

		// P3-B: compile-time branch-target blinding key mix. Mirrors VMImpl::tgtKeyIR
		// op-for-op; distinct constants from ksByteCT (Layer-1 keystream) so the two
		// blinding layers don't share a constant.
		static uint32_t tgtKeyCT(uint32_t salt) {
			uint32_t k = salt ^ 0x2545F491u;
			k *= 0x9E3779B1u;
			k ^= k >> 16;
			return k;
		}

		// ── Liveness reuse ───────────────────────────────────────────────────
		// Free lists recycle slots after last use. Pinned values (args, entry
		// allocas, constants, OP_CALL_PAIR aliases) never release. LastUse maps
		// each Value* to the Instruction* that is its last consumer in the
		// same walk order used by slot assignment (see computeLastUses).
		SmallVector<uint8_t, 32> FreeVR;
		SmallVector<uint8_t, 32> FreeVR64;
		SmallVector<uint8_t, 32> FreePR;
		SmallVector<uint8_t, 32> FreeFR;
		DenseSet<Value*>         Pinned;
		DenseSet<Value*>         Released; // idempotent releaseValue (fused+operand overlap)
		DenseMap<Value*, Instruction*> LastUse;

		void pin(Value* V) { if (V) Pinned.insert(V); }

		// Bump high-water only — for values that must stay valid from function
		// entry (args already allocated pre-reuse; constants / PtrLoads).
		uint8_t takeFreshSlot(uint8_t& HighWater, const char* OverflowMsg) {
			if (HighWater >= kMaxSlots) {
				Unsupported = true;
				if (FailReason.empty()) FailReason = OverflowMsg;
				return kInvalidSlot;
			}
			return HighWater++;
		}

		uint8_t takeSlot(uint8_t& HighWater, SmallVectorImpl<uint8_t>& Free,
			const char* OverflowMsg) {
			if (!Free.empty())
				return Free.pop_back_val();
			return takeFreshSlot(HighWater, OverflowMsg);
		}

		// Recycle only values whose every IR user is in the defining block.
		// Cross-block / loop-carried values keep their slot for the whole
		// function (safe without full live-out analysis). Same-BB temps —
		// including those inside loops — are safe: the def re-executes before
		// the next use on each iteration.
		bool canRecycle(Value* V) const {
			auto* DefI = dyn_cast<Instruction>(V);
			if (!DefI) return false;
			BasicBlock* DB = DefI->getParent();
			for (const User* U : V->users()) {
				auto* UI = dyn_cast<Instruction>(U);
				if (!UI || UI->getParent() != DB) return false;
			}
			return true;
		}

		void releaseValue(Value* V) {
			if (!V || Pinned.count(V) || !canRecycle(V)) return;
			// Fused-operand tryRel can name the same Value* already released via
			// I->operands() (e.g. muladd `%d=add %m,%a` with `%m=mul %a,%b`, or
			// cmpsel where a select arm is also a cmp input). Pushing the slot
			// twice would hand one physical index to two simultaneously live
			// values — hard overlap / runtime corruption.
			if (!Released.insert(V).second) return;
			{
				auto It = VR.find(V);
				if (It != VR.end()) { FreeVR.push_back(It->second); return; }
			}
			{
				auto It = VR64.find(V);
				if (It != VR64.end()) { FreeVR64.push_back(It->second); return; }
			}
			{
				auto It = PR.find(V);
				if (It != PR.end()) { FreePR.push_back(It->second); return; }
			}
			{
				auto It = FR.find(V);
				if (It != FR.end()) { FreeFR.push_back(It->second); return; }
			}
		}

		void releaseDeadAt(Instruction* I) {
			auto tryRel = [&](Value* V) {
				auto It = LastUse.find(V);
				if (It != LastUse.end() && It->second == I)
					releaseValue(V);
			};
			for (Use& U : I->operands())
				tryRel(U.get());
			// superOps: folded operands are read at the consumer but are not
			// in I's operand list — release them here to match computeLastUses.
			{
				auto It = FusedAddToMul.find(I);
				if (It != FusedAddToMul.end()) {
					tryRel(It->second->getOperand(0));
					tryRel(It->second->getOperand(1));
				}
			}
			{
				auto It = FusedAddToShl.find(I);
				if (It != FusedAddToShl.end()) {
					tryRel(It->second->getOperand(0));
					tryRel(It->second->getOperand(1));
				}
			}
			{
				auto It = FusedSelToCmp.find(I);
				if (It != FusedSelToCmp.end()) {
					tryRel(It->second->getOperand(0));
					tryRel(It->second->getOperand(1));
				}
			}
			{
				auto It = FusedCmpToAnd.find(I);
				if (It != FusedCmpToAnd.end()) {
					tryRel(It->second->getOperand(0));
					tryRel(It->second->getOperand(1));
				}
			}
			// Dead def: no recorded use → free immediately after assign.
			if (!LastUse.count(I))
				releaseValue(I);
		}

		void computeLastUses(Function& F);

		// ── Idempotent slot allocation (safe to call in both passes) ─────────

		uint8_t newVR(Value* V) {
			auto It = VR.find(V);
			if (It != VR.end()) return It->second;
			uint8_t S = takeSlot(NVR, FreeVR, "vreg file overflow (>250 slots)");
			if (S == kInvalidSlot) return S;
			VR[V] = S;
			return S;
		}

		uint8_t newVR64(Value* V) {
			auto It = VR64.find(V);
			if (It != VR64.end()) return It->second;
			uint8_t S = takeSlot(NVR64, FreeVR64, "vreg64 file overflow (>250 slots)");
			if (S == kInvalidSlot) return S;
			VR64[V] = S;
			return S;
		}


		uint8_t newPR(Value* V) {
			auto It = PR.find(V);
			if (It != PR.end()) return It->second;
			uint8_t S = takeSlot(NPR, FreePR, "preg file overflow (>250 slots)");
			if (S == kInvalidSlot) return S;
			PR[V] = S;
			return S;
		}

		// Scratch preg for multi-op expansions (e.g. store {ptr,i64}); not tied
		// to an SSA value. Caller must freeScratchPR after the expansion.
		uint8_t allocScratchPR() {
			return takeSlot(NPR, FreePR, "preg file overflow (>250 slots)");
		}
		void freeScratchPR(uint8_t S) {
			if (S != kInvalidSlot) FreePR.push_back(S);
		}

		// ── Float register slot allocation ───────────────────────
		//
		// The freg file holds f64 (double) values.  f32 values from the LLVM IR
		// are widened to f64 on slot assignment and narrowed to f32 on STORE_F /
		// RET_F by the handler, transparently to the bytecode encoding.

		uint8_t newFR(Value* V) {
			auto It = FR.find(V);
			if (It != FR.end()) return It->second;
			uint8_t S = takeSlot(NFR, FreeFR, "freg file overflow (>250 slots)");
			if (S == kInvalidSlot) return S;
			FR[V] = S;
			return S;
		}

		uint8_t xorSalt(uint8_t S) const { return S ^ Salt; }

		void setFail(StringRef R) { if (FailReason.empty()) FailReason = R.str(); }

		std::string describeUnsupported() const {
			std::string S;
			raw_string_ostream OS(S);
			if (!FirstUnsupportedWhy.empty())
				OS << FirstUnsupportedWhy << ": ";
			if (FirstUnsupportedInst)
				FirstUnsupportedInst->print(OS);
			else if (FirstUnsupportedVal)
				FirstUnsupportedVal->print(OS);
			else
				OS << "<unknown>";
			OS.flush();
			for (char& C : S) if (C == '\n' || C == '\r') C = ' ';
			return S;
		}

		void markUnsupported(Instruction* I, StringRef Why = "unsupported instruction") {
			Unsupported = true;
			if (!FirstUnsupportedInst && !FirstUnsupportedVal) {
				FirstUnsupportedInst = I;
				FirstUnsupportedWhy = Why.str();
			}
		}

		void markUnsupportedValue(Value* V, StringRef Why = "unsupported value") {
			Unsupported = true;
			if (!FirstUnsupportedInst && !FirstUnsupportedVal) {
				FirstUnsupportedVal = V;
				FirstUnsupportedWhy = Why.str();
			}
		}

		// ── Slot resolution with constant materialisation ────────────────────

		// resolve vreg slot, materialising ConstantInt on first use
		uint8_t vr(Value* V) {
			if (auto* CI = dyn_cast<ConstantInt>(V)) {
				if (CI->getType()->getIntegerBitWidth() > 32) { markUnsupportedValue(V); return 0; }
				auto It = VR.find(V);
				if (It != VR.end()) return It->second;
				// Fresh slot only: ImmLoads / prologue seed at entry; a recycled
				// index would still be written by the SSA def that freed it.
				uint8_t S = takeFreshSlot(NVR, "vreg file overflow (>250 slots)");
				if (S == kInvalidSlot) return S;
				VR[V] = S;
				pin(V);
				ImmLoads.push_back({ S, CI });
				return S;
			}
			auto It = VR.find(V);
			assert(It != VR.end() && "vr(): untracked value");
			return It->second;
		}

		uint8_t vr64(Value* V) {
			if (auto* CI = dyn_cast<ConstantInt>(V)) {
				if (!CI->getType()->isIntegerTy(64)) { markUnsupportedValue(V); return 0; }
				auto It = VR64.find(V);
				if (It != VR64.end()) return It->second;
				uint8_t S = takeFreshSlot(NVR64, "vreg64 file overflow (>250 slots)");
				if (S == kInvalidSlot) return S;
				VR64[V] = S;
				pin(V);
				ImmLoads64.push_back({ S, CI });
				return S;
			}
			auto It = VR64.find(V);
			assert(It != VR64.end() && "vr64(): untracked value");
			return It->second;
		}

		// resolve preg slot, materialising ptr constant on first use
		uint8_t pr(Value* V) {
			auto It = PR.find(V);
			if (It != PR.end()) return It->second;
			assert(isa<Constant>(V) && "pr(): untracked non-const ptr");
			uint8_t S = takeFreshSlot(NPR, "preg file overflow (>250 slots)");
			if (S == kInvalidSlot) return S;
			PR[V] = S;
			pin(V);
			PtrLoads.push_back({ S, V });
			return S;
		}

		// ── [Step 01.1] Float constant materialisation ───────────────────────
		//
		// resolve freg slot, materialising ConstantFP on first use.
		// Both f32 and f64 ConstantFP values are accepted — the handler widens
		// f32 to f64 when loading the slot via OP_LOADI_F (ImmLoadsF path).

		uint8_t fr(Value* V) {
			if (auto* CFP = dyn_cast<ConstantFP>(V)) {
				Type* Ty = CFP->getType();
				if (!Ty->isFloatTy() && !Ty->isDoubleTy()) {
					markUnsupportedValue(V, "unsupported FP constant type (not f32/f64)");
					return 0;
				}
				auto It = FR.find(V);
				if (It != FR.end()) return It->second;
				uint8_t S = takeFreshSlot(NFR, "freg file overflow (>250 slots)");
				if (S == kInvalidSlot) return S;
				FR[V] = S;
				pin(V);
				ImmLoadsF.push_back({ S, CFP });
				return S;
			}
			auto It = FR.find(V);
			assert(It != FR.end() && "fr(): untracked float value");
			return It->second;
		}

		uint8_t callee(Value* C) {
			for (unsigned I = 0; I < CalleeTab.size(); ++I) {
				if (IndSlots.count(I)) continue;
				if (CalleeTab[I] == C) return (uint8_t)I;
			}
			assert(CalleeTab.size() < 252); CalleeTab.push_back(C);
			return (uint8_t)(CalleeTab.size() - 1);
		}

		// 6.2: callee registration with its FunctionType.
		uint8_t callee(Value* C, FunctionType* FTy) {
			// Vararg callees are never deduplicated: each call site has a
			// unique concrete FTy (arg count may differ between call sites).
			if (!FTy->isVarArg())
				for (unsigned I = 0; I < CalleeTab.size(); ++I) {
					if (IndSlots.count(I)) continue;
					if (CalleeTab[I] == C) return (uint8_t)I;
				}
			assert(CalleeTab.size() < 252); CalleeTab.push_back(C); CalleeFTyTab.push_back(FTy);
			return (uint8_t)(CalleeTab.size() - 1);
		}

		// Null placeholder keyed by FunctionType. Bit 7 of nargs tells the
		// handler to call a preg instead of this slot.
		uint8_t indirectCalleeSlot(FunctionType* FTy) {
			auto It = IndFTySlot.find(FTy);
			if (It != IndFTySlot.end()) return It->second;
			assert(CalleeTab.size() < 252);
			uint8_t I = (uint8_t)CalleeTab.size();
			auto* PTy = PointerType::getUnqual(FTy->getContext());
			CalleeTab.push_back(ConstantPointerNull::get(PTy));
			CalleeFTyTab.push_back(FTy);
			IndFTySlot[FTy] = I;
			IndSlots.insert(I);
			return I;
		}

		// ── Bytecode emission primitives ──────────────────────────────────────

		uint8_t encOp(VMOp Op) const { return OpMap ? OpMap->encode(Op) : (uint8_t)Op; }
		void bop(VMOp Op) {
			uint8_t v = encOp(Op);
			// keyedDispatch: K(IP) is baked in using ip() as it stands right now.
			// When constInStream later splices a prologue in front of the
			// already-emitted body, every body opcode byte's final position moves
			// by PrologueLen -- the baked-in mask no longer matches. Record this
			// byte's pre-splice IP so run()'s constInStream block can re-key it
			// once the real final position is known (see the KeyedOpIPs walk
			// there). Prologue opcodes are written after the splice point is
			// decided, so their ip() is already final and never need correcting.
			if (KeyedDispatch) {
				uint32_t IP = ip();
				v ^= opKeyByteCT(KeyedSalt, IP);
				KeyedOpIPs.push_back(IP);
			}
			b8(v);
		}

		void     b8(uint8_t v) { BC.push_back(v); }
		void     u16(uint16_t v) { b8(v & 0xFF); b8(v >> 8); }
		void     u32(uint32_t v) { b8(v); b8(v >> 8); b8(v >> 16); b8(v >> 24); }
		void     u64(uint64_t v) { u32((uint32_t)v); u32((uint32_t)(v >> 32)); }
		uint32_t ip() const { return (uint32_t)BC.size(); }

		/// [Step 01.1] Emit an f64 value as 8 bytes, little-endian IEEE-754.
		/// Used by OP_LOADI_F during pass 2 (emit).
		void f64(double V) {
			uint64_t Bits;
			static_assert(sizeof(Bits) == sizeof(V), "f64 size mismatch");
			std::memcpy(&Bits, &V, 8);
			b8((uint8_t)(Bits));
			b8((uint8_t)(Bits >> 8));
			b8((uint8_t)(Bits >> 16));
			b8((uint8_t)(Bits >> 24));
			b8((uint8_t)(Bits >> 32));
			b8((uint8_t)(Bits >> 40));
			b8((uint8_t)(Bits >> 48));
			b8((uint8_t)(Bits >> 56));
		}

		void emit(BasicBlock* BB);
		void emit(Instruction* I);

		// ── Pass 1: sizing (kept for reference; unused by run() after Phase 2) ────────────────
		uint32_t isize(Instruction* I);
		uint32_t bsize(BasicBlock* BB);

	private:
		// ── Forward-branch fixup table ────────────────────────────────────────────────────────
		// fixup_u32() emits a 4-byte placeholder (0x00000000) and records its
		// offset so the patch loop in run() can fill in the resolved BlockIP.
		struct Fixup { uint32_t Offset; BasicBlock* Target; };
		SmallVector<Fixup, 32> Fixups;

		void fixup_u32(BasicBlock* BB) {
			Fixups.push_back({ ip(), BB });
			u32(0);  // placeholder — overwritten by run() patch loop
		}
	};

} // namespace llvm