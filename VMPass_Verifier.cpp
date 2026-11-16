// ============================================================================
// VMPass_Verifier.cpp — Code Virtualisation pass : Bytecode Verifier impl
// ============================================================================

#include "llvm/Transforms/Obfuscator/VMPass_Verifier.h"
#include "llvm/Transforms/Obfuscator/VMPass_Emitter.h"
#include "llvm/Transforms/Obfuscator/VMPass_ISA.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Twine.h"

using namespace llvm;

namespace llvm {

	bool verifyBytecode(const BytecodeEmitter& E, uint16_t CTSalt, const VMOpcodeMap& OpMap,
		std::string& OutErr, uint32_t& OutBadIP,
		uint32_t SaltFull, bool BlindTargets, bool KeyedDispatch) {
		const auto& BC = E.BC;

		// keyedDispatch: mirrors BytecodeEmitter::opKeyByteCT / VMImpl::opKeyByteIR
		// op-for-op so the opcode byte at each IP is un-XOR'd the same way the
		// runtime fetch path does before it is looked up in OpMap.P2L.
		auto opKeyByteCT = [](uint32_t salt, uint32_t ip) -> uint8_t {
			uint32_t k = (salt * (ip + 1u)) ^ (salt >> 8);
			return (uint8_t)(k & 0xFFu);
			};

		// P3-B: branch targets are stored XOR-blinded with tgtKey(SaltFull).
		// Mirror BytecodeEmitter::tgtKeyCT / VMImpl::tgtKeyIR so chkTarget can
		// recover the real offset before range-checking. TgtKey==0 (identity)
		// when blinding is off, so existing behavior is preserved.
		auto tgtKeyCT = [](uint32_t salt) -> uint32_t {
			uint32_t k = salt ^ 0x2545F491u;
			k *= 0x9E3779B1u;
			k ^= k >> 16;
			return k;
			};
		const uint32_t TgtKey = BlindTargets ? tgtKeyCT(SaltFull) : 0u;
		if (BC.empty()) {
			OutErr = "bytecode empty";
			OutBadIP = 0;
			return false;
		}

		DenseSet<uint32_t> BlockStarts;
		for (const auto& KV : E.BlockIP)
			BlockStarts.insert(KV.second);

		auto fail = [&](uint32_t IP, const Twine& Msg) -> bool {
			OutBadIP = IP;
			OutErr = Msg.str();
			for (char& C : OutErr) if (C == '\n' || C == '\r') C = ' ';
			return false;
			};

		auto decIdx = [&](uint16_t Raw) -> unsigned {
			return (unsigned)(Raw ^ CTSalt);
			};

		auto chk = [&](uint32_t IP, const char* Kind, unsigned Idx, unsigned Lim) -> bool {
			if (Idx >= Lim)
				return fail(IP, Twine(Kind) + " index " + Twine(Idx) + " out of range (limit=" + Twine(Lim) + ")");
			return true;
			};

		auto rdU16 = [&](uint32_t Off) -> uint16_t {
			return (uint16_t)((uint16_t)BC[Off] | ((uint16_t)BC[Off + 1] << 8));
			};
		auto rdIdx = [&](uint32_t Off) -> unsigned {
			return decIdx(rdU16(Off));
			};
		auto rdU32 = [&](uint32_t Off) -> uint32_t {
			return (uint32_t)BC[Off] |
				((uint32_t)BC[Off + 1] << 8) |
				((uint32_t)BC[Off + 2] << 16) |
				((uint32_t)BC[Off + 3] << 24);
			};

		auto chkTarget = [&](uint32_t IP, uint32_t RawTgt, const char* Which) -> bool {
			uint32_t Tgt = RawTgt ^ TgtKey;   // P3-B un-blind (TgtKey=0 when off)
			if (Tgt >= BC.size())
				return fail(IP, Twine(Which) + " target " + Twine(Tgt) + " out of bounds (bc=" + Twine(BC.size()) + ")");
			if (!BlockStarts.count(Tgt))
				return fail(IP, Twine(Which) + " target " + Twine(Tgt) + " is not a block start");
			return true;
			};


		// shared CALL verifier — dst/args are u16le; fn/nargs remain u8
		auto verifyCall = [&](uint32_t IP, unsigned DstKind) -> bool {
			const bool IsPair = (DstKind == 5);
			const bool HasDst = (DstKind != 0);
			// opc(1) + dst bytes + fn(1) + nargs(1)
			uint32_t DstBytes = IsPair ? 4u : (HasDst ? 2u : 0u);
			uint32_t Hdr = 1u + DstBytes + 2u;
			if (IP + Hdr > BC.size()) return fail(IP, "OP_CALL header truncated");
			uint32_t Off = IP + 1;
			if (IsPair) {
				if (!chk(IP, "preg", rdIdx(Off), E.NPR)) return false; Off += 2;
				if (!chk(IP, "vreg64", rdIdx(Off), E.NVR64)) return false; Off += 2;
			} else if (HasDst) {
				unsigned DstIdx = rdIdx(Off); Off += 2;
				switch (DstKind) {
				case 1: if (!chk(IP, "vreg", DstIdx, E.NVR))    return false; break;
				case 2: if (!chk(IP, "preg", DstIdx, E.NPR))    return false; break;
				case 3: if (!chk(IP, "vreg64", DstIdx, E.NVR64))  return false; break;
				case 4: if (!chk(IP, "freg", DstIdx, E.NFR))    return false; break;
				}
			}
			uint8_t  FnIdx = BC[Off + 0];
			uint8_t  NArgsRaw = BC[Off + 1];
			const bool Ind = (NArgsRaw & 0x80) != 0;
			uint8_t  NArgs = (uint8_t)(NArgsRaw & 0x7F);
			if (FnIdx >= E.CalleeTab.size())
				return fail(IP, Twine("OP_CALL fn index out of range: ") + Twine((unsigned)FnIdx));
			if (NArgs > kVMCallMaxArgs)
				return fail(IP, Twine("OP_CALL nargs too large: ") + Twine((unsigned)NArgs));

			uint32_t Extra = Ind ? 2u : 0u;
			uint32_t Total = Hdr + Extra + 2u * (uint32_t)NArgs;
			if (IP + Total > BC.size())
				return fail(IP, "OP_CALL args truncated");
			uint32_t ArgBase = IP + Hdr;
			if (Ind) {
				if (!chk(IP, "preg", rdIdx(ArgBase), E.NPR)) return false;
				ArgBase += 2;
			}
			for (unsigned i = 0; i < NArgs; ++i) {
				unsigned Idx = rdIdx(ArgBase + 2u * i);
				unsigned MaxSlots = std::max({ (unsigned)E.NVR, (unsigned)E.NVR64,
				(unsigned)E.NPR, (unsigned)E.NFR });
				if (!chk(IP, "arg", Idx, MaxSlots)) return false;
			}
			return true;
			};
		auto callTotal = [&](uint32_t IP, unsigned NumDst) -> uint32_t {
			// NumDst: 0=void, 1=single, 2=pair — each dst is u16
			uint32_t DstBytes = 2u * NumDst;
			uint32_t Hdr = 1u + DstBytes + 2u;
			uint32_t Off = IP + 1 + DstBytes;
			uint8_t  NArgsRaw = BC[Off + 1];
			uint32_t Extra = (NArgsRaw & 0x80) ? 2u : 0u;
			return Hdr + Extra + 2u * (uint32_t)(NArgsRaw & 0x7F);
			};



		uint32_t IP = 0;
		while (IP < BC.size()) {
			uint8_t Phys = BC[IP];
			if (KeyedDispatch) Phys ^= opKeyByteCT(SaltFull, IP);
			if (Phys >= OP_COUNT)
				return fail(IP, Twine("invalid opcode byte ") + Twine((unsigned)Phys));

			VMOp Opc = OpMap.decode(Phys);
			switch (Opc) {
			case OP_LOADI: {
				if (IP + 7 > BC.size()) return fail(IP, "OP_LOADI truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				IP += 7; break;
			}
			case OP_LOADI64: {
				if (IP + 11 > BC.size()) return fail(IP, "OP_LOADI64 truncated");
				if (!chk(IP, "vreg64", rdIdx(IP + 1), E.NVR64)) return false;
				IP += 11; break;
			}
			case OP_MOVR: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_MOVR truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				IP += 5; break;
			}
			case OP_BINOP: {
				if (IP + 8 > BC.size()) return fail(IP, "OP_BINOP truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 5), E.NVR)) return false;
				IP += 8; break;
			}
			case OP_MULADD: {
				if (IP + 9 > BC.size()) return fail(IP, "OP_MULADD truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 5), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 7), E.NVR)) return false;
				IP += 9; break;
			}
			case OP_SHLADD: {
				if (IP + 9 > BC.size()) return fail(IP, "OP_SHLADD truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 5), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 7), E.NVR)) return false;
				IP += 9; break;
			}
			case OP_CMPSEL: {
				if (IP + 12 > BC.size()) return fail(IP, "OP_CMPSEL truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 5), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 8), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 10), E.NVR)) return false;
				IP += 12; break;
			}
			case OP_ANDCMPZ: {
				if (IP + 8 > BC.size()) return fail(IP, "OP_ANDCMPZ truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 5), E.NVR)) return false;
				IP += 8; break;
			}
			case OP_ICMP: {
				if (IP + 8 > BC.size()) return fail(IP, "OP_ICMP truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 5), E.NVR)) return false;
				IP += 8; break;
			}
			case OP_ICMP64: {
				if (IP + 8 > BC.size()) return fail(IP, "OP_ICMP64 truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "vreg64", rdIdx(IP + 3), E.NVR64)) return false;
				if (!chk(IP, "vreg64", rdIdx(IP + 5), E.NVR64)) return false;
				IP += 8; break;
			}
			case OP_ICMP_PTR: {
				if (IP + 8 > BC.size()) return fail(IP, "OP_ICMP_PTR truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 5), E.NPR)) return false;
				IP += 8; break;
			}
			case OP_CAST: {
				if (IP + 6 > BC.size()) return fail(IP, "OP_CAST truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				IP += 6; break;
			}
			case OP_CAST64: {
				if (IP + 6 > BC.size()) return fail(IP, "OP_CAST64 truncated");
				unsigned Kind = (unsigned)BC[IP + 5];
				if (Kind <= (unsigned)C64_SEXT32) {
					if (!chk(IP, "vreg64", rdIdx(IP + 1), E.NVR64)) return false;
					if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				} else if (Kind >= (unsigned)C64_TRUNC1 && Kind <= (unsigned)C64_TRUNC32) {
					if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
					if (!chk(IP, "vreg64", rdIdx(IP + 3), E.NVR64)) return false;
				} else {
					return fail(IP, Twine("OP_CAST64 invalid kind ") + Twine(Kind));
				}
				IP += 6; break;
			}
			case OP_PTRTOINT: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_PTRTOINT truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				IP += 5; break;
			}
			case OP_PTRTOINT64: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_PTRTOINT64 truncated");
				if (!chk(IP, "vreg64", rdIdx(IP + 1), E.NVR64)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				IP += 5; break;
			}
			case OP_INTTOPTR: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_INTTOPTR truncated");
				if (!chk(IP, "preg", rdIdx(IP + 1), E.NPR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				IP += 5; break;
			}
			case OP_INTTOPTR64: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_INTTOPTR64 truncated");
				if (!chk(IP, "preg", rdIdx(IP + 1), E.NPR)) return false;
				if (!chk(IP, "vreg64", rdIdx(IP + 3), E.NVR64)) return false;
				IP += 5; break;
			}
			case OP_LOAD32: case OP_LOAD8: case OP_LOAD16: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_LOAD* truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				IP += 5; break;
			}
			case OP_LOAD64: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_LOAD64 truncated");
				if (!chk(IP, "vreg64", rdIdx(IP + 1), E.NVR64)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				IP += 5; break;
			}
			case OP_STORE32: case OP_STORE8: case OP_STORE16: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_STORE* truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				IP += 5; break;
			}
			case OP_STORE64: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_STORE64 truncated");
				if (!chk(IP, "vreg64", rdIdx(IP + 1), E.NVR64)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				IP += 5; break;
			}
			case OP_LOADPTR: case OP_STOREPTR: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_*PTR truncated");
				if (!chk(IP, "preg", rdIdx(IP + 1), E.NPR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				IP += 5; break;
			}
			case OP_GEP: {
				if (IP + 9 > BC.size()) return fail(IP, "OP_GEP truncated");
				if (!chk(IP, "preg", rdIdx(IP + 1), E.NPR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 5), E.NVR)) return false;
				IP += 9; break;
			}
			case OP_GEP64: {
				if (IP + 9 > BC.size()) return fail(IP, "OP_GEP64 truncated");
				if (!chk(IP, "preg", rdIdx(IP + 1), E.NPR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				if (!chk(IP, "vreg64", rdIdx(IP + 5), E.NVR64)) return false;
				IP += 9; break;
			}
			case OP_JMP: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_JMP truncated");
				if (!chkTarget(IP, rdU32(IP + 1), "OP_JMP")) return false;
				IP += 5; break;
			}
			case OP_JMPC: {
				if (IP + 11 > BC.size()) return fail(IP, "OP_JMPC truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chkTarget(IP, rdU32(IP + 3), "OP_JMPC.true")) return false;
				if (!chkTarget(IP, rdU32(IP + 7), "OP_JMPC.false")) return false;
				IP += 11; break;
			}
			case OP_RET_VOID: { IP += 1; break; }
			case OP_RET_INT: {
				if (IP + 3 > BC.size()) return fail(IP, "OP_RET_INT truncated");
				unsigned RetLim = E.NVR > E.NVR64 ? E.NVR : E.NVR64;
				if (!chk(IP, "vreg/vreg64", rdIdx(IP + 1), RetLim)) return false;
				IP += 3; break;
			}
			case OP_RET_PTR: {
				if (IP + 3 > BC.size()) return fail(IP, "OP_RET_PTR truncated");
				if (!chk(IP, "preg", rdIdx(IP + 1), E.NPR)) return false;
				IP += 3; break;
			}
			case OP_CALL_VOID: {
				if (!verifyCall(IP, 0)) return false;
				IP += callTotal(IP, 0); break;
			}
			case OP_CALL_INT: {
				if (!verifyCall(IP, 1)) return false;
				IP += callTotal(IP, 1); break;
			}
			case OP_CALL_PTR: {
				if (!verifyCall(IP, 2)) return false;
				IP += callTotal(IP, 1); break;
			}
			case OP_CALL_INT64: {
				if (!verifyCall(IP, 3)) return false;
				IP += callTotal(IP, 1); break;
			}
			case OP_CALL_F: {
				if (!verifyCall(IP, 4)) return false;
				IP += callTotal(IP, 1); break;
			}
			case OP_CALL_PAIR: {
				if (!verifyCall(IP, 5)) return false;
				IP += callTotal(IP, 2); break;
			}
			case OP_SELECT: {
				if (IP + 10 > BC.size()) return fail(IP, "OP_SELECT truncated");
				uint8_t Kind = BC[IP + 1];
				if (!chk(IP, "vreg", rdIdx(IP + 4), E.NVR)) return false; // cond
				if (Kind == 0) {
					if (!chk(IP, "vreg", rdIdx(IP + 2), E.NVR)) return false;
					if (!chk(IP, "vreg", rdIdx(IP + 6), E.NVR)) return false;
					if (!chk(IP, "vreg", rdIdx(IP + 8), E.NVR)) return false;
				} else if (Kind == 1) {
					if (!chk(IP, "preg", rdIdx(IP + 2), E.NPR)) return false;
					if (!chk(IP, "preg", rdIdx(IP + 6), E.NPR)) return false;
					if (!chk(IP, "preg", rdIdx(IP + 8), E.NPR)) return false;
				} else if (Kind == 2) {
					if (!chk(IP, "vreg64", rdIdx(IP + 2), E.NVR64)) return false;
					if (!chk(IP, "vreg64", rdIdx(IP + 6), E.NVR64)) return false;
					if (!chk(IP, "vreg64", rdIdx(IP + 8), E.NVR64)) return false;
				} else {
					return fail(IP, Twine("OP_SELECT invalid kind ") + Twine((unsigned)Kind));
				}
				IP += 10; break;
			}
			case OP_BINOP64: {
				if (IP + 8 > BC.size()) return fail(IP, "OP_BINOP64 truncated");
				if (!chk(IP, "vreg64", rdIdx(IP + 1), E.NVR64)) return false;
				if (!chk(IP, "vreg64", rdIdx(IP + 3), E.NVR64)) return false;
				if (!chk(IP, "vreg64", rdIdx(IP + 5), E.NVR64)) return false;
				IP += 8; break;
			}
			case OP_SWITCH: {
				if (IP + 9 > BC.size()) return fail(IP, "OP_SWITCH header truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				uint16_t NC = rdU16(IP + 3);
				uint32_t Def = rdU32(IP + 5);
				uint32_t Sz = 9u + (uint32_t)NC * 8u;
				if (IP + Sz > BC.size()) return fail(IP, "OP_SWITCH cases truncated");
				if (!chkTarget(IP, Def, "OP_SWITCH.default")) return false;
				uint32_t COff = IP + 9;
				for (unsigned i = 0; i < NC; ++i) {
					(void)rdU32(COff + 0);
					if (!chkTarget(IP, rdU32(COff + 4), "OP_SWITCH.case")) return false;
					COff += 8;
				}
				IP += Sz; break;
			}
			case OP_LOADI_F: {
				if (IP + 11 > BC.size()) return fail(IP, "OP_LOADI_F truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				IP += 11; break;
			}
			case OP_MOVR_F: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_MOVR_F truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 3), E.NFR)) return false;
				IP += 5; break;
			}
			case OP_BINOP_F: {
				if (IP + 8 > BC.size()) return fail(IP, "OP_BINOP_F truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 3), E.NFR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 5), E.NFR)) return false;
				{
					uint8_t Sub = BC[IP + 7] & ~(uint8_t)FBS_F32_FLAG;
					if (Sub > (uint8_t)FBS_FREM)
						return fail(IP, Twine("OP_BINOP_F invalid subop: ") + Twine((unsigned)Sub));
				}
				IP += 8; break;
			}
			case OP_FCMP: {
				if (IP + 8 > BC.size()) return fail(IP, "OP_FCMP truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 3), E.NFR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 5), E.NFR)) return false;
				IP += 8; break;
			}
			case OP_FCAST_FF: {
				if (IP + 6 > BC.size()) return fail(IP, "OP_FCAST_FF truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 3), E.NFR)) return false;
				{ unsigned K = BC[IP + 5];
				  if (K != FK_FPEXT && K != FK_FPTRUNC)
					return fail(IP, Twine("OP_FCAST_FF invalid kind ") + Twine(K)); }
				IP += 6; break;
			}
			case OP_FCAST_FV: {
				if (IP + 6 > BC.size()) return fail(IP, "OP_FCAST_FV truncated");
				if (!chk(IP, "vreg", rdIdx(IP + 1), E.NVR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 3), E.NFR)) return false;
				{ unsigned K = BC[IP + 5];
				  if (K != FK_FPTOSI && K != FK_FPTOUI)
					return fail(IP, Twine("OP_FCAST_FV invalid kind ") + Twine(K)); }
				IP += 6; break;
			}
			case OP_FCAST_FV64: {
				if (IP + 6 > BC.size()) return fail(IP, "OP_FCAST_FV64 truncated");
				if (!chk(IP, "vreg64", rdIdx(IP + 1), E.NVR64)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 3), E.NFR)) return false;
				{ unsigned K = BC[IP + 5];
				  if (K != FK_FPTOSI64 && K != FK_FPTOUI64)
					return fail(IP, Twine("OP_FCAST_FV64 invalid kind ") + Twine(K)); }
				IP += 6; break;
			}
			case OP_FCAST_VF: {
				if (IP + 6 > BC.size()) return fail(IP, "OP_FCAST_VF truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				{ unsigned K = BC[IP + 5] & 0x7Fu;
				  if (K != FK_SITOFP && K != FK_UITOFP)
					return fail(IP, Twine("OP_FCAST_VF invalid kind ") + Twine(K)); }
				IP += 6; break;
			}
			case OP_FCAST_V64F: {
				if (IP + 6 > BC.size()) return fail(IP, "OP_FCAST_V64F truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				if (!chk(IP, "vreg64", rdIdx(IP + 3), E.NVR64)) return false;
				{ unsigned K = BC[IP + 5] & 0x7Fu;
				  if (K != FK_SI64TOFP && K != FK_UI64TOFP)
					return fail(IP, Twine("OP_FCAST_V64F invalid kind ") + Twine(K)); }
				IP += 6; break;
			}
			case OP_LOAD_F: case OP_LOAD_F32: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_LOAD_F* truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				IP += 5; break;
			}
			case OP_STORE_F: case OP_STORE_F32: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_STORE_F* truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				if (!chk(IP, "preg", rdIdx(IP + 3), E.NPR)) return false;
				IP += 5; break;
			}
			case OP_RET_F: {
				if (IP + 3 > BC.size()) return fail(IP, "OP_RET_F truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				IP += 3; break;
			}
			case OP_SELECT_F: {
				if (IP + 9 > BC.size()) return fail(IP, "OP_SELECT_F truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				if (!chk(IP, "vreg", rdIdx(IP + 3), E.NVR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 5), E.NFR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 7), E.NFR)) return false;
				IP += 9; break;
			}
			case OP_FNEG: {
				if (IP + 5 > BC.size()) return fail(IP, "OP_FNEG truncated");
				if (!chk(IP, "freg", rdIdx(IP + 1), E.NFR)) return false;
				if (!chk(IP, "freg", rdIdx(IP + 3), E.NFR)) return false;
				IP += 5; break;
			}
			default: {
				return fail(IP, Twine("unhandled opcode in verifier: phys=") + Twine((unsigned)Phys) + " logical=" + Twine((unsigned)Opc));
			}
			}
		}

		if (!BlockStarts.count(0))
			return fail(0, "missing block start at IP=0");

		return true;
	}

} // namespace llvm