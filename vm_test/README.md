# VM ISA Correctness Suite (`vm_test/`)

Focused regression suite for xOLLVM **code virtualisation**: every VM opcode and
legalize/shell path must survive both the **transform** (bytecode emission +
`-obf-verify` + IR gates) and **runtime** (baseline vs obfuscated differential
execution).

Hardening matrix (AES, nestedVM, …) stays under `utils/obf_runtime_tests.py`.

## Prerequisites

```bash
export XOLLVM_BUILD=/path/to/xollvm-install   # must contain bin/clang and bin/opt
```

`categories/` is **generated** and gitignored. `run_all.sh` regenerates it each run.

## Quick start

```bash
export XOLLVM_BUILD=/path/to/xollvm-install
./vm_test/run_all.sh
./vm_test/run_all.sh --build-dir "$XOLLVM_BUILD" --category legalize -v --keep
./vm_test/run_all.sh --category odd   # substring filter
```

Coverage-only (no exec):

```bash
python3 vm_test/lib/gen_tests.py
python3 vm_test/lib/check_coverage.py \
  --isa include/llvm/Transforms/Obfuscator/VMPass_ISA.h \
  --coverage vm_test/categories/COVERAGE.json
python3 vm_test/lib/check_coverage.py --isa … --coverage … --list
```

## Dual-phase verification

| Phase | Check |
|---|---|
| **Coverage** | `check_coverage.py` vs `VMPass_ISA.h` - every live `OP_*`, required odd widths, legalize/shell patterns mapped to =>1 test |
| **Transform** | `opt -passes=obfuscation -obf-verify`; per-test `*.expect.json` IR gates |
| **Runtime** | Compile base+obf; identical exit + stdout on fixed `(x,y)` vectors |

## Layout

```
vm_test/
  README.md
  run_all.sh
  lib/
    common.sh            # requires XOLLVM_BUILD or --build-dir
    gen_tests.py         # writes categories/ + COVERAGE.json
    check_coverage.py    # proves full OP_* / odd-int coverage
    check_transform.py   # per-test IR gates
  categories/            # GENERATED - gitignored
  .work/                 # GENERATED - gitignored
```

## Opcode inventory -> categories

Source: `include/llvm/Transforms/Obfuscator/VMPass_ISA.h` (`OP_COUNT = 0x3B`).

| Category | Coverage |
|---|---|
| `01_int32` | `OP_LOADI`, `OP_BINOP` (all BinSubop), `OP_CAST`, `OP_ICMP`, `OP_SELECT` k0, `OP_RET_INT` |
| `02_int64` | `OP_LOADI64`, `OP_BINOP64`, `OP_CAST64`, `OP_ICMP64`, `OP_SELECT` k2 |
| `03_control` | `OP_JMP`, `OP_JMPC`, `OP_SWITCH`, `OP_RET_VOID` |
| `04_memory` | LOAD/STORE 8/16/32/64/ptr, `OP_GEP`, `OP_GEP64`, i1 mem |
| `05_float` | float ALU/cast/mem/select/ret including f32 globals |
| `06_ptr` | ptr↔int 32/64, `OP_ICMP_PTR`, `OP_RET_PTR` |
| `07_calls` | CALL_VOID/INT/PTR/INT64/F/PAIR + narrow |
| `08_legalize` | mem expand, switch i16, agg load, PHI, **odd-int i3/i5/i40/i56/i88/i104** |
| `09_shells` | varargs split, sret, `__vm_nat.*` |
| `10_superops` | `OP_MULADD` / `SHLADD` / `CMPSEL` / `ANDCMPZ` (`superOps=1`) |

### Odd-int widths (required - proven by `check_coverage.py`)

| Width | Path | Test |
|---|---|---|
| i3, i5 | <=64 SSA promote | `test_odd_i3_i5.ll` |
| i40, i56 | bitfield **and** general Pass-3 SSA (all binops + icmp/select/mem) | `test_odd_i40_bitfield.ll`, `test_odd_i40_ssa.ll`, … |
| i88, i104 | bitfield extract+deposit only (`__vm_il_*`; >64 arith not in i64 file) | `test_odd_i88_bitfield.ll`, `test_odd_i104_bitfield.ll` |
| C bitfields | extract/deposit | `test_odd_bitfield.c` |

`check_coverage.py` parses `VMPass_ISA.h` and fails if any live `OP_*` or required odd width lacks a mapped test.

### Dead ISA slots (documented only)

`OP_MOVR`, `OP_MOVR_F` - handlers exist; emitter never emits. Listed in `COVERAGE.json` -> `dead_opcodes`.

## Adding a test

1. Edit `lib/gen_tests.py` (add `write`/`write_ll` + entry in `build_coverage()`).
2. `python3 vm_test/lib/gen_tests.py && python3 vm_test/lib/check_coverage.py --isa … --coverage vm_test/categories/COVERAGE.json`
3. `./vm_test/run_all.sh --category <cat>`
