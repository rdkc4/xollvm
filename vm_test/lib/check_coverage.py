#!/usr/bin/env python3
"""Prove every VM opcode + required odd-int widths are covered by the suite.

Reads:
  - include/llvm/Transforms/Obfuscator/VMPass_ISA.h  → OP_* inventory
  - categories/COVERAGE.json                          → emitted by gen_tests.py

Exit 0 only when every required opcode and odd width is claimed by ≥1 test.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Handlers exist but the emitter never emits these — document-only.
DEAD_OPS = frozenset({"OP_MOVR", "OP_MOVR_F"})

# Non-opcode markers in the enum that are not instructions.
SKIP_ENUM = frozenset({"OP_COUNT", "OP_DECOY_BASE", "OP_COUNT_TOTAL"})

# Odd widths that must have dedicated legalize coverage (docs/VM.md).
REQUIRED_ODD_WIDTHS = frozenset({40, 56, 88, 104})

# Legalize / shell patterns that are not OP_* but still required.
REQUIRED_PATTERNS = frozenset({
    "LEGALIZE_MEM_EXPAND",
    "LEGALIZE_SWITCH_NON_I32",
    "LEGALIZE_AGG_LOAD",
    "LEGALIZE_PHI_DEMOTE",
    "LEGALIZE_ODD_SSA",       # ≤64 leftover (i40/i56)
    "LEGALIZE_ODD_BITFIELD",  # extract/deposit on wide containers (i88/i104)
    "SHELL_VARARGS",
    "SHELL_SRET",
    "SHELL_NAT",
})


def parse_opcodes(isa_h: Path) -> list[str]:
    text = isa_h.read_text(encoding="utf-8", errors="replace")
    # Match OP_FOO = 0xNN inside enum VMOp
    ops = re.findall(r"\b(OP_[A-Z0-9_]+)\s*=\s*0x[0-9A-Fa-f]+", text)
    # Preserve order, unique
    seen: set[str] = set()
    out: list[str] = []
    for op in ops:
        if op in SKIP_ENUM or op in seen:
            continue
        seen.add(op)
        out.append(op)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--isa", type=Path, required=True, help="VMPass_ISA.h path")
    ap.add_argument("--coverage", type=Path, required=True, help="COVERAGE.json")
    ap.add_argument("--list", action="store_true", help="Print matrix and exit 0")
    args = ap.parse_args()

    ops = parse_opcodes(args.isa)
    required_ops = [o for o in ops if o not in DEAD_OPS]

    cov = json.loads(args.coverage.read_text(encoding="utf-8"))
    by_op: dict[str, list[str]] = cov.get("opcodes", {})
    by_pat: dict[str, list[str]] = cov.get("patterns", {})
    by_odd: dict[str, list[str]] = {
        str(k): v for k, v in cov.get("odd_widths", {}).items()
    }

    if args.list:
        print(f"ISA opcodes: {len(ops)} (required {len(required_ops)}, dead {sorted(DEAD_OPS)})")
        for op in ops:
            tests = by_op.get(op, [])
            tag = "DEAD" if op in DEAD_OPS else ("OK" if tests else "MISSING")
            print(f"  [{tag:7}] {op:20} → {tests or '-'}")
        print("Patterns:")
        for p in sorted(REQUIRED_PATTERNS):
            print(f"  {p:28} → {by_pat.get(p, []) or '-'}")
        print("Odd widths:")
        for w in sorted(REQUIRED_ODD_WIDTHS):
            print(f"  i{w: <4} → {by_odd.get(str(w), []) or '-'}")
        return 0

    errors: list[str] = []

    for op in required_ops:
        tests = by_op.get(op, [])
        if not tests:
            errors.append(f"opcode uncovered: {op}")

    for op in DEAD_OPS:
        if op not in ops:
            errors.append(f"dead opcode {op} not found in ISA.h")
        # Must be explicitly listed as dead in coverage file
        if op not in cov.get("dead_opcodes", []):
            errors.append(f"dead opcode {op} not declared in COVERAGE.json dead_opcodes")

    for pat in sorted(REQUIRED_PATTERNS):
        if not by_pat.get(pat):
            errors.append(f"pattern uncovered: {pat}")

    for w in sorted(REQUIRED_ODD_WIDTHS):
        if not by_odd.get(str(w)):
            errors.append(f"odd-int width uncovered: i{w}")

    # Sanity: every claimed test file should exist next to COVERAGE.json
    cat = args.coverage.parent
    claimed_tests: set[str] = set()
    for m in (by_op, by_pat, by_odd):
        for tests in m.values():
            claimed_tests.update(tests)
    for t in sorted(claimed_tests):
        # t like "08_legalize/test_odd_i40"
        c = cat / f"{t}.c"
        ll = cat / f"{t}.ll"
        if not c.exists() and not ll.exists():
            errors.append(f"coverage claims missing source: {t}.{{c,ll}}")

    if errors:
        print("COVERAGE FAIL:", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        print(
            f"summary: {len(required_ops)} required opcodes, "
            f"{len(REQUIRED_ODD_WIDTHS)} odd widths, "
            f"{len(REQUIRED_PATTERNS)} patterns; "
            f"{len(errors)} gap(s)",
            file=sys.stderr,
        )
        return 1

    print(
        f"COVERAGE OK: {len(required_ops)} opcodes + "
        f"{len(REQUIRED_ODD_WIDTHS)} odd widths + "
        f"{len(REQUIRED_PATTERNS)} patterns"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
