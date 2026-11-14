#!/usr/bin/env python3
"""Apply expect.json IR gates to an obfuscated LLVM IR file."""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


def load_expect(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SystemExit(f"expect file must be a JSON object: {path}")
    return data


def check(ir: str, expect: dict) -> list[str]:
    errors: list[str] = []

    for pat in expect.get("must_match", []):
        if not re.search(pat, ir):
            errors.append(f"must_match failed: /{pat}/")

    for group in expect.get("must_match_any", []):
        if isinstance(group, str):
            group = [group]
        if not any(re.search(p, ir) for p in group):
            errors.append(f"must_match_any failed: {group}")

    for pat in expect.get("must_not_match", []):
        if re.search(pat, ir):
            errors.append(f"must_not_match hit: /{pat}/")

    return errors


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("obf_ll", type=Path, help="Path to obfuscated .ll")
    ap.add_argument("expect_json", type=Path, help="Path to expect.json")
    args = ap.parse_args()

    ir = args.obf_ll.read_text(encoding="utf-8", errors="replace")
    expect = load_expect(args.expect_json)
    errs = check(ir, expect)
    if errs:
        print(f"TRANSFORM FAIL ({args.obf_ll}):", file=sys.stderr)
        for e in errs:
            print(f"  - {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
