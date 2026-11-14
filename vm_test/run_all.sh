#!/usr/bin/env bash
# Run the VM ISA correctness suite (coverage proof + transform + runtime).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=lib/common.sh
source "$ROOT/lib/common.sh"

BUILD_DIR=""
CATEGORY_FILTER=""
KEEP=0
VERBOSE=0
SEED=1
SKIP_GEN=0

usage() {
  cat <<EOF
Usage: $0 [--build-dir DIR] [--category N|name] [--seed N] [--keep] [--skip-gen] [-v]

  XOLLVM_BUILD     Required env var: xollvm install prefix (bin/clang, bin/opt)
                   unless --build-dir is passed.

  --build-dir DIR  Override XOLLVM_BUILD for this run
  --category FILTER Substring match on category dir name
  --seed N         Obfuscation seed (default: 1)
  --keep           Keep per-test workdirs under vm_test/.work/
  --skip-gen       Do not regenerate categories/ (use existing)
  -v               Verbose toolchain commands
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --build-dir) BUILD_DIR="$2"; shift 2 ;;
    --category) CATEGORY_FILTER="$2"; shift 2 ;;
    --seed) SEED="$2"; shift 2 ;;
    --keep) KEEP=1; shift ;;
    --skip-gen) SKIP_GEN=1; shift ;;
    -v|--verbose) VERBOSE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown arg: $1" >&2; usage; exit 2 ;;
  esac
done

BUILD_DIR="$(detect_build_dir "$BUILD_DIR")"
require_tools "$BUILD_DIR"

REPO_ROOT="$(cd "$ROOT/.." && pwd)"
ISA_H="$REPO_ROOT/include/llvm/Transforms/Obfuscator/VMPass_ISA.h"

if [[ "$SKIP_GEN" -eq 0 ]]; then
  echo "generating categories/ …"
  python3 "$ROOT/lib/gen_tests.py"
fi

if [[ ! -f "$ROOT/categories/COVERAGE.json" ]]; then
  echo "error: missing $ROOT/categories/COVERAGE.json — run without --skip-gen" >&2
  exit 1
fi

echo "checking ISA coverage …"
python3 "$ROOT/lib/check_coverage.py" --isa "$ISA_H" --coverage "$ROOT/categories/COVERAGE.json"

WORK_ROOT="$ROOT/.work"
mkdir -p "$WORK_ROOT"

PASS=0
FAIL=0
SKIP=0

log() { echo "$*"; }
vlog() { [[ "$VERBOSE" -eq 1 ]] && echo "+ $*" >&2 || true; }

run_one() {
  local src="$1"
  local cat_dir expect work base_ll obf_ll base_exe obf_exe name stem

  cat_dir="$(dirname "$src")"
  name="$(basename "$src")"
  stem="${name%.*}"
  work="$WORK_ROOT/$(basename "$cat_dir")/$stem"
  rm -rf "$work"
  mkdir -p "$work"

  if [[ -f "$cat_dir/$stem.expect.json" ]]; then
    expect="$cat_dir/$stem.expect.json"
  elif [[ -f "$cat_dir/expect.json" ]]; then
    expect="$cat_dir/expect.json"
  else
    expect=""
  fi

  base_ll="$work/base.ll"
  obf_ll="$work/obf.ll"
  base_exe="$work/base.exe"
  obf_exe="$work/obf.exe"

  if [[ "$src" == *.c ]]; then
    vlog "compile $src"
    compile_c_to_ll "$src" "$base_ll"
  elif [[ "$src" == *.ll ]]; then
    cp "$src" "$base_ll"
  else
    echo "SKIP unknown source: $src"
    SKIP=$((SKIP + 1))
    return 0
  fi

  vlog "obfuscate seed=$SEED"
  if ! obfuscate_ll "$base_ll" "$obf_ll" "$SEED"; then
    echo "FAIL  $src  (opt -obf-verify failed)"
    FAIL=$((FAIL + 1))
    return 0
  fi

  if [[ -n "$expect" ]]; then
    vlog "transform gates $expect"
    if ! python3 "$ROOT/lib/check_transform.py" "$obf_ll" "$expect"; then
      echo "FAIL  $src  (transform gates)"
      FAIL=$((FAIL + 1))
      return 0
    fi
  fi

  vlog "link base+obf"
  compile_ll_to_exe "$base_ll" "$base_exe"
  compile_ll_to_exe "$obf_ll" "$obf_exe"

  if ! run_compare "$base_exe" "$obf_exe" "${DEFAULT_INPUTS[@]}"; then
    echo "FAIL  $src  (runtime)"
    FAIL=$((FAIL + 1))
    return 0
  fi

  echo "PASS  $src"
  PASS=$((PASS + 1))
  if [[ "$KEEP" -eq 0 ]]; then
    rm -rf "$work"
  fi
}

log "vm_test: build-dir=$BUILD_DIR seed=$SEED"
log "----------------------------------------"

shopt -s nullglob
for cat in "$ROOT"/categories/*/; do
  cat_name="$(basename "$cat")"
  if [[ -n "$CATEGORY_FILTER" && "$cat_name" != *"$CATEGORY_FILTER"* ]]; then
    continue
  fi
  log "[$cat_name]"
  for src in "${cat}test_"*.c "${cat}test_"*.ll; do
    [[ -e "$src" ]] || continue
    run_one "$src"
  done
done

log "----------------------------------------"
log "PASS=$PASS FAIL=$FAIL SKIP=$SKIP"
[[ "$FAIL" -eq 0 ]]
