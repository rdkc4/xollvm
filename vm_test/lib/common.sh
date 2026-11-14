#!/usr/bin/env bash
# Shared helpers for vm_test/run_all.sh
set -euo pipefail

vm_test_root() {
  cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd
}

# Resolve install dir: --build-dir wins, else $XOLLVM_BUILD (required).
detect_build_dir() {
  local override="${1:-}"
  if [[ -n "$override" ]]; then
    echo "$override"
    return
  fi
  if [[ -n "${XOLLVM_BUILD:-}" ]]; then
    echo "$XOLLVM_BUILD"
    return
  fi
  echo "error: set XOLLVM_BUILD to the xollvm install prefix (bin/clang + bin/opt)," >&2
  echo "       or pass --build-dir DIR" >&2
  return 1
}

require_tools() {
  local build="$1"
  CLANG="$build/bin/clang"
  OPT="$build/bin/opt"
  if [[ ! -x "$CLANG" ]]; then
    echo "error: clang not found at $CLANG (XOLLVM_BUILD=$build)" >&2
    return 1
  fi
  if [[ ! -x "$OPT" ]]; then
    echo "error: opt not found at $OPT (XOLLVM_BUILD=$build)" >&2
    return 1
  fi
  export CLANG OPT
}

compile_c_to_ll() {
  local src="$1" out="$2"
  "$CLANG" -O0 -Xclang -disable-O0-optnone -fno-discard-value-names \
    -ffp-contract=off -S -emit-llvm "$src" -o "$out"
}

obfuscate_ll() {
  local base="$1" out="$2" seed="${3:-1}"
  "$OPT" -passes=obfuscation -obf-seed="$seed" -obf-verify -S "$base" -o "$out"
}

compile_ll_to_exe() {
  local ll="$1" exe="$2"
  "$CLANG" -O0 -ffp-contract=off "$ll" -o "$exe" -lm
}

run_compare() {
  local base_exe="$1" obf_exe="$2"
  shift 2
  local x y
  local fail=0
  for pair in "$@"; do
    x="${pair%,*}"
    y="${pair#*,}"
    local bo oo be oe
    set +e
    bo="$("$base_exe" "$x" "$y" 2>&1)"
    be=$?
    oo="$("$obf_exe" "$x" "$y" 2>&1)"
    oe=$?
    set -e
    if [[ "$be" -ne "$oe" || "$bo" != "$oo" ]]; then
      echo "  runtime mismatch input=($x,$y)" >&2
      echo "    base exit=$be out=[$bo]" >&2
      echo "    obf  exit=$oe out=[$oo]" >&2
      fail=1
    fi
  done
  return "$fail"
}

DEFAULT_INPUTS=(
  "0,0"
  "1,1"
  "123,456"
  "7,3"
  "255,17"
  "0xDEAD,0xBEEF"
  "100,0"
  "42,99"
)
