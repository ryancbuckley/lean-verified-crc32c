#!/bin/bash
# Checks the C++ wrapper's trust assumptions by test: builds the library and
# runs the guard-page test and the in-process differential test against
# abseil, with the hardware path on and off.
# Usage: scripts/check_capi.sh [differential-iterations]
set -euo pipefail
cd "$(dirname "$0")/.."
ITERS="${1:-200000}"
ABSL="${ABSEIL:-$HOME/programming/temp/abseil-cpp}"
[ -f build/absl/libabslcrc.a ] || tests/build_absl.sh "$ABSL"
cxx/build.sh >/dev/null
FLAGS="-std=c++17 -O2 -I$ABSL -Icxx build/absl/libabslcrc.a $(cat build/cxx/LINK_FLAGS)"
for t in test_guard test_diff; do
  clang++ cxx/$t.cc $FLAGS -o build/cxx/$t 2> >(grep -v "newer 'macOS'" >&2)
done
build/cxx/test_guard
SIMDMODELS_DISABLE_HW=1 build/cxx/test_guard
build/cxx/test_diff "$ITERS" 1
SIMDMODELS_DISABLE_HW=1 build/cxx/test_diff "$ITERS" 2
