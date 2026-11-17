#!/bin/bash
# Builds build/cxx/libleanrs.a: the Reed–Solomon C library (cxx/leanrs.h).
# Link users with: $(cat build/cxx/LINK_FLAGS_RS)
set -euo pipefail
cd "$(dirname "$0")/.."
CC="${CC:-clang}"
CXX="${CXX:-clang++}"
CFLAGS_EXTRA="${CFLAGS_EXTRA:--DNDEBUG}"
PREFIX="$(lean --print-prefix)"
OUT="${OUT:-build/cxx}"
mkdir -p "$OUT/rs"

lake build +ReedSolomon.Impl.Kernel:c.o.export +SimdModels.Trusted:c.o.export >/dev/null

OBJS=()
compile_c() { # $1 = generated C file
  local o="$OUT/rs/$(echo "$1" | tr '/' '_').o"
  "$CC" -O2 $CFLAGS_EXTRA -I"$PREFIX/include" \
    -include lean-simd-models/c/simd_shim.h -c "$1" -o "$o" \
    2> >(grep -v "newer 'macOS'" >&2 || true)
  OBJS+=("$o")
}
for m in Gf Kernel; do compile_c ".lake/build/ir/ReedSolomon/Impl/$m.c"; done
for m in Models Trusted; do compile_c "lean-simd-models/.lake/build/ir/SimdModels/$m.c"; done

# Hand-written AArch64 kernel (empty object on other targets). Its bytes are the
# ones proven in ReedSolomon/Arm64/Apply.lean.
"$CC" -c cxx/leanrs_apply_arm64.S -o "$OUT/leanrs_apply_arm64.o" \
  2> >(grep -v "newer 'macOS'" >&2 || true)
OBJS+=("$OUT/leanrs_apply_arm64.o")

"$CXX" -std=c++17 -O2 -fno-exceptions -fno-rtti $CFLAGS_EXTRA -I"$PREFIX/include" -Icxx \
  -c cxx/leanrs.cc -o "$OUT/rs/leanrs.o" 2> >(grep -v "newer 'macOS'" >&2 || true)
rm -f "$OUT/libleanrs.a"
ar rcs "$OUT/libleanrs.a" "$OUT/rs/leanrs.o" "${OBJS[@]}"
echo "$PWD/$OUT/libleanrs.a -L$PREFIX/lib/lean -lleanshared -lInit_shared -Wl,-rpath,$PREFIX/lib/lean" > "$OUT/LINK_FLAGS_RS"
echo "built $OUT/libleanrs.a"
