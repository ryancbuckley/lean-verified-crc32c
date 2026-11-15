#!/bin/bash
# Builds build/cxx/libleanmemcpy.a from the Lean-generated C modules plus the
# C/C++ wrapper. Compiles the generated C directly so c/simd_shim.h changes are
# always picked up and x86-64 hardware kernel TUs receive -msse4.2 -mpclmul (so
# the CRC32 and PCLMULQDQ intrinsics inline into the kernel loops without
# emitting SSE4 instructions into portable or module-init paths).
#
# Link users with: $(cat build/cxx/LINK_FLAGS)
set -euo pipefail
cd "$(dirname "$0")/.."
CC="${CC:-clang}"
CXX="${CXX:-clang++}"
CFLAGS_EXTRA="${CFLAGS_EXTRA:--DNDEBUG}"
PREFIX="$(lean --print-prefix)"
OUT="${OUT:-build/cxx}"
mkdir -p "$OUT"

lake build +MemcpyCrc32c.Impl.CApi:c.o.export +SimdModels.Trusted:c.o.export >/dev/null

HW_ISA_FLAGS=""
HWCOMBINE_ISA_FLAGS=""
if "$CC" $CFLAGS_EXTRA -dM -E - </dev/null | grep -q '__x86_64__'; then
  HW_ISA_FLAGS="-msse4.2 -mpclmul"
  HWCOMBINE_ISA_FLAGS="-msse4.2 -mpclmul -fno-vectorize -fno-slp-vectorize"
fi

OBJS=()
compile_c() { # $1 = generated C file, $2 = extra ISA flags
  local o="$OUT/$(echo "$1" | tr '/' '_').o"
  "$CC" -O2 $CFLAGS_EXTRA ${2:-} -I"$PREFIX/include" \
    -include lean-simd-models/c/simd_shim.h -c "$1" -o "$o" \
    2> >(grep -v "newer 'macOS'" >&2 || true)
  OBJS+=("$o")
}

for m in Reference Arith Portable Memcpy Dispatch CApi; do
  compile_c ".lake/build/ir/MemcpyCrc32c/Impl/$m.c" ""
done
compile_c ".lake/build/ir/MemcpyCrc32c/Impl/HwCombine.c" "$HWCOMBINE_ISA_FLAGS"
compile_c ".lake/build/ir/MemcpyCrc32c/Impl/Hw.c" "$HW_ISA_FLAGS"
for m in Models Trusted; do
  compile_c "lean-simd-models/.lake/build/ir/SimdModels/$m.c" ""
done

"$CXX" -std=c++17 -O3 -fno-exceptions -fno-rtti $CFLAGS_EXTRA -I"$PREFIX/include" -Icxx \
  -c cxx/leanmemcpy.cc -o "$OUT/leanmemcpy.o" \
  2> >(grep -v "newer 'macOS'" >&2 || true)
rm -f "$OUT/libleanmemcpy.a"
ar rcs "$OUT/libleanmemcpy.a" "$OUT/leanmemcpy.o" "${OBJS[@]}"
echo "$PWD/$OUT/libleanmemcpy.a -L$PREFIX/lib/lean -lleanshared -lInit_shared -Wl,-rpath,$PREFIX/lib/lean" > "$OUT/LINK_FLAGS"
echo "built $OUT/libleanmemcpy.a"
