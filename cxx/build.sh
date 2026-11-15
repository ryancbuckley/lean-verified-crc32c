#!/bin/bash
# Builds build/cxx/libleanmemcpy.a from the objects Lake compiled for the Lean
# modules plus the C++ wrapper. Run `lake build MemcpyCrc32c` first.
# Link users with:  $(cat build/cxx/LINK_FLAGS)
set -euo pipefail
cd "$(dirname "$0")/.."
PREFIX="$(lean --print-prefix)"
OUT=build/cxx
mkdir -p "$OUT"
lake build +MemcpyCrc32c.Impl.CApi:c.o.export +SimdModels.Trusted:c.o.export >/dev/null
OBJS=()
for m in Reference Arith Portable HwCombine Hw Memcpy Dispatch CApi; do
  OBJS+=(".lake/build/ir/MemcpyCrc32c/Impl/$m.c.o.export")
done
for m in Models Trusted; do
  OBJS+=("lean-simd-models/.lake/build/ir/SimdModels/$m.c.o.export")
done
for o in "${OBJS[@]}"; do [ -f "$o" ] || { echo "missing object $o" >&2; exit 1; }; done
clang++ -std=c++17 -O2 -DNDEBUG -I"$PREFIX/include" -c cxx/leanmemcpy.cc -o "$OUT/leanmemcpy.o"
rm -f "$OUT/libleanmemcpy.a"
ar rcs "$OUT/libleanmemcpy.a" "$OUT/leanmemcpy.o" "${OBJS[@]}"
echo "$PWD/$OUT/libleanmemcpy.a -L$PREFIX/lib/lean -lleanshared -lInit_shared -Wl,-rpath,$PREFIX/lib/lean" > "$OUT/LINK_FLAGS"
echo "built $OUT/libleanmemcpy.a"
