#!/bin/bash
# Builds build/fuzz/fuzz: the libFuzzer target with the Lean-generated C, the
# instruction shim and the C++ wrapper all compiled under AddressSanitizer and
# UndefinedBehaviorSanitizer. Needs an LLVM with libFuzzer (Homebrew llvm@17).
set -euo pipefail
cd "$(dirname "$0")/.."
LLVM="${LLVM:-/opt/homebrew/opt/llvm@17}"
ABSL="${ABSEIL:-$HOME/programming/temp/abseil-cpp}"
PREFIX="$(lean --print-prefix)"
OUT=build/fuzz
mkdir -p "$OUT"
lake build +MemcpyCrc32c.Impl.CApi:c.o.export +SimdModels.Trusted:c.o.export >/dev/null
[ -f build/absl/libabslcrc.a ] || tests/build_absl.sh "$ABSL"
SDK="$(xcrun --show-sdk-path 2>/dev/null || true)"
[ -n "$SDK" ] && SYSROOT="-isysroot $SDK" || SYSROOT=""
SAN="$SYSROOT -fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer -g"
OBJS=()
compile_c() { # $1 = generated C file
  local o="$OUT/$(echo "$1" | tr '/' '_').o"
  "$LLVM/bin/clang" -O2 -DNDEBUG $SAN -fsanitize=fuzzer-no-link -I"$PREFIX/include" \
    -include lean-simd-models/c/simd_shim.h -c "$1" -o "$o"
  OBJS+=("$o")
}
for m in Reference Arith Portable HwCombine Hw Memcpy Dispatch CApi; do
  compile_c ".lake/build/ir/MemcpyCrc32c/Impl/$m.c"
done
for m in Models Trusted; do
  compile_c "lean-simd-models/.lake/build/ir/SimdModels/$m.c"
done
"$LLVM/bin/clang++" -std=c++17 -O2 $SAN -fsanitize=fuzzer -I"$PREFIX/include" -I"$ABSL" -Icxx \
  cxx/fuzz.cc cxx/leanmemcpy.cc "${OBJS[@]}" build/absl/libabslcrc.a \
  -L"$LLVM/lib/c++" -Wl,-rpath,"$LLVM/lib/c++" ${SDK:+-Wl,-syslibroot,"$SDK"} -L"$PREFIX/lib/lean" -lleanshared -lInit_shared -Wl,-rpath,"$PREFIX/lib/lean" -o "$OUT/fuzz"
echo "built $OUT/fuzz"
