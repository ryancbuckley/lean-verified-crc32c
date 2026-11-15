#!/bin/bash
# Builds build/fuzz/fuzz: the libFuzzer target with the Lean-generated C, the
# instruction shim and the C/C++ wrapper all compiled under AddressSanitizer,
# UndefinedBehaviorSanitizer (-fno-sanitize-recover=all), SanitizerCoverage, and
# Lean runtime assertions (no -DNDEBUG).
set -euo pipefail
cd "$(dirname "$0")/.."

if [ -z "${LLVM:-}" ]; then
  for cand in /opt/homebrew/opt/llvm@22 /opt/homebrew/opt/llvm \
              /opt/homebrew/opt/llvm@21 /opt/homebrew/opt/llvm@20 \
              /opt/homebrew/opt/llvm@19 /opt/homebrew/opt/llvm@18 \
              /opt/homebrew/opt/llvm@17; do
    if [ -x "$cand/bin/clang++" ]; then
      LLVM="$cand"
      break
    fi
  done
fi
if [ -z "${LLVM:-}" ] || [ ! -x "$LLVM/bin/clang++" ]; then
  echo "error: set LLVM=/path/to/llvm with libFuzzer + ASan + UBSan" >&2
  exit 1
fi

ABSL="${ABSEIL:-$HOME/programming/temp/abseil-cpp}"
PREFIX="$(lean --print-prefix)"
OUT=build/fuzz
mkdir -p "$OUT/absl_obj"

lake build +MemcpyCrc32c.Impl.CApi:c.o.export +SimdModels.Trusted:c.o.export >/dev/null

SDK="$(xcrun --show-sdk-path 2>/dev/null || true)"
SYSROOT=()
LD_SYSROOT=()
COV_WORKAROUND=()
if [ -n "$SDK" ]; then
  SYSROOT=(-isysroot "$SDK")
  LD_SYSROOT=(-Wl,-syslibroot,"$SDK")
fi
if [ "$(uname -s)" = "Darwin" ]; then
  # Apple /usr/bin/ld rejects local-symbol relocations in __DATA,__sancov_pcs
  # emitted by LLVM 22's pc-table; inline-8bit-counters + trace-cmp remain active.
  COV_WORKAROUND=(-fno-sanitize-coverage=pc-table)
fi

if [ -d "$ABSL" ]; then
  if [ ! -f "$OUT/libabslcrc_fuzz.a" ]; then
    ABSL_SRCS=(
      absl/crc/crc32c.cc
      absl/crc/internal/crc.cc
      absl/crc/internal/crc_x86_arm_combined.cc
      absl/crc/internal/crc_memcpy_fallback.cc
      absl/crc/internal/crc_memcpy_x86_arm_combined.cc
      absl/crc/internal/crc_non_temporal_memcpy.cc
      absl/base/internal/cpu_detect.cc
      absl/base/internal/raw_logging.cc
      absl/base/log_severity.cc
    )
    ABSL_OBJS=()
    for s in "${ABSL_SRCS[@]}"; do
      ao="$OUT/absl_obj/$(echo "$s" | tr '/' '_').o"
      "$LLVM/bin/clang++" -std=c++17 -O2 -DNDEBUG "${SYSROOT[@]}" -I"$ABSL" -c "$ABSL/$s" -o "$ao"
      ABSL_OBJS+=("$ao")
    done
    ar rcs "$OUT/libabslcrc_fuzz.a" "${ABSL_OBJS[@]}"
  fi
  ABSL_CXXFLAGS=(-I"$ABSL")
  ABSL_LDFLAGS=("$OUT/libabslcrc_fuzz.a")
elif pkg-config --exists absl_crc32c 2>/dev/null; then
  read -r -a ABSL_CXXFLAGS <<< "$(pkg-config --cflags absl_crc32c)"
  read -r -a ABSL_LDFLAGS <<< "$(pkg-config --libs absl_crc32c)"
else
  echo "error: Abseil not found at $ABSL and absl_crc32c not in pkg-config" >&2
  exit 1
fi

HW_ISA_FLAGS=()
HWCOMBINE_ISA_FLAGS=()
if "$LLVM/bin/clang" "${SYSROOT[@]}" -dM -E - </dev/null | grep -q '__x86_64__'; then
  HW_ISA_FLAGS=(-msse4.2 -mpclmul)
  HWCOMBINE_ISA_FLAGS=(-msse4.2 -mpclmul -fno-vectorize -fno-slp-vectorize)
fi

SAN=("${SYSROOT[@]}" -fsanitize=address,undefined -fno-sanitize-recover=all
     "${COV_WORKAROUND[@]}" -fno-omit-frame-pointer -g)

OBJS=()
compile_c() {
  local src="$1"
  shift
  local o="$OUT/$(echo "$src" | tr '/' '_').o"
  "$LLVM/bin/clang" -O2 "${SAN[@]}" -fsanitize=fuzzer-no-link "$@" \
    -I"$PREFIX/include" -include lean-simd-models/c/simd_shim.h -c "$src" -o "$o" \
    2> >(grep -v "newer 'macOS'" >&2 || true)
  OBJS+=("$o")
}

for m in Reference Arith Portable Memcpy Dispatch CApi; do
  compile_c ".lake/build/ir/MemcpyCrc32c/Impl/$m.c"
done
compile_c ".lake/build/ir/MemcpyCrc32c/Impl/HwCombine.c" ${HWCOMBINE_ISA_FLAGS[@]+"${HWCOMBINE_ISA_FLAGS[@]}"}
compile_c ".lake/build/ir/MemcpyCrc32c/Impl/Hw.c" ${HW_ISA_FLAGS[@]+"${HW_ISA_FLAGS[@]}"}
for m in Models Trusted; do
  compile_c "lean-simd-models/.lake/build/ir/SimdModels/$m.c"
done

"$LLVM/bin/clang++" -std=c++17 -O2 -fno-exceptions -fno-rtti "${SAN[@]}" \
  -fsanitize=fuzzer-no-link -I"$PREFIX/include" -Icxx \
  -c cxx/leancrc32c.cc -o "$OUT/leancrc32c.o" \
  2> >(grep -v "newer 'macOS'" >&2 || true)

CXX_RUNTIME=()
if [ -d "$LLVM/lib/c++" ]; then
  CXX_RUNTIME=(-L"$LLVM/lib/c++" -Wl,-rpath,"$LLVM/lib/c++")
fi

"$LLVM/bin/clang++" -std=c++17 -O2 "${SAN[@]}" -fsanitize=fuzzer \
  "${ABSL_CXXFLAGS[@]}" -Icxx \
  cxx/fuzz.cc "$OUT/leancrc32c.o" "${OBJS[@]}" "${ABSL_LDFLAGS[@]}" \
  ${CXX_RUNTIME[@]+"${CXX_RUNTIME[@]}"} \
  ${LD_SYSROOT[@]+"${LD_SYSROOT[@]}"} \
  -L"$PREFIX/lib/lean" -lleanshared -lInit_shared -Wl,-rpath,"$PREFIX/lib/lean" \
  -o "$OUT/fuzz" \
  2> >(grep -v "newer 'macOS'" >&2 || true)

echo "built $OUT/fuzz using $LLVM"
