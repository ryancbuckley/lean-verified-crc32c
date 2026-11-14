#!/bin/bash
# Builds the abseil CRC library sources directly (release flags, no cmake)
# into build/absl/libabslcrc.a, plus the test-case generator.
# Usage: tests/build_absl.sh [path-to-abseil-cpp]
set -euo pipefail
A="${1:-$HOME/programming/temp/abseil-cpp}"
OUT="$(cd "$(dirname "$0")/.." && pwd)/build/absl"
mkdir -p "$OUT/obj"
SRCS=(
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
OBJS=()
for s in "${SRCS[@]}"; do
  o="$OUT/obj/$(echo "$s" | tr '/' '_').o"
  clang++ -std=c++17 -O2 -DNDEBUG -I"$A" -c "$A/$s" -o "$o"
  OBJS+=("$o")
done
rm -f "$OUT/libabslcrc.a"
ar rcs "$OUT/libabslcrc.a" "${OBJS[@]}"
clang++ -std=c++17 -O2 -DNDEBUG -I"$A" "$(dirname "$0")/absl_gen.cc" "$OUT/libabslcrc.a" -o "$OUT/absl_gen"
(cd "$A" && git rev-parse HEAD) > "$OUT/ABSEIL_COMMIT"
clang++ --version | head -1 > "$OUT/COMPILER"
