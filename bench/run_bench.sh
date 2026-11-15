#!/bin/bash
# Builds Abseil with CMake (Release, default flags), builds libleancrc32c.a,
# links bench/full_bench.cc into a single-process benchmark binary, and runs
# the full Phase 6 benchmarking protocol, writing raw and summary CSVs under
# reports/.
#
# Usage: bench/run_bench.sh [raw-csv] [summary-csv]
set -euo pipefail
cd "$(dirname "$0")/.."

RAW_CSV="${1:-reports/bench_apple_m4_raw.csv}"
SUM_CSV="${2:-reports/bench_apple_m4_summary.csv}"
ABSL="${ABSEIL:-$HOME/programming/temp/abseil-cpp}"
CMAKE_BIN="${CMAKE:-cmake}"
if ! command -v "$CMAKE_BIN" >/dev/null 2>&1 && [ -x /opt/homebrew/bin/cmake ]; then
  CMAKE_BIN=/opt/homebrew/bin/cmake
fi

mkdir -p build/bench reports

if [ -d "$ABSL" ] && command -v "$CMAKE_BIN" >/dev/null 2>&1; then
  if [ ! -f build/absl-cmake/absl/crc/libabsl_crc32c.a ]; then
    rm -rf build/absl-cmake
    "$CMAKE_BIN" -S "$ABSL" -B build/absl-cmake \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_CXX_STANDARD=17 \
      -DCMAKE_INSTALL_PREFIX="$PWD/build/absl-cmake/install" \
      -DABSL_PROPAGATE_CXX_STD=ON \
      -DBUILD_TESTING=OFF >/dev/null
    "$CMAKE_BIN" --build build/absl-cmake --target crc32c -j8 >/dev/null
  fi
  ABSL_CXXFLAGS=(-I"$ABSL")
  ABSL_ARCHIVES=()
  while IFS= read -r lib; do
    ABSL_ARCHIVES+=("$lib")
  done < <(find build/absl-cmake -name 'libabsl_*.a' | sort)
  if [ "$(uname -s)" = "Linux" ]; then
    ABSL_LDFLAGS=(-Wl,--start-group "${ABSL_ARCHIVES[@]}" -Wl,--end-group)
  else
    ABSL_LDFLAGS=("${ABSL_ARCHIVES[@]}")
  fi
elif pkg-config --exists absl_crc32c 2>/dev/null; then
  read -r -a ABSL_CXXFLAGS <<< "$(pkg-config --cflags absl_crc32c)"
  read -r -a ABSL_LDFLAGS <<< "$(pkg-config --libs absl_crc32c)"
else
  echo "error: CMake Abseil source not found at $ABSL and absl_crc32c not in pkg-config" >&2
  exit 1
fi

cxx/build.sh >/dev/null

clang++ -std=c++17 -O3 -DNDEBUG "${ABSL_CXXFLAGS[@]}" -Icxx \
  bench/full_bench.cc "${ABSL_LDFLAGS[@]}" $(cat build/cxx/LINK_FLAGS) \
  -o build/bench/full_bench \
  2> >(grep -v "newer 'macOS'" >&2 || true)

build/bench/full_bench "$RAW_CSV" "$SUM_CSV"
