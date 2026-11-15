#!/bin/bash
# Builds the C/C++ library and pure-C11 test binary (if needed) and runs the
# Phase 7 AArch64 Mach-O machine-code & relocation audit against
# `MemcpyCrc32c/Arm64/Code.lean`.
set -euo pipefail
cd "$(dirname "$0")/.."

if [ "$(uname -m)" != "arm64" ] && [ "$(uname -m)" != "aarch64" ]; then
  echo "SKIP: check_aarch64_mc.sh requires an AArch64 host"
  exit 0
fi

cxx/build.sh >/dev/null
clang -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 -Icxx \
  cxx/test_c_abi.c $(cat build/cxx/LINK_FLAGS) -o build/cxx/test_c_abi \
  2> >(grep -v "newer 'macOS'" >&2 || true)

python3 scripts/check_aarch64_mc.py
python3 scripts/check_aarch64_copy_mc.py
clang -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 \
  cxx/test_copy_large.c build/cxx/leancrc32c_copy_arm64.o -o build/cxx/test_copy_large
build/cxx/test_copy_large
clang -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 \
  cxx/test_copy_small.c build/cxx/leancrc32c_copy_arm64.o -o build/cxx/test_copy_small
build/cxx/test_copy_small
