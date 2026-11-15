#!/bin/bash
# Audits and tests the C/C++ wrapper's trust boundary:
#   1. Static C-IR audit: walks the transitive call graph from the four raw
#      Lean entry points across all generated .c files and fails if any
#      reachable function reads ByteArray size/header, touches reference counts,
#      allocates, or dereferences a struct-aligned `lean_sarray_object*`.
#   2. Pure C11 ABI check (`-std=c11 -Wall -Wextra -Wpedantic -Werror`).
#   3. Debug (`!NDEBUG`) guard-page check (verifying `<lean/lean.h>` assertions
#      never inspect `m_header` or `m_size` on headerless caller buffers).
#   4. Release guard-page and in-process differential tests against Abseil,
#      with hardware acceleration both enabled and disabled.
# Usage: scripts/check_capi.sh [differential-iterations]
set -euo pipefail
cd "$(dirname "$0")/.."
ITERS="${1:-200000}"
ABSL="${ABSEIL:-$HOME/programming/temp/abseil-cpp}"
if [ -f build/absl/libabslcrc.a ] && [ -d "$ABSL" ]; then
  ABSL_CXXFLAGS="-I$ABSL"
  ABSL_LDFLAGS="build/absl/libabslcrc.a"
elif pkg-config --exists absl_crc32c 2>/dev/null; then
  ABSL_CXXFLAGS="$(pkg-config --cflags absl_crc32c)"
  ABSL_LDFLAGS="$(pkg-config --libs absl_crc32c)"
else
  tests/build_absl.sh "$ABSL"
  ABSL_CXXFLAGS="-I$ABSL"
  ABSL_LDFLAGS="build/absl/libabslcrc.a"
fi

cxx/build.sh >/dev/null

# 1. Static C-IR audit of transitive call graph from raw entry points.
python3 - <<'PY'
import pathlib, re, sys

c_files = [
    *(pathlib.Path(".lake/build/ir/MemcpyCrc32c/Impl") / f"{m}.c"
      for m in ["Reference", "Arith", "Portable", "HwCombine", "Hw", "Memcpy", "Dispatch", "CApi"]),
    *(pathlib.Path("lean-simd-models/.lake/build/ir/SimdModels") / f"{m}.c"
      for m in ["Models", "Trusted"]),
]

func_hdr = re.compile(
    r'^(?:LEAN_EXPORT|static(?:\s+inline)?)\s+[A-Za-z0-9_*\s]+?\b(l[p]?_[A-Za-z0-9_]+)\s*\([^;]*\)\s*\{',
    re.M,
)

funcs = {}
for p in c_files:
    src = p.read_text()
    for m in func_hdr.finditer(src):
        name = m.group(1)
        i = m.end() - 1
        depth = 0
        while i < len(src):
            if src[i] == '{':
                depth += 1
            elif src[i] == '}':
                depth -= 1
                if depth == 0:
                    funcs[name] = (str(p), src[m.start():i + 1])
                    break
            i += 1

roots = [
    "lp_leancrc32c_Crc32c_extendRaw___redArg",
    "lp_leancrc32c_Crc32c_extendHwRaw___redArg",
    "lp_leancrc32c_Crc32c_extendPortableRaw___redArg",
    "lp_leancrc32c_Crc32c_hwAvailableRaw___redArg",
]
for r in roots:
    if r not in funcs:
        print(f"MISSING ENTRY POINT IN GENERATED C: {r}", file=sys.stderr)
        sys.exit(1)

call_re = re.compile(r'\b(l[p]?_[A-Za-z0-9_]+)\s*\(')
visited = set()
stack = list(roots)
while stack:
    fn = stack.pop()
    if fn in visited or fn not in funcs:
        continue
    visited.add(fn)
    _, body = funcs[fn]
    for callee in call_re.findall(body):
        if callee not in visited and callee in funcs:
            stack.append(callee)

forbidden = re.compile(
    r'\b('
    r'lean_byte_array_size|lean_sarray_size|lean_byte_array_uget|'
    r'lean_sarray_cptr|lean_to_sarray|'
    r'lean_inc|lean_inc_ref|lean_dec|lean_dec_ref|lean_is_exclusive|'
    r'lean_alloc_sarray|lean_copy_byte_array|lean_byte_array_extract'
    r')\b'
)

bad = []
for fn in sorted(visited):
    path, body = funcs[fn]
    hits = sorted(set(forbidden.findall(body)))
    if hits:
        bad.append(f"  {fn} ({path}): {', '.join(hits)}")

if bad:
    print("FORBIDDEN ByteArray header/refcount/sarray-struct operations in C-API call graph:", file=sys.stderr)
    print("\n".join(bad), file=sys.stderr)
    sys.exit(1)

print(f"OK: static C-IR audit ({len(visited)} reachable functions, 0 header/size/refcount/sarray-struct ops)")
PY

# 2. Pure C11 ABI check.
clang -std=c11 -Wall -Wextra -Wpedantic -Werror -O2 -Icxx \
  cxx/test_c_abi.c $(cat build/cxx/LINK_FLAGS) -o build/cxx/test_c_abi \
  2> >(grep -v "newer 'macOS'" >&2 || true)
build/cxx/test_c_abi
SIMDMODELS_DISABLE_HW=1 build/cxx/test_c_abi

# 3. Debug (!NDEBUG) guard-page check.
OUT=build/cxx-debug CFLAGS_EXTRA="" cxx/build.sh >/dev/null
clang++ -std=c++17 -O2 $ABSL_CXXFLAGS -Icxx cxx/test_guard.cc \
  $ABSL_LDFLAGS $(cat build/cxx-debug/LINK_FLAGS) -o build/cxx-debug/test_guard \
  2> >(grep -v "newer 'macOS'" >&2 || true)
build/cxx-debug/test_guard
SIMDMODELS_DISABLE_HW=1 build/cxx-debug/test_guard

# 4. Release guard-page and differential checks.
for t in test_guard test_diff; do
  clang++ -std=c++17 -O2 -DNDEBUG $ABSL_CXXFLAGS -Icxx cxx/$t.cc \
    $ABSL_LDFLAGS $(cat build/cxx/LINK_FLAGS) -o build/cxx/$t \
    2> >(grep -v "newer 'macOS'" >&2 || true)
done
build/cxx/test_guard
SIMDMODELS_DISABLE_HW=1 build/cxx/test_guard
build/cxx/test_diff "$ITERS" 1
SIMDMODELS_DISABLE_HW=1 build/cxx/test_diff "$ITERS" 2
