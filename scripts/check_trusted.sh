#!/bin/bash
# Trust audit. `#print axioms` cannot see `@[extern]` or `implemented_by`, so
# this script is the other half of the audit: it fails if any Lean file other
# than lean-simd-models/SimdModels/Trusted.lean binds external code, or if any
# file uses `sorry`, `admit`, a new `axiom`, or `native_decide`. `bv_decide` is
# allowed only under a `BvDecide/` directory. Mentions inside backticks (in
# comments) are ignored.
set -euo pipefail
cd "$(dirname "$0")/.."
TRUSTED="lean-simd-models/SimdModels/Trusted.lean"
status=0
files=$(find MemcpyCrc32c MemcpyCrc32c.lean tests lean-simd-models -name '*.lean' -not -path '*/.lake/*')
scan() { # $1 = perl regex, $2 = description, $3 = path regex to exempt
  local hits
  hits=$(perl -ne 'BEGIN{$re=shift} print "$ARGV:$.: $_" if /$re/; close ARGV if eof' "$1" $files | grep -Ev "^($3):" || true)
  if [ -n "$hits" ]; then echo "FORBIDDEN ($2):"; echo "$hits"; status=1; fi
}
scan '(?<!`)@\[[^\]]*\bextern\b' "extern outside the trusted file" "$TRUSTED"
scan '(?<!`)\bimplemented_by\b' "implemented_by" "$TRUSTED"
scan '^\s*(private\s+|protected\s+)?(unsafe\s+)?axiom\s' "axiom" "NONE"
scan '(?<!`)\b(sorry|admit)\b(?!`)' "sorry/admit" "NONE"
scan '(?<!`)\bnative_decide\b(?!`)' "native_decide" "NONE"
scan '(?<!`)\bbv_decide\b(?!`)' "bv_decide outside a BvDecide directory" ".*/BvDecide/.*"
n=$(grep -c '^@\[extern' "$TRUSTED")
echo "trusted bindings in $TRUSTED: $n"
[ $status -eq 0 ] && echo "OK: no external bindings, axioms, sorry or native_decide outside the trusted file"
exit $status
