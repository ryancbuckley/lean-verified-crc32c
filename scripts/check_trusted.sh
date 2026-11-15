#!/bin/bash
# Trust audit. `#print axioms` cannot see `@[extern]`, `@[csimp]`, or
# `implemented_by`, so this script is the other half of the audit: it strips
# Lean line comments (`--`), nested block comments (`/- ... -/`), and string
# literal payloads while preserving line numbers, then fails if any `.lean` file
# outside `lean-simd-models/SimdModels/Trusted.lean` binds external code or if
# any `.lean` file uses `implemented_by`, `csimp`, `axiom`, `sorry`, `admit`,
# `native_decide`, `unsafe`, or `skipKernelTC` (`bv_decide` is allowed only
# under a `BvDecide/` directory).
set -euo pipefail
cd "$(dirname "$0")/.."
TRUSTED="lean-simd-models/SimdModels/Trusted.lean"
status=0

mapfile_lean() {
  find . -name '*.lean' -not -path '*/.lake/*' | sed 's|^\./||' | LC_ALL=C sort
}
files=$(mapfile_lean)

# Strip comments (`-- ...`, nested `/- ... -/`) and string interiors (`"..."`),
# replacing stripped characters with spaces and keeping every newline so file:line
# reporting stays exact.
strip_lean() {
  perl -e '
    use strict;
    use warnings;
    for my $f (@ARGV) {
      open my $fh, "<", $f or die "cannot open $f: $!";
      local $/;
      my $s = <$fh>;
      close $fh;
      my $out = "";
      my $i = 0;
      my $len = length($s);
      my $depth = 0;
      my $in_str = 0;
      while ($i < $len) {
        my $c = substr($s, $i, 1);
        my $c2 = ($i + 1 < $len) ? substr($s, $i, 2) : "";
        if ($depth > 0) {
          if ($c2 eq "/-") { $depth++; $out .= "  "; $i += 2; next; }
          if ($c2 eq "-/") { $depth--; $out .= "  "; $i += 2; next; }
          $out .= ($c eq "\n") ? "\n" : " ";
          $i++;
        } elsif ($in_str) {
          if ($c eq "\\" && $i + 1 < $len) {
            my $n = substr($s, $i + 1, 1);
            $out .= " " . (($n eq "\n") ? "\n" : " ");
            $i += 2;
            next;
          }
          if ($c eq "\"") { $in_str = 0; $out .= "\""; $i++; next; }
          $out .= ($c eq "\n") ? "\n" : " ";
          $i++;
        } else {
          if ($c2 eq "/-") { $depth = 1; $out .= "  "; $i += 2; next; }
          if ($c2 eq "--") {
            while ($i < $len && substr($s, $i, 1) ne "\n") { $out .= " "; $i++; }
            next;
          }
          if ($c eq "\"") { $in_str = 1; $out .= "\""; $i++; next; }
          if ($c eq "\x27" && $i + 2 < $len && substr($s, $i + 1, 1) ne "\\" && substr($s, $i + 2, 1) eq "\x27") {
            $out .= "   "; $i += 3; next;
          }
          if ($c eq "\x27" && $i + 3 < $len && substr($s, $i + 1, 1) eq "\\" && substr($s, $i + 3, 1) eq "\x27") {
            $out .= "    "; $i += 4; next;
          }
          $out .= $c;
          $i++;
        }
      }
      my $ln = 1;
      for my $line (split /\n/, $out, -1) {
        print "$f:$ln: $line\n";
        $ln++;
      }
    }
  ' "$@"
}

stripped=$(strip_lean $files)

scan() { # $1 = perl regex, $2 = description, $3 = path regex to exempt
  local hits
  hits=$(printf '%s\n' "$stripped" | perl -ne 'BEGIN{$re=shift} if (/^([^:]+:\d+):\s*(.*)$/) { my ($loc,$code)=($1,$2); print "$loc: $code\n" if $code =~ /$re/; }' "$1" | grep -Ev "^($3):" || true)
  if [ -n "$hits" ]; then
    echo "FORBIDDEN ($2):"
    echo "$hits"
    status=1
  fi
}

scan '\bextern\b' "extern outside the trusted file" "$TRUSTED"
scan '\bimplemented_by\b' "implemented_by" "NONE"
scan '\bcsimp\b' "csimp" "NONE"
scan '\baxiom\b' "axiom" "NONE"
scan '\b(sorry|admit)\b' "sorry/admit" "NONE"
scan '\bnative_decide\b' "native_decide" "NONE"
scan '\bbv_decide\b' "bv_decide outside a BvDecide directory" "(^|.*/)BvDecide/.*"
scan '\bunsafe\b' "unsafe" "NONE"
scan '\bskipKernelTC\b' "skipKernelTC" "NONE"

# Verify $TRUSTED itself imports only SimdModels.Models and every `def` is an `@[extern]` binding.
trusted_stripped=$(strip_lean "$TRUSTED")
bad_imports=$(printf '%s\n' "$trusted_stripped" | perl -ne 'if (/^[^:]+:\d+:\s*(import\s+\S+)/) { print "$1\n" unless $1 eq "import SimdModels.Models"; }')
if [ -n "$bad_imports" ]; then
  echo "FORBIDDEN (unexpected import in $TRUSTED):"
  echo "$bad_imports"
  status=1
fi

n=$(printf '%s\n' "$trusted_stripped" | perl -ne 'BEGIN{$c=0} if (/^[^:]+:\d+:\s*(.*)$/ && $1 =~ /\bextern\b/) { $c++; } END{print "$c\n"}')
ndefs=$(printf '%s\n' "$trusted_stripped" | perl -ne 'BEGIN{$c=0} if (/^[^:]+:\d+:\s*(.*)$/ && $1 =~ /\b(def|opaque)\b/) { $c++; } END{print "$c\n"}')
if [ "$n" -ne "$ndefs" ]; then
  echo "FORBIDDEN (mismatch between @[extern] count ($n) and def-or-opaque count ($ndefs) in $TRUSTED)"
  status=1
fi

echo "trusted bindings in $TRUSTED: $n"
[ $status -eq 0 ] && echo "OK: no external bindings, csimp, implemented_by, axioms, unsafe, sorry or native_decide outside the trusted file"
exit $status
