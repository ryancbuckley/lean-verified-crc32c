#!/bin/bash
# Differential test of the Lean CRC functions against abseil.
# Usage: tests/run_diff.sh [cases-per-seed] [seeds...]
set -euo pipefail
cd "$(dirname "$0")/.."
N="${1:-20000}"; shift || true
SEEDS=("${@:-1 2 3}")
[ -x build/absl/absl_gen ] || tests/build_absl.sh
lake build diff >/dev/null
for seed in ${SEEDS[@]}; do
  echo -n "seed $seed: "
  build/absl/absl_gen "$seed" "$N" | .lake/build/bin/diff
done
