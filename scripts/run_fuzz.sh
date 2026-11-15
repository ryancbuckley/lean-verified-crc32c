#!/bin/bash
# Runs the libFuzzer + ASan + UBSan harness across parallel workers to reach
# >= 10^8 executions per path (both hardware and portable paths are checked on
# every single input), plus an explicit SIMDMODELS_DISABLE_HW=1 dispatch check.
#
# Usage: scripts/run_fuzz.sh [runs-per-worker] [workers]
set -euo pipefail
cd "$(dirname "$0")/.."

RUNS_PER_WORKER="${1:-13000000}"
WORKERS="${2:-8}"
BIN="${FUZZ_BIN:-build/fuzz/fuzz}"

if [ ! -x "$BIN" ]; then
  cxx/build_fuzz.sh
fi

mkdir -p build/fuzz/logs
PIDS=()
for w in $(seq 1 "$WORKERS"); do
  CORPUS="build/fuzz/corpus_$w"
  LOG="build/fuzz/logs/worker_$w.log"
  mkdir -p "$CORPUS"
  "$BIN" "$CORPUS" \
    -runs="$RUNS_PER_WORKER" \
    -max_len=1280 \
    -seed="$((100 + w))" \
    -print_final_stats=1 \
    >"$LOG" 2>&1 &
  PIDS+=("$!")
done

FAIL=0
for i in "${!PIDS[@]}"; do
  w="$((i + 1))"
  if ! wait "${PIDS[$i]}"; then
    echo "FAIL: fuzz worker $w failed; tail of build/fuzz/logs/worker_$w.log:" >&2
    tail -n 40 "build/fuzz/logs/worker_$w.log" >&2
    FAIL=1
  fi
done
[ "$FAIL" -eq 0 ] || exit 1

# Also verify runtime dispatch fallback under SIMDMODELS_DISABLE_HW=1.
mkdir -p build/fuzz/corpus_disable_hw
SIMDMODELS_DISABLE_HW=1 "$BIN" build/fuzz/corpus_disable_hw \
  -runs=2000000 \
  -max_len=1280 \
  -seed=999 \
  -print_final_stats=1 \
  >build/fuzz/logs/disable_hw.log 2>&1

python3 - <<'PY'
import glob, re

total = 0
for path in sorted(glob.glob("build/fuzz/logs/*.log")):
    txt = open(path).read()
    m = re.search(r"stat::number_of_executed_units:\s+(\d+)", txt)
    cov = re.findall(r"#\d+\s+DONE\s+cov:\s*(\d+)\s+ft:\s*(\d+)", txt)
    n = int(m.group(1)) if m else 0
    total += n
    cov_str = f"cov={cov[-1][0]} ft={cov[-1][1]}" if cov else "done"
    print(f"{path}: {n:,} executions ({cov_str})")
print(f"TOTAL EXECUTIONS PER PATH: {total:,}")
PY
