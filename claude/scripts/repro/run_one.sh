#!/bin/bash
# Run ONE benchmark under ONE configuration; print a CSV line:
#     <relpath>,<result>,<duration_seconds>
#
# Usage:  run_one.sh <config> <relpath-under-FMCAD_DIR>
#
# This is the exact per-instance harness used for every campaign in the
# report. Measurement conditions, identical across configs:
#   * 100 s wall-clock timeout            (timeout 100)
#   * 6 GB virtual-memory cap per process (ulimit -v 6291456)
#   * single-threaded: no Normaliz OpenMP (OMP_NUM_THREADS=1)
#   * wall time measured around the whole invocation via $EPOCHREALTIME
#   * the *production* build (assertions off, optimized); timing on the debug
#     build is meaningless (10-50x slower).
#
# IMPORTANT about flags. Over the project the shipped defaults changed: by the
# end, generalize / guided / endgame=10 / cuts are all default-ON. To reproduce
# a *historical* row in isolation we start from BASE_OFF (every later feature
# turned off => the original "lazy accumulate" procedure) and switch exactly
# one feature back on. That is why, e.g., "gen" passes --no-arith-liastar-guided.

CVC5=${CVC5:-/home/mudathir/all/cvc5/mudathir/build-prod/bin/cvc5}
FMCAD_DIR=${FMCAD_DIR:-/home/mudathir/fmcad26}
TIMEOUT=${TIMEOUT:-100}

# every post-baseline feature off == the original lazy-accumulate procedure
BASE_OFF="--no-arith-liastar-generalize --no-arith-liastar-guided --arith-liastar-endgame=0 --no-arith-liastar-cuts"

cfg="$1"; rel="$2"; f="$FMCAD_DIR/$rel"

case "$cfg" in
  acc)            flags="$BASE_OFF" ;;                                              # 463: lazy accumulate baseline
  pp)             flags="$BASE_OFF --arith-liastar-push-pop" ;;                     # 460
  ms)             flags="$BASE_OFF --arith-liastar-main-solver" ;;                  # 447
  gen)            flags="--no-arith-liastar-guided --arith-liastar-endgame=0 --no-arith-liastar-cuts" ;;          # 466: +boolean generalization
  sem)            flags="--no-arith-liastar-guided --arith-liastar-endgame=0 --no-arith-liastar-cuts --arith-liastar-generalize-semantic" ;; # 465
  psum)           flags="$BASE_OFF --arith-liastar-partial-sums" ;;                 # 450
  guided_endgame) flags="--no-arith-liastar-cuts" ;;                               # 476: gen+guided+endgame, no cuts
  eager)          flags="--no-arith-liastar-lazy" ;;
  final|default)  flags="" ;;                                                       # 480: shipped default (all on)
  *) echo "unknown config: $cfg" >&2; exit 2 ;;
esac

start=$EPOCHREALTIME
out=$(ulimit -v 6291456; OMP_NUM_THREADS=1 timeout "$TIMEOUT" "$CVC5" -q $flags "$f" 2>&1)
code=$?
end=$EPOCHREALTIME
dur=$(awk "BEGIN{printf \"%.3f\", $end-$start}")

if [ $code -eq 124 ]; then res="timeout"; else res=$(echo "$out" | tail -1 | tr -d '\r'); fi
case "$res" in sat|unsat|unknown|timeout) ;; *) res="error";; esac
echo "$rel,$res,$dur"
