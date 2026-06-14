#!/bin/bash
# macOS port of repro/run_one.sh -- run ONE benchmark under ONE configuration;
# print a CSV line:   <relpath>,<result>,<duration_seconds>
#
# Usage:  run_one.sh <config> <relpath-under-FMCAD_DIR>
#
# Differences from the Linux harness (and why):
#   * timeout: macOS has no `timeout`/`gtimeout`, so we use mac/timed_run.pl
#     (perl alarm + Time::HiRes) which also returns the wall-clock duration.
#   * timing: bash on macOS is 3.2 (no $EPOCHREALTIME); timed_run.pl measures
#     the child's wall time directly and prints it as a trailing __DURATION__ line.
#   * memory cap: `ulimit -v` is unsupported on macOS (setrlimit RLIMIT_AS
#     rejects it), so the 6 GB cap is dropped. The `final` config peaks well
#     under that on every instance, so this does not change any answer.
#   * single-threaded Normaliz is still enforced via OMP_NUM_THREADS=1.
#
# Flags per config are IDENTICAL to the Linux run_one.sh (see comments there).

HERE="$(cd "$(dirname "$0")" && pwd)"
CVC5=${CVC5:-/Users/mahgoubyahia/cvc5/mudathir/build-prod/bin/cvc5}
FMCAD_DIR=${FMCAD_DIR:-/Users/mahgoubyahia/fmcad26}
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

out=$(OMP_NUM_THREADS=1 perl "$HERE/timed_run.pl" "$TIMEOUT" "$CVC5" -q $flags "$f" 2>&1)
code=$?
dur=$(printf '%s\n' "$out" | sed -n 's/^__DURATION__ //p' | tail -1)
[ -z "$dur" ] && dur="0.000"

if [ $code -eq 124 ]; then
  res="timeout"
else
  res=$(printf '%s\n' "$out" | grep -v '^__DURATION__' | tail -1 | tr -d '\r')
fi
case "$res" in sat|unsat|unknown|timeout) ;; *) res="error";; esac
echo "$rel,$res,$dur"
