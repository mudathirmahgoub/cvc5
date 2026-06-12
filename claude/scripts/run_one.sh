#!/bin/bash
# Run one benchmark in one config and print a CSV line: relpath,result,duration
# $1 = config: "acc" (lazy accumulate, default), "pp" (lazy push/pop),
#      "ms" (lazy main-solver enumeration)
rel="$2"
f="/home/mudathir/fmcad26/$rel"
flags=""
if [ "$1" = "pp" ]; then flags="--arith-liastar-push-pop"; fi
if [ "$1" = "ms" ]; then flags="--arith-liastar-main-solver"; fi
start=$EPOCHREALTIME
out=$(ulimit -v 6291456; OMP_NUM_THREADS=1 timeout 100 \
  /home/mudathir/all/cvc5/mudathir/build-prod/bin/cvc5 -q $flags "$f" 2>&1)
code=$?
end=$EPOCHREALTIME
dur=$(awk "BEGIN{printf \"%.3f\", $end-$start}")
if [ $code -eq 124 ]; then
  res="timeout"
else
  res=$(echo "$out" | tail -1 | tr -d '\r')
fi
case "$res" in sat|unsat|unknown|timeout) ;; *) res="error";; esac
echo "$rel,$res,$dur"
