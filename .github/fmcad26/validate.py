#!/usr/bin/env python3
"""Run a cvc5 binary on every benchmark of comparison.csv and compare its
answers with the recorded cvc5 column.

    python3 validate.py FMCAD_DIR TLIMIT_S JOBS CMD...

CMD is the binary (possibly prefixed, e.g. `arch -x86_64 bin/cvc5`).
Prints counts and any sat/unsat disagreement.
"""
import csv
import os
import subprocess
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

fmcad, tlimit, jobs, cmd = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4:]
with open(os.path.join(fmcad, "comparison.csv"), newline="") as f:
    rows = [(r[3].strip(), r[4].strip()) for r in list(csv.reader(f))[1:]]


def run(item):
    bench, expected = item
    try:
        p = subprocess.run(cmd + ["--tlimit={}".format(tlimit * 1000),
                                  os.path.join(fmcad, "benchmarks", bench)],
                           capture_output=True, text=True, timeout=tlimit + 30)
        out = (p.stdout.strip().splitlines() or [""])[-1]
        if "interrupted by timeout" in p.stdout + p.stderr:
            out = "timeout"
    except subprocess.TimeoutExpired:
        out = "timeout"
    return bench, expected, out or "error"


with ThreadPoolExecutor(jobs) as ex:
    results = list(ex.map(run, rows))
print("answers:", dict(Counter(o for _, _, o in results)))
print("recorded:", dict(Counter(e for _, e, _ in results)))
flips = [(b, e, o) for b, e, o in results
         if e in ("sat", "unsat") and o in ("sat", "unsat") and e != o]
odd = [(b, e, o) for b, e, o in results
       if o not in ("sat", "unsat", "timeout")]
print("sat/unsat disagreements:", len(flips))
for x in flips + odd[:10]:
    print("  ", *x)
lost = sum(1 for _, e, o in results if e in ("sat", "unsat") and o == "timeout")
print("recorded solved but timed out at {}s: {}".format(tlimit, lost))
sys.exit(1 if flips or odd else 0)
