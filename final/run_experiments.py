"""Run cvc5 and sls-reachability on the BAPA benchmarks of this artifact.

usage: python3 run_experiments.py CVC5_BINARY [--jobs N] [--timeout SECONDS]

Run it with a Python that has z3 installed (see install.sh), since
sls-reachability is run with the same interpreter. It writes results.csv next
to this script, with the answer and the wall-clock time of every configuration
on every benchmark. Times are measured around the solver process, so they
include its startup.

The benchmarks use the set syntax of z3 (card, subset, intersection, ...).
For cvc5, they are rewritten to the SMT-LIB syntax of sets (set.card,
set.subset, set.inter, ...) in a temporary directory. Their status annotations
are dropped there, since they are the statuses of the verification conditions
these formulas come from, and some of the formulas themselves are
satisfiable.
"""
import argparse
import csv
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
BENCHMARKS = [(d, "fol_%07d.smt2" % i) for d in ("arith", "card") for i in range(1, 121)]

# (name, tool, options)
CONFIGURATIONS = [
    ("sets", "cvc5", ["--sets-to-bags=none"]),
    ("sets-fmf", "cvc5", ["--sets-to-bags=none", "--fmf-bound"]),
    ("setof-stock", "cvc5", ["--sets-to-bags=setof", "--fmf-bound"]),
    ("relaxed-stock", "cvc5", ["--sets-to-bags=relaxed", "--fmf-bound"]),
    ("setof-liastar", "cvc5", ["--sets-to-bags=setof", "--bags-to-liastar"]),
    ("relaxed-liastar", "cvc5", ["--sets-to-bags=relaxed", "--bags-to-liastar"]),
    ("sls-bapa", "sls", []),
    ("sls-mapa", "sls", ["--mapa"]),
    ("sls-mapa-unfold5", "sls", ["--mapa", "--unfold=5"]),
    ("sls-mapa-nointerp", "sls", ["--mapa", "--no-interp"]),
]

SYNTAX = [
    (r"\bALL_SUPPORTED\b", "ALL"),
    (r"\(card ", "(set.card "),
    (r"\(subset ", "(set.subset "),
    (r"\(intersection ", "(set.inter "),
    (r"\(setminus ", "(set.minus "),
    (r"\(union ", "(set.union "),
]


def to_cvc5_syntax(src, dst):
    lines = []
    for line in open(src):
        if "set-info :status" in line:
            continue
        for pattern, replacement in SYNTAX:
            line = re.sub(pattern, replacement, line)
        lines.append(line)
    with open(dst, "w") as fh:
        fh.writelines(lines)


def classify(returncode, stdout, stderr):
    lines = [l.strip() for l in stdout.splitlines() if l.strip()]
    if lines and lines[0] in ("sat", "unsat", "unknown"):
        return lines[0]
    if "interrupted by timeout" in stdout + stderr:
        return "timeout"
    return "error: " + (stdout + stderr).strip().replace("\n", " ")[-120:]


def run(cmd, timeout):
    start = time.perf_counter()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, cwd=ROOT)
        answer = classify(p.returncode, p.stdout, p.stderr)
    except subprocess.TimeoutExpired:
        answer = "timeout"
    return answer, time.perf_counter() - start


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("cvc5", help="the cvc5 binary")
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--timeout", type=float, default=5.0)
    args = parser.parse_args()

    tmp = tempfile.mkdtemp(prefix="bapa-cvc5-")
    for d, f in BENCHMARKS:
        to_cvc5_syntax(os.path.join(ROOT, "benchmarks/bapa", d, f),
                       os.path.join(tmp, "%s_%s" % (d, f)))

    results = {}
    for name, tool, options in CONFIGURATIONS:
        def command(df):
            d, f = df
            if tool == "cvc5":
                # cvc5 enforces the limit itself; the process timeout is a guard
                return [args.cvc5, "--tlimit=%d" % (args.timeout * 1000)] + options \
                    + [os.path.join(tmp, "%s_%s" % (d, f))]
            return [sys.executable, os.path.join(ROOT, "lia_star_solver.py"),
                    os.path.join(ROOT, "benchmarks/bapa", d, f)] + options
        guard = args.timeout * 2 if tool == "cvc5" else args.timeout
        with ThreadPoolExecutor(args.jobs) as ex:
            rows = list(ex.map(lambda df: run(command(df), guard), BENCHMARKS))
        for (d, f), (answer, t) in zip(BENCHMARKS, rows):
            results.setdefault("%s/%s" % (d, f), {})[name] = (answer, t)
        print("%-18s done" % name, flush=True)

    with open(os.path.join(HERE, "results.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["benchmark"] + [c for name, _, _ in CONFIGURATIONS
                                    for c in (name + " answer", name + " time (s)")])
        for bench in sorted(results):
            w.writerow([bench] + [c for name, _, _ in CONFIGURATIONS
                                  for c in (results[bench][name][0],
                                            "%.4f" % results[bench][name][1])])


if __name__ == "__main__":
    main()
