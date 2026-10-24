"""Run cvc5 and sls-reachability on the BAPA benchmarks of this artifact.

usage: python3 run_experiments.py CVC5_BINARY [--jobs N] [--timeout SECONDS]

Run it with a Python that has z3 installed (see install.sh), since
sls-reachability is run with the same interpreter. It writes results.csv next
to this script, with the answer and the wall-clock time of every configuration
on every benchmark. Times are measured around the solver process, so they
include its startup.

The only inputs are the 240 benchmarks in benchmarks/bapa. As in the paper,
they are read as problems over sets (BAPA) and as problems over multisets, i.e.
bags (MAPA): sls-reachability reads them as bags with --mapa, and cvc5 with
--sets-to-bags=relaxed.

cvc5 cannot parse the set syntax of z3 that the benchmarks use, so each
benchmark is translated in memory and given to cvc5 on its standard input:
the logic ALL_SUPPORTED becomes ALL, and card, subset, intersection and
setminus become set.card, set.subset, set.inter and set.minus. The status
annotation is dropped, since it is the status of the verification condition
the formula comes from, and some of the formulas themselves are satisfiable.

Before the timed runs of each configuration, every job runs the same command
once on the first benchmark, untimed. Otherwise the first runs of a
configuration are slower, since they start while the caches of the machine are
cold.
"""
import argparse
import csv
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
BENCHMARKS = [(d, "fol_%07d.smt2" % i) for d in ("arith", "card") for i in range(1, 121)]

# (name, reading, tool, options)
CONFIGURATIONS = [
    ("sets", "sets", "cvc5", ["--sets-to-bags=none"]),
    ("sets-fmf", "sets", "cvc5", ["--sets-to-bags=none", "--fmf-bound"]),
    ("setof-stock", "sets", "cvc5", ["--sets-to-bags=setof", "--fmf-bound"]),
    ("setof-liastar", "sets", "cvc5", ["--sets-to-bags=setof", "--bags-to-liastar"]),
    ("sls-bapa", "sets", "sls", []),
    ("relaxed-stock", "bags", "cvc5", ["--sets-to-bags=relaxed", "--fmf-bound"]),
    ("relaxed-liastar", "bags", "cvc5", ["--sets-to-bags=relaxed", "--bags-to-liastar"]),
    ("sls-mapa", "bags", "sls", ["--mapa"]),
    ("sls-mapa-unfold5", "bags", "sls", ["--mapa", "--unfold=5"]),
    ("sls-mapa-nointerp", "bags", "sls", ["--mapa", "--no-interp"]),
]

SYNTAX = [
    (r"\bALL_SUPPORTED\b", "ALL"),
    (r"\(card ", "(set.card "),
    (r"\(subset ", "(set.subset "),
    (r"\(intersection ", "(set.inter "),
    (r"\(setminus ", "(set.minus "),
]


def translate(text):
    lines = []
    for line in text.splitlines(keepends=True):
        if "set-info :status" in line:
            continue
        for pattern, replacement in SYNTAX:
            line = re.sub(pattern, replacement, line)
        lines.append(line)
    return "".join(lines)


def classify(stdout, stderr):
    lines = [l.strip() for l in stdout.splitlines() if l.strip()]
    if lines and lines[0] in ("sat", "unsat", "unknown"):
        return lines[0]
    if "interrupted by timeout" in stdout + stderr:
        return "timeout"
    return "error: " + (stdout + stderr).strip().replace("\n", " ")[-120:]


def run(cmd, timeout, stdin=None):
    start = time.perf_counter()
    try:
        p = subprocess.run(cmd, input=stdin, capture_output=True, text=True,
                           timeout=timeout, cwd=ROOT)
        answer = classify(p.stdout, p.stderr)
    except subprocess.TimeoutExpired:
        answer = "timeout"
    return answer, time.perf_counter() - start


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("cvc5", help="the cvc5 binary")
    parser.add_argument("--jobs", type=int, default=12)
    parser.add_argument("--timeout", type=float, default=5.0)
    args = parser.parse_args()

    paths = {df: os.path.join(ROOT, "benchmarks/bapa", *df) for df in BENCHMARKS}
    texts = {df: translate(open(path).read()) for df, path in paths.items()}

    results = {}
    for name, _, tool, options in CONFIGURATIONS:
        if tool == "cvc5":
            # cvc5 enforces the limit itself; the process timeout is a guard
            command = [args.cvc5, "--lang=smt2", "--tlimit=%d" % (args.timeout * 1000)] + options
            guard = args.timeout * 2

            def warm(_):
                return run(command, guard, texts[BENCHMARKS[0]])

            def timed(df):
                return run(command, guard, texts[df])
        else:
            solver = [sys.executable, os.path.join(ROOT, "lia_star_solver.py")]
            guard = args.timeout

            def warm(_):
                return run(solver + [paths[BENCHMARKS[0]]] + options, guard)

            def timed(df):
                return run(solver + [paths[df]] + options, guard)
        with ThreadPoolExecutor(args.jobs) as ex:
            list(ex.map(warm, range(args.jobs)))
            rows = list(ex.map(timed, BENCHMARKS))
        for (d, f), (answer, t) in zip(BENCHMARKS, rows):
            results.setdefault("%s/%s" % (d, f), {})[name] = (answer, t)
        print("%-18s done" % name, flush=True)

    with open(os.path.join(HERE, "results.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["benchmark"] + [c for name, _, _, _ in CONFIGURATIONS
                                    for c in (name + " answer", name + " time (s)")])
        for bench in sorted(results):
            w.writerow([bench] + [c for name, _, _, _ in CONFIGURATIONS
                                  for c in (results[bench][name][0],
                                            "%.4f" % results[bench][name][1])])


if __name__ == "__main__":
    main()
