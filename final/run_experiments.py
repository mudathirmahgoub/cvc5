"""Run cvc5 and sls-reachability on the BAPA benchmarks of this artifact.

usage: python3 run_experiments.py CVC5_BINARY [--jobs N] [--timeout SECONDS]

Run it with a Python that has z3 installed (see install.sh), since
sls-reachability is run with the same interpreter. It writes results.csv next
to this script, with the answer and the wall-clock time of every configuration
on every benchmark. Times are measured around the solver process, so they
include its startup.

The benchmarks are read in two ways, as in the paper: as problems over sets
(BAPA), and as problems over multisets, i.e. bags (MAPA). Answers for one
reading are not answers for the other.

The benchmarks use the set syntax of z3 (card, subset, intersection,
setminus). For cvc5, they are rewritten in a temporary directory:
- for the set reading, to the SMT-LIB syntax of sets (set.card, set.subset,
  set.inter, set.minus);
- for the bag reading, to the SMT-LIB syntax of bags, following the MAPA
  translation of dsl.py: (Set Int) becomes (Bag Int), card becomes bag.card,
  subset becomes bag.subbag, intersection becomes bag.inter_min and setminus
  becomes bag.difference_subtract. The benchmarks have no set union and no
  equality between sets, which this translation does not cover.
The status annotations are dropped, since they are the statuses of the
verification conditions these formulas come from, and some of the formulas
themselves are satisfiable.

Before the timed runs of each configuration, every job runs the same command
once on a small problem, untimed. Otherwise the first runs of a configuration
are slower, since they start while the caches of the machine are cold.
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

# (name, reading, tool, options), where the tool is cvc5 on the set syntax,
# cvc5 on the bag syntax, or sls-reachability on the original files
CONFIGURATIONS = [
    ("sets", "sets", "cvc5-sets", ["--sets-to-bags=none"]),
    ("sets-fmf", "sets", "cvc5-sets", ["--sets-to-bags=none", "--fmf-bound"]),
    ("setof-stock", "sets", "cvc5-sets", ["--sets-to-bags=setof", "--fmf-bound"]),
    ("setof-liastar", "sets", "cvc5-sets", ["--sets-to-bags=setof", "--bags-to-liastar"]),
    ("sls-bapa", "sets", "sls", []),
    ("bags-stock", "bags", "cvc5-bags", ["--fmf-bound"]),
    ("bags-liastar", "bags", "cvc5-bags", ["--bags-to-liastar", "--force-logic=HO_ALL"]),
    ("relaxed-stock", "bags", "cvc5-sets", ["--sets-to-bags=relaxed", "--fmf-bound"]),
    ("relaxed-liastar", "bags", "cvc5-sets", ["--sets-to-bags=relaxed", "--bags-to-liastar"]),
    ("sls-mapa", "bags", "sls", ["--mapa"]),
    ("sls-mapa-unfold5", "bags", "sls", ["--mapa", "--unfold=5"]),
    ("sls-mapa-nointerp", "bags", "sls", ["--mapa", "--no-interp"]),
]

# the small problem of the warm-up, in the syntax of the BAPA benchmarks
WARMUP = """(set-logic ALL_SUPPORTED)
(declare-fun A () (Set Int))
(declare-fun n () Int)
(assert (= (card A) n))
(assert (> n 1))
(check-sat)
"""

SET_SYNTAX = [
    (r"\bALL_SUPPORTED\b", "ALL"),
    (r"\(card ", "(set.card "),
    (r"\(subset ", "(set.subset "),
    (r"\(intersection ", "(set.inter "),
    (r"\(setminus ", "(set.minus "),
]
BAG_SYNTAX = [
    (r"\bALL_SUPPORTED\b", "ALL"),
    (r"\(Set ", "(Bag "),
    (r"\(card ", "(bag.card "),
    (r"\(subset ", "(bag.subbag "),
    (r"\(intersection ", "(bag.inter_min "),
    (r"\(setminus ", "(bag.difference_subtract "),
]


def rewrite(src, dst, syntax):
    lines = []
    for line in open(src):
        if "set-info :status" in line:
            continue
        if "(union " in line:
            raise ValueError("%s: set union is not supported" % src)
        for pattern, replacement in syntax:
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

    # the input files of each tool, by benchmark, and of its warm-up
    tmp = tempfile.mkdtemp(prefix="bapa-cvc5-")
    warmup = os.path.join(tmp, "warmup.smt2")
    with open(warmup, "w") as fh:
        fh.write(WARMUP)
    inputs = {"sls": {}}
    warmups = {"sls": warmup}
    for tool, syntax in (("cvc5-sets", SET_SYNTAX), ("cvc5-bags", BAG_SYNTAX)):
        os.mkdir(os.path.join(tmp, tool))
        inputs[tool] = {}
        for d, f in BENCHMARKS:
            dst = os.path.join(tmp, tool, "%s_%s" % (d, f))
            rewrite(os.path.join(ROOT, "benchmarks/bapa", d, f), dst, syntax)
            inputs[tool][(d, f)] = dst
        warmups[tool] = os.path.join(tmp, tool, "warmup.smt2")
        rewrite(warmup, warmups[tool], syntax)
    for d, f in BENCHMARKS:
        inputs["sls"][(d, f)] = os.path.join(ROOT, "benchmarks/bapa", d, f)

    results = {}
    for name, _, tool, options in CONFIGURATIONS:
        def command(path):
            if tool == "sls":
                return [sys.executable, os.path.join(ROOT, "lia_star_solver.py"), path] + options
            # cvc5 enforces the limit itself; the process timeout is a guard
            return [args.cvc5, "--tlimit=%d" % (args.timeout * 1000)] + options + [path]

        guard = args.timeout if tool == "sls" else args.timeout * 2
        with ThreadPoolExecutor(args.jobs) as ex:
            list(ex.map(lambda _: run(command(warmups[tool]), guard), range(args.jobs)))
            rows = list(ex.map(lambda df: run(command(inputs[tool][df]), guard), BENCHMARKS))
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
