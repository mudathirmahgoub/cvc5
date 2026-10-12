#!/usr/bin/env python3
"""Prove that a relation has no cycle by a decomposition into bounded cvc5
queries (see DECOMPOSITION.md).

From a problem whose goal is (assert (rel.cyclic REL)) it writes and runs
  * path-K:  K distinct elements joined by REL edges p0 -> p1 -> ... with no
             other REL edge between any two of them (no chord, no backward
             edge); unsat means a shortest cycle of REL has fewer than K+1
             edges, i.e. at most K edges;
  * cycle-n: n distinct elements e0 -> e1 -> ... -> e(n-1) -> e0 of REL edges,
             for n = 1 .. K.
If every query is unsat, REL has no cycle under the assertions of the problem.

usage: decompose.py CVC5 PROBLEM REL K OUTDIR [TIMEOUT_S] [JOBS] [-- OPTIONS...]
"""
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor


def cycle(rel, n):
    vs = [f"e{i}" for i in range(n)]
    g = "".join(f"(declare-const {v} Atom)\n" for v in vs)
    if n > 1:
        g += "(assert (distinct " + " ".join(vs) + "))\n"
    for i in range(n):
        g += f"(assert (set.member (tuple {vs[i]} {vs[(i + 1) % n]}) {rel}))\n"
    return g


def chordfree_path(rel, k):
    vs = [f"p{i}" for i in range(k)]
    g = "".join(f"(declare-const {v} Atom)\n" for v in vs)
    g += "(assert (distinct " + " ".join(vs) + "))\n"
    for i in range(k - 1):
        g += f"(assert (set.member (tuple {vs[i]} {vs[i + 1]}) {rel}))\n"
    for i in range(k):
        for j in range(k):
            if i != j and j != i + 1:
                g += f"(assert (not (set.member (tuple {vs[i]} {vs[j]}) {rel})))\n"
    return g


def main():
    args = sys.argv[1:]
    opts = []
    if "--" in args:
        i = args.index("--")
        args, opts = args[:i], args[i + 1:]
    cvc5, problem, rel, k, outdir = args[:5]
    k = int(k)
    timeout = int(args[5]) if len(args) > 5 else 3600
    jobs = int(args[6]) if len(args) > 6 else 4
    src = open(problem).read()
    goal = f"(assert (rel.cyclic {rel}))"
    assert src.count(goal) == 1, f"the problem must contain exactly one {goal}"
    os.makedirs(outdir, exist_ok=True)
    queries = [(f"path-{k}", chordfree_path(rel, k))]
    queries += [(f"cycle-{n}", cycle(rel, n)) for n in range(1, k + 1)]
    files = []
    for name, g in queries:
        f = os.path.join(outdir, name + ".smt2")
        open(f, "w").write(src.replace(goal, g))
        files.append((name, f))

    def run(item):
        name, f = item
        t = time.time()
        p = subprocess.run([cvc5, *opts, f"--tlimit={timeout * 1000}", f],
                           capture_output=True, text=True)
        out = (p.stdout + p.stderr).strip().splitlines()
        return name, out[0] if out else "?", time.time() - t

    results = {}
    with ThreadPoolExecutor(jobs) as ex:
        for name, answer, secs in ex.map(run, files):
            results[name] = answer
            print(f"{name:10s} {answer:10s} {secs:8.1f}s", flush=True)
    ok = all(a == "unsat" for a in results.values())
    print("conclusion:", f"{rel} is acyclic" if ok else "not proved")


if __name__ == "__main__":
    main()
