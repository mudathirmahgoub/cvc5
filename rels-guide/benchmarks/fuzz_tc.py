#!/usr/bin/env python3
"""Differential test for the transitive-closure graph construction.

Formulas have the shape

    (assert (set.member (tuple u v) x))            for edges labelled 'x'
    (assert (set.member (tuple u v) (rel.tclosure x)))  for edges labelled 't'
    (assert (not (set.member (tuple a b) (rel.tclosure x))))

Exact oracle.  Let E be the union of both edge sets over distinct integer
constants.  Every model must contain, for each asserted x-edge, that edge in x,
and for each asserted tclosure edge (u,v), some x-path u ~> v.  Hence
(a,b) in TC(x) is entailed iff b is reachable from a in E in >= 1 steps.
Conversely, taking x = {x-edges} U {direct edge for each tclosure edge} gives a
model whenever b is not reachable.  So

    formula is unsat  <=>  b reachable from a in E in >= 1 steps.
"""
import itertools
import os
import random
import subprocess
import sys
import tempfile

SP = os.path.dirname(os.path.abspath(__file__))
# Snapshots of the two configurations. Override with BASE_BIN / ONCE_BIN; the
# defaults expect self-contained snapshots in base/ and once/ (see Appendix B of
# the guide for why copying the executable alone is not enough).
BINS = {"base": os.environ.get("BASE_BIN", os.path.join(SP, "base/cvc5")),
        "once": os.environ.get("ONCE_BIN", os.path.join(SP, "once/cvc5"))}
TIMEOUT = 8.0
# Instance size. The measurement against the unguarded baseline used the
# defaults; the re-run against the guarded baseline used MAX_NODES=7,
# MAX_EDGES=10.
MAX_NODES = int(os.environ.get("MAX_NODES", "5"))
MAX_EDGES = int(os.environ.get("MAX_EDGES", "5"))


def reachable(edges, a, b):
    """b reachable from a in >= 1 steps."""
    adj = {}
    for (u, v) in edges:
        adj.setdefault(u, set()).add(v)
    seen = set()
    stack = list(adj.get(a, ()))
    while stack:
        n = stack.pop()
        if n == b:
            return True
        if n in seen:
            continue
        seen.add(n)
        stack.extend(adj.get(n, ()))
    return False


def gen(rng):
    n = rng.randint(2, MAX_NODES)
    nodes = list(range(n))
    allpairs = [(u, v) for u in nodes for v in nodes if u != v]
    rng.shuffle(allpairs)
    k = rng.randint(1, min(MAX_EDGES, len(allpairs)))
    chosen = allpairs[:k]
    labels = [rng.choice("xt") for _ in chosen]
    # guarantee at least one of each label often enough to hit the bug
    if rng.random() < 0.7 and len(chosen) >= 2:
        labels[0] = "x"
        labels[1] = "t"
    a, b = rng.choice(allpairs)
    return chosen, labels, a, b


def render(chosen, labels, a, b):
    L = ["(set-logic ALL)", "(declare-fun x () (Relation Int Int))"]
    for (u, v), lab in zip(chosen, labels):
        tgt = "x" if lab == "x" else "(rel.tclosure x)"
        L.append(f"(assert (set.member (tuple {u} {v}) {tgt}))")
    L.append(f"(assert (not (set.member (tuple {a} {b}) (rel.tclosure x))))")
    L.append("(check-sat)")
    return "\n".join(L) + "\n"


def run(binary, path):
    try:
        p = subprocess.run([binary, f"--tlimit={int(TIMEOUT*1000)}", path],
                           capture_output=True, text=True, timeout=TIMEOUT + 5)
        out = p.stdout.strip().splitlines()
        return out[0].strip() if out else "EMPTY"
    except subprocess.TimeoutExpired:
        return "timeout"


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = random.Random(seed)
    stats = {k: {"correct": 0, "timeout": 0, "wrong": 0, "unknown": 0}
             for k in BINS}
    wrong = []
    diffs = []
    tmpdir = tempfile.mkdtemp(dir=SP)
    for i in range(N):
        chosen, labels, a, b = gen(rng)
        edges = chosen
        expect = "unsat" if reachable(edges, a, b) else "sat"
        path = os.path.join(tmpdir, f"f{i}.smt2")
        with open(path, "w") as f:
            f.write(render(chosen, labels, a, b))
        got = {}
        for k, bin_ in BINS.items():
            r = run(bin_, path)
            got[k] = r
            if r == "timeout":
                stats[k]["timeout"] += 1
            elif r == expect:
                stats[k]["correct"] += 1
            elif r in ("sat", "unsat"):
                stats[k]["wrong"] += 1
                wrong.append((k, path, expect, r))
            else:
                stats[k]["unknown"] += 1
        if got["base"] != got["once"]:
            diffs.append((path, expect, got["base"], got["once"]))
    print(f"seed={seed} n={N}")
    for k in BINS:
        s = stats[k]
        print(f"  {k:5s} correct={s['correct']:4d} timeout={s['timeout']:4d} "
              f"wrong={s['wrong']:4d} unknown={s['unknown']:4d}")
    print(f"  differing answers: {len(diffs)}")
    for d in diffs[:25]:
        print("   ", d)
    if wrong:
        print("  UNSOUND/INCORRECT ANSWERS:")
        for w in wrong[:20]:
            print("   ", w)
    # show a couple of the files where base times out and once succeeds
    winners = [d for d in diffs if d[2] == "timeout" and d[3] != "timeout"]
    losers = [d for d in diffs if d[3] == "timeout" and d[2] != "timeout"]
    print(f"  base timeout / once solved: {len(winners)}")
    print(f"  once timeout / base solved: {len(losers)}")
    if winners:
        print("  example won by 'once':")
        print(open(winners[0][0]).read())


main()
