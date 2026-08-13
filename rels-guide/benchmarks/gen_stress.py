#!/usr/bin/env python3
"""Generate transitive-closure stress benchmarks for theory_sets_rels.

usage: gen_stress.py <outdir>

The in-tree rels regressions are all tiny, so these families put load on the
code paths that the "build the TC graph once" patch touches. All are decided by
the same reachability argument as fuzz_tc.py, so the ; EXPECT: headers are
exact, not observed.

Scaling families, N in {4, 8, 16, 32, 64}:

  base-chain-N    chain of N base edges in x, query (1,N+1) in TC(x)     unsat
  closure-chain-N the same chain asserted in TC(x) instead of x          unsat
  mixed-chain-N   alternating base and closure edges -- the shape that
                  needs the edges applyTCRule contributes to
                  d_tcr_tcGraph, i.e. exactly what a rebuild discards    unsat
  clique-N        denser graph: edges i->i+1 and i->i+2                  unsat
  eqrel-N         three provably equal base relations, closure edge on
                  one of them, query on another                         unsat
  sat-chain-N     chain with a query that does not follow                sat
  join-tc-N       the rel_tc_7 shape (closure under a join) at size N    unsat

Probes for the one case where building one graph per closure *term* (the patch)
could do more work than one graph per base *representative* (main's guard):
k closure terms over base relations that are asserted equal.

  eqwide-Kk-Nn    plain top-level equalities x0 = xk
  eqterm-Kk-Nn    each closure term pinned by an auxiliary tk = TC(xk)
  eqsat-Kk-Nn     equalities entailed only at the SAT level, so that the
                  preprocessor cannot substitute them away
"""
import os
import sys

SIZES = [4, 8, 16, 32, 64]
EQ_K = [2, 4, 8, 16]
EQ_N = [16, 32]


def hdr(expect, nrels=1):
    L = ["; EXPECT: %s" % expect,
         "(set-option :incremental false)",
         "(set-logic ALL)"]
    L += ["(declare-fun x () (Relation Int Int))"] if nrels == 1 else []
    return L


def mem(a, b, r="x"):
    return "(assert (set.member (tuple %d %d) %s))" % (a, b, r)


def scaling(family, n):
    if family == "base-chain":
        L = hdr("unsat")
        L += [mem(i, i + 1) for i in range(1, n + 1)]
        L += ["(assert (not (set.member (tuple 1 %d) (rel.tclosure x))))" % (n + 1)]
    elif family == "closure-chain":
        L = hdr("unsat")
        L += [mem(i, i + 1, "(rel.tclosure x)") for i in range(1, n + 1)]
        L += ["(assert (not (set.member (tuple 1 %d) (rel.tclosure x))))" % (n + 1)]
    elif family == "mixed-chain":
        L = hdr("unsat")
        L += [mem(i, i + 1, "x" if i % 2 else "(rel.tclosure x)")
              for i in range(1, n + 1)]
        L += ["(assert (not (set.member (tuple 1 %d) (rel.tclosure x))))" % (n + 1)]
    elif family == "clique":
        L = hdr("unsat")
        for i in range(1, n + 1):
            L.append(mem(i, i + 1))
            if i + 2 <= n + 1:
                L.append(mem(i, i + 2))
        L += ["(assert (not (set.member (tuple 1 %d) (rel.tclosure x))))" % (n + 1)]
    elif family == "eqrel":
        L = hdr("unsat")
        L += ["(declare-fun y () (Relation Int Int))",
              "(declare-fun z () (Relation Int Int))",
              "(assert (= x y))", "(assert (= y z))"]
        L += [mem(i, i + 1) for i in range(1, n + 1)]
        L += [mem(1, n + 2, "(rel.tclosure y)")]
        L += ["(assert (not (set.member (tuple 1 %d) (rel.tclosure z))))" % (n + 1)]
    elif family == "sat-chain":
        L = hdr("sat")
        L += [mem(i, i + 1) for i in range(1, n + 1)]
        L += ["(assert (not (set.member (tuple %d 1) (rel.tclosure x))))" % (n + 1)]
    elif family == "join-tc":
        L = hdr("unsat")
        L += ["(declare-fun y () (Relation Int Int))",
              "(assert (= y (rel.join (rel.tclosure x) x)))"]
        L += [mem(i, i + 1) for i in range(1, n + 1)]
        L += ["(assert (not (set.subset y (rel.tclosure x))))"]
    else:
        raise SystemExit("unknown family " + family)
    return L + ["(check-sat)"]


def eqfamily(family, k, n):
    L = ["; EXPECT: unsat", "(set-option :incremental false)", "(set-logic ALL)"]
    L += ["(declare-fun x%d () (Relation Int Int))" % i for i in range(k)]
    if family == "eqwide":
        L += ["(assert (= x0 x%d))" % i for i in range(1, k)]
        L += [mem(i, i + 1, "x0") for i in range(1, n + 1)]
        # keep every closure term live
        L += ["(assert (set.subset (rel.tclosure x%d) (rel.tclosure x%d)))" % (i, i)
              for i in range(k)]
        L += ["(assert (not (set.member (tuple 1 %d) (rel.tclosure x%d))))"
              % (n + 1, k - 1)]
    elif family == "eqterm":
        L += ["(declare-fun t%d () (Relation Int Int))" % i for i in range(k)]
        L += ["(assert (= x0 x%d))" % i for i in range(1, k)]
        L += ["(assert (= t%d (rel.tclosure x%d)))" % (i, i) for i in range(k)]
        L += [mem(i, i + 1, "x0") for i in range(1, n + 1)]
        L += ["(assert (not (set.member (tuple 1 %d) t%d)))" % (n + 1, k - 1)]
    elif family == "eqsat":
        L += ["(declare-fun t%d () (Relation Int Int))" % i for i in range(k)]
        L += ["(declare-fun p%d () Bool)" % i for i in range(k)]
        for i in range(1, k):
            L += ["(assert (or (= x0 x%d) p%d))" % (i, i),
                  "(assert (not p%d))" % i]
        L += ["(assert (or (= t%d (rel.tclosure x%d)) p0))" % (i, i)
              for i in range(k)]
        L += ["(assert (not p0))"]
        L += [mem(i, i + 1, "x0") for i in range(1, n + 1)]
        L += ["(assert (not (set.member (tuple 1 %d) t%d)))" % (n + 1, k - 1)]
    else:
        raise SystemExit("unknown family " + family)
    return L + ["(check-sat)"]


def write(outdir, name, lines):
    with open(os.path.join(outdir, name + ".smt2"), "w") as fh:
        fh.write("\n".join(lines) + "\n")


def main():
    outdir = sys.argv[1]
    os.makedirs(outdir, exist_ok=True)
    count = 0
    for f in ["base-chain", "closure-chain", "mixed-chain", "clique", "eqrel",
              "sat-chain", "join-tc"]:
        for n in SIZES:
            write(outdir, "%s-%d" % (f, n), scaling(f, n))
            count += 1
    for f in ["eqwide", "eqterm"]:
        for k in EQ_K:
            for n in EQ_N + [64]:
                write(outdir, "%s-K%d-N%d" % (f, k, n), eqfamily(f, k, n))
                count += 1
    for k in [1, 2, 4, 8]:
        for n in EQ_N:
            write(outdir, "eqsat-K%d-N%d" % (k, n), eqfamily("eqsat", k, n))
            count += 1
    print("wrote %d benchmarks to %s" % (count, outdir))


main()
