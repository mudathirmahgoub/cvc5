#!/usr/bin/env python3
"""Run every relations regression (regress*/rels) with extra options and
compare with its EXPECT line: reports wrong answers and runs that did not
finish. Run from the root of the cvc5 checkout.

usage: regress_check.py CVC5 "EXTRA OPTIONS" [TIME_LIMIT_SECONDS] [JOBS]
"""
import glob
import os
import re
import shlex
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def run(cvc5, extra, limit, f):
    txt = open(f).read()
    expect = re.findall(r"^; EXPECT: (\S+)", txt, re.M)
    cmdlines = re.findall(r"^; COMMAND-LINE:(.*)$", txt, re.M) or [""]
    if not expect or expect[0] not in ("sat", "unsat"):
        return []
    res = []
    for cl in cmdlines:
        cmd = [cvc5, *shlex.split(cl), *shlex.split(extra), f"--tlimit={limit * 1000}", f]
        p = subprocess.run(cmd, capture_output=True, text=True)
        out = (p.stdout + p.stderr).strip().splitlines()
        res.append((f, cl.strip(), expect[0], out[0] if out else "?"))
    return res


def main():
    cvc5, extra = sys.argv[1], sys.argv[2]
    limit = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    jobs = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    files = sorted(glob.glob("test/regress/cli/regress*/rels/**/*.smt2", recursive=True))
    with ThreadPoolExecutor(jobs) as ex:
        results = [r for rs in ex.map(lambda f: run(cvc5, extra, limit, f), files) for r in rs]
    ok = [r for r in results if r[3] == r[2]]
    wrong = [r for r in results if r[3] in ("sat", "unsat") and r[3] != r[2]]
    other = [r for r in results if r[3] not in ("sat", "unsat")]
    print(f"runs={len(results)} ok={len(ok)} wrong={len(wrong)} unfinished={len(other)}")
    for f, cl, e, a in wrong:
        print("WRONG", f, cl, "expected", e, "got", a)
    for f, cl, e, a in other:
        print("UNFINISHED", f, cl, "expected", e, "got", a[:60])


if __name__ == "__main__":
    main()
