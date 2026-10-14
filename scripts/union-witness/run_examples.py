#!/usr/bin/env python3
"""Run the examples of this directory under four base configurations, each
without and with the prototype options; print one line per (file, config).

usage: run_examples.py CVC5 [TIME_LIMIT_SECONDS] [FILE...]
"""
import glob
import os
import subprocess
import sys
import time

BASES = {
    "default": [],
    "R": ["--rels-tc-subset"],
    "R+lazy": ["--rels-tc-subset", "--rels-tc-down-lazy"],
    "R+hammer": ["--rels-tc-subset", "--rels-acyclic-hammer"],
}
EXTRAS = {
    "none": [],
    "def": ["--rels-cycle-def-union"],
    "guard": ["--rels-cycle-unroll-guard"],
    "decide": ["--rels-cycle-len-decide"],
    "def+decide": ["--rels-cycle-def-union", "--rels-cycle-len-decide"],
}


def main():
    cvc5 = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    here = os.path.dirname(os.path.abspath(__file__))
    files = sys.argv[3:] or sorted(glob.glob(os.path.join(here, "examples", "*.smt2")))
    for f in files:
        for b, bopts in BASES.items():
            for e, eopts in EXTRAS.items():
                t = time.time()
                p = subprocess.run([cvc5, *bopts, *eopts, f"--tlimit={limit * 1000}", f],
                                   capture_output=True, text=True)
                out = (p.stdout + p.stderr).strip().splitlines()
                answer = out[0] if out else "?"
                if "timeout" in answer:
                    answer = "timeout"
                print(f"{os.path.basename(f):28s} {b:9s} {e:11s} {answer:8s} {time.time() - t:6.2f}s",
                      flush=True)


if __name__ == "__main__":
    main()
