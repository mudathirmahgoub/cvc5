#!/usr/bin/env python3
"""ablate.py --cvc5 BIN --bench-dir D --nofmf-dir D2 --configs-file F --extra="OPTS"
              --timeout S --jobs J --out OUT.json  BENCH:CONFIG ...

Runs selected (benchmark, configuration) pairs, with the options of the
configuration (from a configs file, or the built-in table of portfolio.py when
none is given) plus the extra options, and writes the answers and times to
OUT.json. Used to attribute a difference between two portfolio runs to an
option.
"""
import argparse
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import portfolio  # noqa: E402


def run(cvc5, path, opts, timeout):
    cmd = [cvc5, "--tlimit=%d" % int(timeout * 1000)] + opts + [path]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 30)
        out = (p.stdout + p.stderr).strip().splitlines()
        res = out[0] if out else "empty"
    except subprocess.TimeoutExpired:
        res = "timeout"
    t = time.time() - t0
    if res.startswith("cvc5 interrupted"):
        res = "timeout"
    elif res not in ("sat", "unsat", "unknown", "timeout"):
        res = "error: " + res[:60]
    return res, t, cmd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cvc5", required=True)
    ap.add_argument("--bench-dir", required=True)
    ap.add_argument("--nofmf-dir", required=True)
    ap.add_argument("--configs-file", default=None)
    ap.add_argument("--extra", default="", help="extra options, as one argument: --extra=\"--opt1 --opt2\"")
    ap.add_argument("--timeout", type=float, default=300.0)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--out", required=True)
    ap.add_argument("pairs", nargs="+")
    a = ap.parse_args()
    configs = json.load(open(a.configs_file)) if a.configs_file else portfolio.CONFIGS
    extra = a.extra.split()

    def one(pair):
        b, c = pair.split(":")
        d = a.nofmf_dir if configs[c].get("nofmf") else a.bench_dir
        opts = list(configs[c]["opts"]) + [o for o in extra if o not in configs[c]["opts"]]
        res, t, cmd = run(a.cvc5, os.path.join(d, b + ".smt2"), opts, a.timeout)
        print("%-20s %-20s %-8s %7.2f s" % (b, c, res, t), flush=True)
        return dict(benchmark=b, config=c, result=res, time=t, cmd=cmd)

    with ThreadPoolExecutor(a.jobs) as ex:
        rows = list(ex.map(one, a.pairs))
    json.dump(dict(extra=extra, timeout=a.timeout, rows=rows), open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
