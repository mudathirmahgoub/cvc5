#!/usr/bin/env python3
"""Pick, for every rule, a representative lemma from a benchmark where the rule
is needed (lost or wrong without it), else where it fires.

usage: examples.py CVC5 OUTDIR_OF_MEASURE   (writes OUTDIR/examples.json)
"""
import json
import os
import re
import subprocess
import sys

LEMMA = re.compile(r"^\(lemma (.*) :source (\S+)\)$")


def main():
    cvc5, mdir = sys.argv[1:3]
    usage = json.load(open(os.path.join(mdir, "usage.json")))
    abl = json.load(open(os.path.join(mdir, "ablation.json")))
    target = {}
    for key, res in sorted(abl.items(), key=lambda kv: usage[kv[0].split("||")[0]]["time"]):
        pair, rule = key.split("||")
        if rule.startswith("GROUP_"):
            continue
        exp = usage[pair]["expected"]
        bad = res["answer"] != exp
        if bad and rule not in target:
            target[rule] = pair
    for pair, u in sorted(usage.items(), key=lambda kv: kv[1]["time"]):
        for rule in u["counts"]:
            target.setdefault(rule, pair)
    by_pair = {}
    for rule, pair in target.items():
        by_pair.setdefault(pair, []).append(rule)
    examples = {}
    for pair, rules in by_pair.items():
        cmd = usage[pair]["cmd"].split()
        args = [cvc5] + [a for a in cmd[1:-1] if not a.startswith("--tlimit=")] \
            + [f"--tlimit={int(max(60, 3 * usage[pair]['time'])) * 1000}", "-o", "lemmas", cmd[-1]]
        p = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        cand = {r: [] for r in rules}
        for line in p.stdout:
            m = LEMMA.match(line.rstrip("\n"))
            if m and m.group(2) in cand and len(cand[m.group(2)]) < 2000:
                cand[m.group(2)].append(m.group(1))
        p.wait()
        for r, lems in cand.items():
            if not lems:
                continue
            # prefer a lemma with a conjunctive premise and a moderate size
            good = [l for l in lems if "(and " in l and 60 <= len(l) <= 700]
            pick = min(good or lems, key=len)
            examples[r] = {"pair": pair, "lemma": pick}
        print(pair, sorted(r for r in rules if r in examples), flush=True)
    json.dump(examples, open(os.path.join(mdir, "examples.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
