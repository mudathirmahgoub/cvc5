#!/usr/bin/env python3
"""Evidence for every rule of the relations calculus on the portfolio benchmarks.

Needs a cvc5 built with scripts/evidence/rule-ids.patch (finer inference ids
and --rels-evidence-disable). From the runs.json of a virtual portfolio run
(scripts/portfolio.py) it takes every solved (benchmark, configuration) pair
and
  1. usage:    reruns it with --stats-internal -o lemmas and records, per rule,
               the number of lemmas and one example lemma (the shortest of the
               first 200 of that rule);
  2. ablation: for every rule that fired there, reruns it with
               --rels-evidence-disable=RULE and records whether the pair is
               still solved, lost (timeout/unknown), or answered wrongly.
Sat benchmarks are run with --check-models, so that a rule needed for a correct
model shows up as an error.

usage: measure.py CVC5 RUNS_JSON OUTDIR [JOBS] [usage|ablation|both]
"""
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

# the rules of the calculus (new in the PR) and the existing rules they use
RULES = [
    # cycle witness
    "SETS_RELS_ACYCLIC_SELF_LOOP", "SETS_RELS_INST_CYCLE", "SETS_RELS_SAME_OPERANDS",
    "SETS_RELS_UNROLL_CYCLE", "SETS_RELS_SPLIT_CYCLE_LEN",
    # minimality
    "SETS_RELS_ALTERNATE", "SETS_RELS_ALT_CLOSE", "SETS_RELS_CHORD", "SETS_RELS_DISTINCT",
    "SETS_RELS_BACKWARD",
    # last call
    "SETS_RELS_LAST_CALL_COMPLETION", "SETS_RELS_ANCHOR_BRANCH",
    # acyclicity and anchors
    "SETS_RELS_ACYCLIC_DOWN", "SETS_RELS_REGISTER", "SETS_RELS_ANCHOR_INCLUSION",
    "SETS_RELS_ANCHOR_CONFLICT",
    # closure induction
    "SETS_RELS_TC_SUBSET_SYNTACTIC", "SETS_RELS_TC_SUBSET_SELF", "SETS_RELS_TC_SUBSET_PRODUCT",
    "SETS_RELS_TC_SUBSET_INTER_MINUS", "SETS_RELS_TC_SUBSET_SUPERSET",
    # functionality
    "SETS_RELS_FUNCTIONAL", "SETS_RELS_FUNCTIONAL_PAIR", "SETS_RELS_NOT_FUNCTIONAL",
    # closures and joins: lazy split and grounding conflicts
    "SETS_RELS_TCLOSURE_DOWN_LAZY", "SETS_RELS_TCLOSURE_GROUNDING_CONFLICT",
    "SETS_RELS_JOIN_GROUNDING_CONFLICT",
    # existing rules of cvc5 main
    "SETS_RELS_TCLOSURE_UP", "SETS_RELS_TCLOSURE_DOWN", "SETS_RELS_JOIN_COMPOSE",
    "SETS_RELS_JOIN_SPLIT_1",
]
LEMMA = re.compile(r"^\(lemma (.*) :source (\S+)\)$")
# groups of rules that can replace one another, ablated together
GROUPS = {
    "GROUP_CLOSURE_INDUCTION": ["SETS_RELS_TC_SUBSET_SYNTACTIC", "SETS_RELS_TC_SUBSET_SELF",
                                "SETS_RELS_TC_SUBSET_PRODUCT", "SETS_RELS_TC_SUBSET_INTER_MINUS",
                                "SETS_RELS_TC_SUBSET_SUPERSET"],
    "GROUP_MINIMALITY": ["SETS_RELS_ALTERNATE", "SETS_RELS_ALT_CLOSE", "SETS_RELS_CHORD",
                         "SETS_RELS_DISTINCT", "SETS_RELS_BACKWARD"],
    "GROUP_ANCHORS": ["SETS_RELS_ANCHOR_INCLUSION", "SETS_RELS_ANCHOR_BRANCH",
                      "SETS_RELS_ANCHOR_CONFLICT"],
    "GROUP_FUNCTIONAL": ["SETS_RELS_FUNCTIONAL", "SETS_RELS_FUNCTIONAL_PAIR"],
}


def run_usage(cvc5, cmd, limit, sat):
    args = cmd.split()
    args = [cvc5] + [a for a in args[1:] if not a.startswith("--tlimit=")]
    args = args[:-1] + [f"--tlimit={limit * 1000}", "--stats-internal", "-o", "lemmas"] \
        + (["--check-models"] if sat else []) + args[-1:]
    t = time.time()
    p = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    answer, counts, examples = None, {}, {}
    seen = {}
    for line in p.stdout:
        line = line.rstrip("\n")
        if answer is None and line in ("sat", "unsat", "unknown"):
            answer = line
        m = LEMMA.match(line)
        if m and m.group(2) in RULES:
            rid, lem = m.group(2), m.group(1)
            seen[rid] = seen.get(rid, 0) + 1
            if seen[rid] <= 200 and (rid not in examples or len(lem) < len(examples[rid])):
                examples[rid] = lem
        if "inferencesLemma = {" in line:
            for kv in line.split("{", 1)[1].rstrip("}").split(","):
                if ":" in kv:
                    k, v = kv.rsplit(":", 1)
                    if k.strip() in RULES:
                        counts[k.strip()] = counts.get(k.strip(), 0) + int(v)
        if "interrupted by timeout" in line:
            answer = "timeout"
        if line.startswith("(error"):
            answer = "error: " + line[:120]
    p.wait()
    return {"answer": answer or "?", "time": round(time.time() - t, 2),
            "counts": counts, "examples": examples}


def run_ablation(cvc5, cmd, limit, sat, rule):
    args = cmd.split()
    args = [cvc5] + [a for a in args[1:] if not a.startswith("--tlimit=")]
    ids = ",".join(GROUPS.get(rule, [rule]))
    args = args[:-1] + [f"--tlimit={limit * 1000}", f"--rels-evidence-disable={ids}"] \
        + (["--check-models"] if sat else []) + args[-1:]
    t = time.time()
    p = subprocess.run(args, capture_output=True, text=True)
    out = (p.stdout + p.stderr).strip().splitlines()
    a = out[0] if out else "?"
    if "timeout" in a:
        a = "timeout"
    elif a.startswith("(error") or "Error" in a or "check-models" in a.lower():
        a = "error"
    return {"answer": a, "time": round(time.time() - t, 2)}


def main():
    cvc5, runs_json, outdir = sys.argv[1:4]
    jobs = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    phase = sys.argv[5] if len(sys.argv) > 5 else "both"
    os.makedirs(outdir, exist_ok=True)
    runs = json.load(open(runs_json))["runs"]
    pairs = [(k, v) for k, v in sorted(runs.items()) if v["result"] in ("sat", "unsat")]
    upath = os.path.join(outdir, "usage.json")
    if phase in ("usage", "both"):
        def u(item):
            key, v = item
            limit = int(min(600, max(60, 3 * v["time"])))
            r = run_usage(cvc5, v["cmd"], limit, v["result"] == "sat")
            r.update(expected=v["result"], ref_time=v["time"], cmd=v["cmd"])
            print(f"usage {key:40s} {r['answer']:8s} {r['time']:7.1f}s rules={len(r['counts'])}",
                  flush=True)
            return key, r
        with ThreadPoolExecutor(jobs) as ex:
            usage = dict(ex.map(u, pairs))
        json.dump(usage, open(upath, "w"), indent=1)
    usage = json.load(open(upath))
    if phase in ("ablation", "both"):
        todo = []
        for key, r in usage.items():
            if r["answer"] != r["expected"]:
                continue
            for rule in RULES:
                if r["counts"].get(rule, 0) > 0:
                    todo.append((key, rule))
            for g, members in GROUPS.items():
                if sum(1 for m in members if r["counts"].get(m, 0) > 0) >= 2:
                    todo.append((key, g))
        print(f"ablation: {len(todo)} runs", flush=True)

        def a(item):
            key, rule = item
            r = usage[key]
            limit = int(min(300, max(60, 5 * r["time"])))
            res = run_ablation(cvc5, r["cmd"], limit, r["expected"] == "sat", rule)
            res.update(limit=limit)
            print(f"ablate {key:40s} -{rule:40s} {res['answer']:8s} {res['time']:7.1f}s",
                  flush=True)
            return (key, rule), res
        with ThreadPoolExecutor(jobs) as ex:
            abl = dict(ex.map(a, todo))
        json.dump({f"{k}||{rule}": v for (k, rule), v in abl.items()},
                  open(os.path.join(outdir, "ablation.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
