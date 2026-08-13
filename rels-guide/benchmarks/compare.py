#!/usr/bin/env python3
"""Differential + timing comparison of two cvc5 binaries on a set of files.

usage: compare.py <binA_label>=<binA> <binB_label>=<binB> <timeout_s> <file>...
Each file is run REPS times per binary; the minimum wall time is reported.
Expected status is taken from a "; EXPECT:" line if present.
"""
import subprocess, sys, time, os, re

REPS = int(os.environ.get("REPS", "3"))


def expected(path):
    with open(path) as fh:
        for line in fh:
            m = re.match(r"\s*;\s*EXPECT:\s*(\S+)", line)
            if m:
                return m.group(1)
    return None


def run(binary, path, tmo):
    best, status = None, None
    for _ in range(REPS):
        t0 = time.time()
        try:
            p = subprocess.run([binary, "--lang", "smt2", path],
                               capture_output=True, text=True, timeout=tmo)
            out = p.stdout.strip().splitlines()
            status = out[0].strip() if out else (p.stderr.strip().splitlines() or ["<no output>"])[0]
        except subprocess.TimeoutExpired:
            return "TIMEOUT", float(tmo)
        el = time.time() - t0
        best = el if best is None else min(best, el)
    return status, best


def main():
    la, ba = sys.argv[1].split("=", 1)
    lb, bb = sys.argv[2].split("=", 1)
    tmo = float(sys.argv[3])
    files = sys.argv[4:]
    print("%-24s %-8s | %-10s %8s | %-10s %8s | %s"
          % ("benchmark", "expect", la, "time", lb, "time", "speedup"))
    print("-" * 96)
    tot_a = tot_b = 0.0
    mismatches, disagree = [], []
    for f in files:
        exp = expected(f) or "-"
        sa, ta = run(ba, f, tmo)
        sb, tb = run(bb, f, tmo)
        tot_a += ta
        tot_b += tb
        sp = ("%.2fx" % (ta / tb)) if tb > 0 else "-"
        flag = ""
        if sa != sb:
            flag = "  <== STATUS DIFFERS"
            disagree.append(f)
        for lbl, s in ((la, sa), (lb, sb)):
            if exp != "-" and s != exp and s != "TIMEOUT":
                mismatches.append((f, lbl, s, exp))
        print("%-24s %-8s | %-10s %8.3f | %-10s %8.3f | %s%s"
              % (os.path.basename(f)[:-5], exp, sa, ta, sb, tb, sp, flag))
    print("-" * 96)
    print("TOTAL%s %.3fs   %s %.3fs   overall speedup %.2fx"
          % (" " * 33, tot_a, " " * 12, tot_b, (tot_a / tot_b) if tot_b else 0))
    if disagree:
        print("\nstatus disagreements: %s" % ", ".join(os.path.basename(f) for f in disagree))
    if mismatches:
        print("\nWRONG RESULTS vs EXPECT:")
        for f, lbl, s, exp in mismatches:
            print("  %s [%s] got %s want %s" % (os.path.basename(f), lbl, s, exp))
    else:
        print("\nno wrong answers (relative to ; EXPECT: lines)")


main()
