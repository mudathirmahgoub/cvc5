#!/usr/bin/env python3
"""Build the Mac-vs-Linux comparison from the Mac campaign CSVs and the recorded
Linux numbers in comparison.csv.

For each configuration it reports, side by side:
  * solved counts (sat / unsat / timeout / solved),
  * cumulative time over each side's own solved set, median, max,
  * on the instances BOTH machines solved: cumulative-time ratio and the
    median per-instance speedup (Linux_seconds / Mac_seconds; >1 = Mac faster).

The Linux durations recorded in comparison.csv were collected with the same
methodology (12-way parallel, 100 s timeout, one Normaliz thread per instance),
so the comparison is apples-to-apples on methodology; absolute seconds still
carry the report's stated 10-30% run-to-run variance.

Usage:  compare_mac_linux.py [out.md]
        (writes markdown to stdout, and to out.md if given)
"""
import os, sys, pandas as pd

HERE = os.path.dirname(os.path.abspath(__file__))
COMPARISON = os.environ.get(
    "COMPARISON",
    "/Users/mahgoubyahia/paper-fmcad26-liastar/scripts/comparison.csv")
DEFI = ["sat", "unsat"]

# Mac campaign config -> (pretty label, Linux column prefix in comparison.csv)
CONFIGS = [
    ("acc",            "lazy accumulate",               "cvc5 lazy accumulate"),
    ("pp",             "lazy push/pop",                 "cvc5 lazy push-pop"),
    ("ms",             "lazy main-solver enumeration",  "cvc5 lazy main-solver"),
    ("gen",            "lazy + boolean generalization", "cvc5 lazy generalize"),
    ("sem",            "lazy + semantic generalization","cvc5 lazy semantic"),
    ("psum",           "lazy + partial sums",           "cvc5 lazy partial-sums"),
    ("guided_endgame", "guided + endgame (no cuts)",    "cvc5 lazy guided+endgame"),
    ("final",          "final default (+ cuts)",        "cvc5 lazy final"),
]


def norm(s):
    return s.astype(str).str.strip().str.lower()


def load_mac(cfg, df):
    path = os.path.join(HERE, f"{cfg}.csv")
    if not os.path.exists(path):
        return None, None
    c = pd.read_csv(path, header=None, names=["file", "result", "duration"])
    c = c.set_index("file").reindex(df["cvc5 lazy  filename"])
    return norm(c["result"]).reset_index(drop=True), \
           pd.to_numeric(c["duration"], errors="coerce").reset_index(drop=True)


def counts(res):
    vc = res.value_counts().to_dict()
    return vc.get("sat", 0), vc.get("unsat", 0), vc.get("timeout", 0) + vc.get("error", 0), \
           res.isin(DEFI).sum()


def main():
    df = pd.read_csv(COMPARISON)
    out = []
    w = out.append

    w("# LIA\\* lazy: Mac (Apple M5 Max) vs Linux reference\n")
    w("Reproduction of `claude/scripts/repro` on macOS. Same harness semantics "
      "(100 s timeout, 12-way parallel, one Normaliz thread per instance, "
      "production build); macOS adaptations: `perl` alarm in place of `timeout`, "
      "`Time::HiRes` in place of `$EPOCHREALTIME`, and the 6 GB `ulimit -v` cap "
      "dropped (unsupported on macOS; the `final` config peaks well under it).\n")
    w("Linux columns are the recorded numbers from "
      "`paper-fmcad26-liastar/scripts/comparison.csv` (same methodology).\n")

    # ---- solved-count table ----
    w("## Solved instances per configuration (480 benchmarks, 100 s)\n")
    w("| configuration | Mac sat | Mac unsat | Mac t/o | **Mac solved** | "
      "Lin sat | Lin unsat | Lin t/o | **Lin solved** |")
    w("|---|--:|--:|--:|--:|--:|--:|--:|--:|")
    summary = []
    for cfg, label, col in CONFIGS:
        mres, mdur = load_mac(cfg, df)
        lres = norm(df[col + " result"])
        ldur = pd.to_numeric(df[col + " duration"], errors="coerce")
        ls, lu, lt, lsolv = counts(lres)
        if mres is None:
            w(f"| {label} | – | – | – | *pending* | {ls} | {lu} | {lt} | **{lsolv}** |")
            continue
        ms, mu, mt, msolv = counts(mres)
        w(f"| {label} | {ms} | {mu} | {mt} | **{msolv}** | {ls} | {lu} | {lt} | **{lsolv}** |")
        summary.append((cfg, label, mres, mdur, lres, ldur))

    # ---- timing table ----
    w("\n## Timing: Mac vs Linux\n")
    w("`cum` = cumulative wall time over that machine's own solved set. "
      "`speedup` columns are over the instances **both** machines solved: "
      "`cum ratio` = Linux cum / Mac cum, `med speedup` = median of "
      "per-instance Linux/Mac (>1 means Mac is faster).\n")
    w("| configuration | Mac cum | Mac med | Mac max | Lin cum | Lin med | Lin max | cum ratio | med speedup | common |")
    w("|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|")
    for cfg, label, mres, mdur, lres, ldur in summary:
        msolved = mres.isin(DEFI)
        lsolved = lres.isin(DEFI)
        both = msolved & lsolved
        mcum, mmed, mmax = mdur[msolved].sum(), mdur[msolved].median()*1000, mdur[msolved].max()
        lcum, lmed, lmax = ldur[lsolved].sum(), ldur[lsolved].median()*1000, ldur[lsolved].max()
        ratio = (ldur[both].sum() / mdur[both].sum()) if mdur[both].sum() > 0 else float("nan")
        per = (ldur[both] / mdur[both].replace(0, float("nan"))).median()
        w(f"| {label} | {mcum:.1f}s | {mmed:.0f}ms | {mmax:.1f}s | "
          f"{lcum:.1f}s | {lmed:.0f}ms | {lmax:.1f}s | {ratio:.2f}× | {per:.2f}× | {both.sum()} |")

    text = "\n".join(out) + "\n"
    sys.stdout.write(text)
    if len(sys.argv) > 1:
        with open(sys.argv[1], "w") as f:
            f.write(text)
        sys.stderr.write(f"\nwrote {sys.argv[1]}\n")


if __name__ == "__main__":
    main()
