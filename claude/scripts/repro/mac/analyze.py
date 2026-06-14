#!/usr/bin/env python3
"""macOS port of repro/analyze.py -- analyze a campaign CSV against the
comparison sheet (solved counts + soundness audit, optional head-to-head).

Identical logic to the Linux analyze.py; only the default COMPARISON path is
the Mac checkout, and it can be overridden with the COMPARISON env var.

Usage:
    analyze.py <config>.csv                       # solved counts + discrepancy audit
    analyze.py <config>.csv --vs <other>.csv      # head-to-head (+solved/-lost, timing)
"""
import os, sys, pandas as pd

COMPARISON = os.environ.get(
    "COMPARISON",
    "/Users/mahgoubyahia/paper-fmcad26-liastar/scripts/comparison.csv")
DEFI = ["sat", "unsat"]


def norm(s):
    return s.astype(str).str.strip().str.lower()


def load(path, df):
    """Align a campaign CSV (relpath,result,duration) to the sheet's row order."""
    c = pd.read_csv(path, header=None, names=["file", "result", "duration"])
    c = c.set_index("file").reindex(df["cvc5 lazy  filename"])
    assert not c["result"].isna().any(), f"{path}: rows do not line up with the sheet"
    return norm(c["result"]).reset_index(drop=True), c["duration"].astype(float).reset_index(drop=True)


def main():
    df = pd.read_csv(COMPARISON)
    res, dur = load(sys.argv[1], df)

    print(f"== {sys.argv[1]} ==")
    print("counts:", res.value_counts().to_dict(),
          "| solved:", res.isin(DEFI).sum(), "/", len(res))
    print(f"cumulative time over solved: {dur[res.isin(DEFI)].sum():.1f}s"
          f"  median: {dur[res.isin(DEFI)].median()*1000:.0f}ms"
          f"  max: {dur[res.isin(DEFI)].max():.1f}s")

    print("\nsoundness audit (discrepancies vs every reference column):")
    ref_cols = [c for c in df.columns if c.endswith("result")]
    for col in ref_cols:
        r = norm(df[col])
        both = r.isin(DEFI) & res.isin(DEFI)
        bad = df[both & (r != res)]
        tag = "" if len(bad) == 0 else "   <-- inspect"
        print(f"  vs {col:<34} {len(bad)} discrepancies{tag}")
        for _, row in bad.iterrows():
            print(f"        {row['cvc5 lazy  filename']}: "
                  f"ours={res[row.name]} {col.split()[0]}={r[row.name]}")

    if "--vs" in sys.argv:
        other = sys.argv[sys.argv.index("--vs") + 1]
        r2, d2 = load(other, df)
        won = (res.isin(DEFI)) & (~r2.isin(DEFI))
        lost = (~res.isin(DEFI)) & (r2.isin(DEFI))
        both = res.isin(DEFI) & r2.isin(DEFI)
        print(f"\nhead-to-head vs {other}:  +{won.sum()} solved, -{lost.sum()} lost")
        print(f"  common solved {both.sum()}: this={dur[both].sum():.1f}s  other={d2[both].sum():.1f}s")
        if won.sum():
            print("  newly solved:", df.loc[won, "cvc5 lazy  filename"].str.replace("sls-reachability/", "", regex=False).tolist())
        if lost.sum():
            print("  newly lost:  ", df.loc[lost, "cvc5 lazy  filename"].str.replace("sls-reachability/", "", regex=False).tolist())


if __name__ == "__main__":
    main()
