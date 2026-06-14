#!/usr/bin/env python3
"""Mac-vs-Linux plots for the LIA* `final` configuration.

Produces two figures into the output directory:
  * cactus_mac_vs_linux.png   -- solved-count vs per-instance wall time, one
    curve per machine (lower/right = better).
  * scatter_mac_vs_linux.png  -- per-instance Mac time vs Linux time (log-log)
    on the instances both solved; the y=x diagonal separates "Mac faster"
    (below) from "Linux faster" (above).

Linux numbers come from comparison.csv (`cvc5 lazy final` column); Mac numbers
from mac/final.csv produced by run_campaign.sh.

Usage:  plot_mac_vs_linux.py <output_dir>
"""
import os, sys
import pandas as pd
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
COMPARISON = os.environ.get(
    "COMPARISON",
    "/Users/mahgoubyahia/paper-fmcad26-liastar/scripts/comparison.csv")
DEFI = ["sat", "unsat"]


def norm(s):
    return s.astype(str).str.strip().str.lower()


def main():
    outdir = sys.argv[1] if len(sys.argv) > 1 else HERE
    os.makedirs(outdir, exist_ok=True)
    df = pd.read_csv(COMPARISON)

    lin_res = norm(df["cvc5 lazy final result"])
    lin_dur = pd.to_numeric(df["cvc5 lazy final duration"], errors="coerce")

    mac = pd.read_csv(os.path.join(HERE, "final.csv"), header=None,
                      names=["file", "result", "duration"]).set_index("file").reindex(
                          df["cvc5 lazy  filename"])
    mac_res = norm(mac["result"]).reset_index(drop=True)
    mac_dur = pd.to_numeric(mac["duration"], errors="coerce").reset_index(drop=True)

    # ---- cactus ----
    plt.figure(figsize=(7, 5))
    for label, res, dur, style in [
        ("Linux reference", lin_res, lin_dur, dict(color="#c0392b", lw=2)),
        ("Mac (Apple M5 Max)", mac_res, mac_dur, dict(color="#2471a3", lw=2)),
    ]:
        t = np.sort(dur[res.isin(DEFI)].values)
        plt.plot(np.arange(1, len(t) + 1), t, label=f"{label} ({len(t)} solved)", **style)
    plt.xlabel("instances solved (sorted by time)")
    plt.ylabel("per-instance wall time (s)")
    plt.yscale("log")
    plt.title("LIA* final: cactus, Mac vs Linux (100 s timeout, 12-way)")
    plt.legend(loc="upper left")
    plt.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    p1 = os.path.join(outdir, "cactus_mac_vs_linux.png")
    plt.savefig(p1, dpi=150)
    plt.close()

    # ---- scatter (both solved) ----
    both = lin_res.isin(DEFI) & mac_res.isin(DEFI)
    x = mac_dur[both].values
    y = lin_dur[both].values
    plt.figure(figsize=(6, 6))
    plt.scatter(x, y, s=14, alpha=0.5, color="#2471a3", edgecolor="none")
    lo = max(1e-3, min(x.min(), y.min()))
    hi = max(x.max(), y.max())
    plt.plot([lo, hi], [lo, hi], "k--", lw=1, label="y = x (equal)")
    plt.plot([lo, hi], [2*lo, 2*hi], color="gray", ls=":", lw=1, label="Linux = 2× Mac")
    plt.xscale("log"); plt.yscale("log")
    plt.xlabel("Mac (Apple M5 Max) time (s)")
    plt.ylabel("Linux reference time (s)")
    plt.title(f"Per-instance time, both solved (n={both.sum()})\npoints above y=x: Mac faster")
    plt.legend(loc="upper left")
    plt.grid(True, which="both", alpha=0.3)
    plt.tight_layout()
    p2 = os.path.join(outdir, "scatter_mac_vs_linux.png")
    plt.savefig(p2, dpi=150)
    plt.close()

    print(f"wrote {p1}\nwrote {p2}")


if __name__ == "__main__":
    main()
