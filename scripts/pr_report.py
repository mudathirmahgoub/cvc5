#!/usr/bin/env python3
"""pr_report.py <out-dir> MAIN-LABEL LABEL=RESULTS-DIR ...

Charts and markdown tables for a PR description, from portfolio.py results
(each RESULTS-DIR holds virtual/runs.json and real/runs.json). MAIN-LABEL names
the run whose per-configuration details are shown. Writes to <out-dir>:
  cactus-runs.png        virtual best of every run (time on x, solved on y)
  cactus-configs.png     every configuration of the main run, its virtual best
                         and its real portfolio
  solved-per-config.png  solved files per configuration and run
  matrix-<label>.md      every configuration on every benchmark (virtual)
  virtual-real.md        virtual best versus real portfolio of the main run
"""
import json
import os
import re
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

ORDER = ["sc-1-th", "sc-1-th-just-rf", "sc-1-th-no-ltts", "sc-2-th", "sc-2-th-just-rf",
         "plsc-1-th", "plsc-1-th-just-rf", "plsc-1-th-no-ltts", "plsc-2-th", "plsc-2-th-just-rf",
         "tso-1-th", "tso-1-th-just-rf", "tso-1-th-no-ltts"]
SHORT = {"default": "default", "fmf-unsat": "FMF", "nofmf-unsat": "noFMF", "stoponly": "stop-only",
         "fmf-unsat-rules": "FMF+R", "nofmf-unsat-rules": "noFMF+R", "nofmf-unsat-hammer": "noFMF+H"}
RUN_COLORS = ["#7f7f7f", "#d9822b", "#1f5fbf", "#2e8b57"]
CFG_COLORS = {"default": "#1f77b4", "fmf-unsat": "#ff7f0e", "nofmf-unsat": "#d62728",
              "stoponly": "#2ca02c", "fmf-unsat-rules": "#17becf", "nofmf-unsat-rules": "#e377c2",
              "nofmf-unsat-hammer": "#8c564b"}
MARKERS = "osD^v<>ph*"


def solved(r):
    return r in ("sat", "unsat")


def fmt(t):
    return "%.2f" % t if t < 10 else "%.1f" % t


def load(d):
    v = json.load(open(os.path.join(d, "virtual", "runs.json")))
    r = json.load(open(os.path.join(d, "real", "runs.json")))
    return dict(v=v, vt={x["benchmark"]: x for x in v["table"]}, rt={x["benchmark"]: x for x in r["table"]})


def slug(label):
    return re.sub(r"[^a-z0-9]+", "-", label.lower()).strip("-")


def cactus(ax, curves, timeout, total):
    """curves: list of (label, sorted times, color, marker, style)."""
    ends = []
    for label, ts, color, marker, ls in curves:
        if not ts:
            continue
        ys = list(range(1, len(ts) + 1))
        ax.plot(ts, ys, ls, color=color, marker=marker, markersize=4, linewidth=1.8, label=label)
        ends.append([ts[-1], len(ts), label, color])
    ax.axvline(timeout, color="gray", linestyle="--", linewidth=1)
    ax.text(timeout * 0.93, 0.4, "%g s limit" % timeout, rotation=90, ha="right", va="bottom",
            color="gray", fontsize=8)
    # direct labels at the right end of every curve; stagger equal counts
    used = {}
    for t, k, label, color in sorted(ends, key=lambda e: (e[1], e[0])):
        off = used.get(k, 0)
        used[k] = off + 1
        ax.annotate("%s: %d" % (label, k), (t, k), xytext=(5, -9 * off), textcoords="offset points",
                    color=color, fontsize=8, va="center")
    ax.set_xscale("log")
    ax.set_xlim(0.02, timeout * 12)
    ax.set_ylim(0, total + 0.8)
    ax.set_xlabel("time (s)")
    ax.set_ylabel("benchmarks solved")
    ax.grid(True, which="major", color="#e5e5e5")
    ax.set_axisbelow(True)


def main(out, main_label, specs):
    os.makedirs(out, exist_ok=True)
    runs = []
    for s in specs:
        label, d = s.split("=", 1)
        runs.append((label, load(d)))
    R = dict(runs)
    names = [n for n in ORDER if n in runs[0][1]["vt"]]
    timeout = runs[0][1]["v"]["timeout"]

    # cactus: virtual best of every run
    fig, ax = plt.subplots(figsize=(7.5, 4.2), dpi=150)
    curves = []
    for i, (label, d) in enumerate(runs):
        ts = sorted(d["vt"][n]["vbs_time"] for n in names if d["vt"][n]["vbs_config"])
        curves.append((label, ts, RUN_COLORS[i % len(RUN_COLORS)], MARKERS[i], "-"))
    cactus(ax, curves, timeout, len(names))
    ax.set_title("Virtual best per run (fastest configuration per file)", fontsize=10)
    ax.legend(loc="upper left", fontsize=8)
    fig.tight_layout()
    fig.savefig(os.path.join(out, "cactus-runs.png"))
    plt.close(fig)

    # cactus: every configuration of the main run
    d = R[main_label]
    cfgs = list(d["v"]["configs"])
    fig, ax = plt.subplots(figsize=(7.5, 5.4), dpi=150)
    curves = []
    for i, c in enumerate(cfgs):
        ts = sorted(d["vt"][n]["per_config"][c][1] for n in names if solved(d["vt"][n]["per_config"][c][0]))
        curves.append((SHORT.get(c, c), ts, CFG_COLORS.get(c, "gray"), MARKERS[i % len(MARKERS)], "-"))
    vts = sorted(d["vt"][n]["vbs_time"] for n in names if d["vt"][n]["vbs_config"])
    rts = sorted(d["rt"][n]["time"] for n in names if n in d["rt"] and d["rt"][n]["winner"])
    curves.append(("virtual best", vts, "black", "o", "-"))
    curves.append(("real portfolio", rts, "#7b2d8b", "x", "--"))
    cactus(ax, curves, timeout, len(names))
    ax.set_title("%s: every configuration, virtual best and real portfolio" % main_label, fontsize=10)
    ax.legend(loc="upper left", fontsize=7, ncol=2)
    fig.tight_layout()
    fig.savefig(os.path.join(out, "cactus-configs.png"))
    plt.close(fig)

    # solved files per configuration and run
    fig, ax = plt.subplots(figsize=(7.5, 3.6), dpi=150)
    w = 0.8 / len(runs)
    for i, (label, dd) in enumerate(runs):
        ys = [sum(1 for n in names if solved(dd["vt"][n]["per_config"][c][0])) if c in dd["v"]["configs"] else 0
              for c in cfgs]
        xs = [k + (i - (len(runs) - 1) / 2) * w for k in range(len(cfgs))]
        bars = ax.bar(xs, ys, w, label=label, color=RUN_COLORS[i % len(RUN_COLORS)])
        ax.bar_label(bars, fontsize=7, padding=1)
    ax.set_xticks(range(len(cfgs)))
    ax.set_xticklabels([SHORT.get(c, c) for c in cfgs], fontsize=8)
    ax.set_ylabel("files solved (of %d)" % len(names))
    ax.set_ylim(0, len(names) + 1)
    ax.set_title("Files solved by each configuration on its own", fontsize=10)
    ax.legend(fontsize=8, ncol=len(runs), loc="upper left")
    ax.grid(True, axis="y", color="#e5e5e5")
    ax.set_axisbelow(True)
    fig.tight_layout()
    fig.savefig(os.path.join(out, "solved-per-config.png"))
    plt.close(fig)

    # matrix of every run
    for label, dd in runs:
        cf = list(dd["v"]["configs"])
        L = ["| benchmark | exp. | " + " | ".join(SHORT.get(c, c) for c in cf) + " | fastest |",
             "|---|---|" + "---|" * (len(cf) + 1)]
        counts = {c: 0 for c in cf}
        for n in names:
            row = dd["vt"][n]
            cells = []
            for c in cf:
                res, t = row["per_config"][c]
                if solved(res):
                    counts[c] += 1
                    txt = "%s %s" % (res, fmt(t))
                    cells.append("**%s**" % txt if c == row["vbs_config"] else txt)
                elif res == "unknown":
                    cells.append("unknown %s" % fmt(t))
                elif res.startswith("error"):
                    cells.append("error")
                else:
                    cells.append("–")
            fast = "%s s" % fmt(row["vbs_time"]) if row["vbs_config"] else "unsolved"
            L.append("| %s | %s | %s | %s |" % (n, row["expected"] or "", " | ".join(cells), fast))
        nv = sum(1 for n in names if dd["vt"][n]["vbs_config"])
        L.append("| **solved** | | " + " | ".join("**%d**" % counts[c] for c in cf) + " | **%d of %d** |" % (nv, len(names)))
        open(os.path.join(out, "matrix-%s.md" % slug(label)), "w").write("\n".join(L) + "\n")

    # virtual best versus real portfolio of the main run
    L = ["| benchmark | virtual best | configuration | real portfolio | winner | real / virtual | CPU |",
         "|---|---|---|---|---|---|---|"]
    for n in names:
        a = d["vt"][n]
        b = d["rt"].get(n)
        if a["vbs_config"]:
            vb = "%s %s s" % (a["vbs_answer"], fmt(a["vbs_time"]))
            vc = SHORT.get(a["vbs_config"], a["vbs_config"])
        else:
            vb, vc = "timeout", ""
        if b and b["winner"]:
            rb = "%s %s s" % (b["answer"], fmt(b["time"]))
            rc = SHORT.get(b["winner"], b["winner"])
            ratio = "%.2f" % (b["time"] / a["vbs_time"]) if a["vbs_config"] else ""
        else:
            rb, rc, ratio = "timeout", "", ""
        L.append("| %s | %s | %s | %s | %s | %s | %.1f s |" % (n, vb, vc, rb, rc, ratio, b["cpu"] if b else 0))
    open(os.path.join(out, "virtual-real.md"), "w").write("\n".join(L) + "\n")
    print("wrote", sorted(os.listdir(out)))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3:])
