#!/usr/bin/env python3
"""make_figures.py <results-dir> <out-dir>

Turns the runs.json files written by scripts/portfolio.py (<results-dir>/virtual
and <results-dir>/real) into LaTeX fragments that relations-pr.tex \\input's
(usage: python3 make_figures.py data/final-300s figures):
  matrix.tex   every configuration on every benchmark (virtual portfolio)
  cactus.tex   cactus plot: time on x (log), solved count on y, 300 s line
  compare.tex  virtual best versus real portfolio, per solved benchmark
  numbers.tex  macros with the headline numbers
"""
import json
import os
import sys

ORDER = ["sc-1-th", "sc-1-th-just-rf", "sc-1-th-no-ltts", "sc-2-th", "sc-2-th-just-rf",
         "plsc-1-th", "plsc-1-th-just-rf", "plsc-1-th-no-ltts", "plsc-2-th", "plsc-2-th-just-rf",
         "tso-1-th", "tso-1-th-just-rf", "tso-1-th-no-ltts"]
SHORT = {"default": "default", "fmf-unsat": "FMF", "nofmf-unsat": "noFMF", "stoponly": "stop-only",
         "fmf-unsat-rules": "FMF+R", "nofmf-unsat-rules": "noFMF+R", "nofmf-unsat-hammer": "noFMF+H"}
STYLE = {"default": "blue,mark=*", "fmf-unsat": "orange!80!black,mark=square*",
         "nofmf-unsat": "red!70!black,mark=triangle*", "stoponly": "green!50!black,mark=diamond*",
         "fmf-unsat-rules": "cyan!60!black,mark=pentagon*", "nofmf-unsat-rules": "magenta!70!black,mark=star",
         "nofmf-unsat-hammer": "brown!70!black,mark=x"}


def solved(r):
    return r in ("sat", "unsat")


def fmt_t(t):
    return "%.2f" % t if t < 10 else "%.1f" % t


def cell(res, t, best):
    if solved(res):
        txt = "%s %s" % (res, fmt_t(t))
        return "\\best{%s}" % txt if best else "\\good{%s}" % txt
    if res == "unknown":
        return "\\textcolor{orange!80!black}{unknown}"
    if res.startswith("error"):
        return "\\bad{error}"
    return "\\tmo"


def main(resdir, outdir):
    os.makedirs(outdir, exist_ok=True)
    v = json.load(open(os.path.join(resdir, "virtual", "runs.json")))
    r = json.load(open(os.path.join(resdir, "real", "runs.json")))
    cfgs = list(v["configs"])
    vt = {row["benchmark"]: row for row in v["table"]}
    rt = {row["benchmark"]: row for row in r["table"]}
    names = [n for n in ORDER if n in vt] + [n for n in vt if n not in ORDER]

    # ---------------- matrix ----------------
    L = []
    L.append("\\begin{tabular}{@{}ll" + "l" * len(cfgs) + "cl@{}}")
    L.append("\\toprule")
    L.append("benchmark & exp. & " + " & ".join(SHORT.get(c, c) for c in cfgs) + " & by & fastest \\\\")
    L.append("\\midrule")
    counts = {c: 0 for c in cfgs}
    nv = 0
    wrong = 0
    for n in names:
        row = vt[n]
        per = row["per_config"]
        k = sum(1 for c in cfgs if solved(per[c][0]))
        cells = []
        for c in cfgs:
            res, t = per[c]
            if solved(res):
                counts[c] += 1
            cells.append(cell(res, t, c == row["vbs_config"]))
        if row["vbs_config"]:
            nv += 1
            fast = fmt_t(row["vbs_time"]) + " s"
        else:
            fast = "\\bad{open}"
        if row["flags"]:
            wrong += 1
        L.append("%s & %s & %s & %d & %s \\\\" % (n, row["expected"] or "", " & ".join(cells), k, fast))
    L.append("\\midrule")
    L.append("solved & & " + " & ".join(str(counts[c]) for c in cfgs) +
             " & \\multicolumn{2}{l}{\\textbf{%d of %d}} \\\\" % (nv, len(names)))
    L.append("\\bottomrule")
    L.append("\\end{tabular}")
    open(os.path.join(outdir, "matrix.tex"), "w").write("\n".join(L) + "\n")

    # ---------------- cactus ----------------
    C = []
    xmax = max(float(v["timeout"]) * 8, 2400)  # room for the direct labels
    ymax = len(names) + 2
    C.append("\\begin{axis}[width=11cm, height=6.6cm, xmode=log, xmin=0.02, xmax=%g," % xmax)
    C.append("  xlabel={time (s)}, ylabel={benchmarks solved}, ymin=0, ymax=%d," % ymax)
    C.append("  tick label style={font=\\scriptsize}, label style={font=\\scriptsize},")
    C.append("  legend style={font=\\tiny,at={(1.03,1)},anchor=north west}, legend cell align=left,")
    C.append("  grid=major, grid style={gray!20}]")
    labels = []
    for c in cfgs:
        ts = sorted(vt[n]["per_config"][c][1] for n in names if solved(vt[n]["per_config"][c][0]))
        if not ts:
            continue
        pts = " ".join("(%g,%d)" % (t, i + 1) for i, t in enumerate(ts))
        C.append("\\addplot[thick,%s,mark size=1.4pt] coordinates {%s};" % (STYLE.get(c, "gray"), pts))
        C.append("\\addlegendentry{%s}" % SHORT.get(c, c))
        labels.append((ts[-1], len(ts), SHORT.get(c, c), STYLE.get(c, "gray").split(",")[0]))
    vts = sorted(vt[n]["vbs_time"] for n in names if vt[n]["vbs_config"])
    rts = sorted(rt[n]["time"] for n in names if n in rt and rt[n]["winner"])
    C.append("\\addplot[very thick,black,mark=o,mark size=1.8pt] coordinates {%s};" %
             " ".join("(%g,%d)" % (t, i + 1) for i, t in enumerate(vts)))
    C.append("\\addlegendentry{virtual best}")
    C.append("\\addplot[very thick,purple!70!black,dashed,mark=x,mark size=2pt] coordinates {%s};" %
             " ".join("(%g,%d)" % (t, i + 1) for i, t in enumerate(rts)))
    C.append("\\addlegendentry{real portfolio}")
    C.append("\\draw[dashed,gray] (axis cs:%g,0) -- (axis cs:%g,%d) node[pos=0.95,left,font=\\scriptsize]{%g s};" %
             (v["timeout"], v["timeout"], ymax, v["timeout"]))
    # direct labels at the right end; stagger labels that end at the same count
    used = {}
    for t, k, name, color in sorted(labels, key=lambda x: (x[1], x[0])):
        off = used.get(k, 0)
        used[k] = off + 1
        C.append("\\node[font=\\tiny,%s,anchor=west,xshift=3pt,yshift=%dpt] at (axis cs:%g,%d) {%s %d};" %
                 (color, -7 * off, t, k, name, k))
    C.append("\\node[font=\\scriptsize,anchor=south east,yshift=2pt] at (axis cs:%g,%d) {virtual best %d};" % (vts[-1], len(vts), len(vts)))
    C.append("\\node[font=\\scriptsize,purple!70!black,anchor=north west,xshift=3pt,yshift=-2pt] at (axis cs:%g,%d) {real %d};" % (rts[-1], len(rts), len(rts)))
    C.append("\\end{axis}")
    open(os.path.join(outdir, "cactus.tex"), "w").write("\n".join(C) + "\n")

    # ---------------- compare ----------------
    K = []
    K.append("\\begin{tabular}{@{}llrrr@{}}")
    K.append("\\toprule")
    K.append("benchmark & winner & VBS & real & CPU \\\\")
    K.append("\\midrule")
    bars_v, bars_r, ticks = [], [], []
    ratios = []
    same = 0
    for n in names:
        a = vt[n]
        b = rt.get(n)
        if not a["vbs_config"]:
            continue
        rtime = b["time"] if b and b["winner"] else None
        win = SHORT.get(a["vbs_config"], a["vbs_config"])
        if b and b["winner"] == a["vbs_config"]:
            same += 1
        elif b and b["winner"]:
            win += " / " + SHORT.get(b["winner"], b["winner"])
        K.append("%s & %s & %s s & %s & %.1f s \\\\" % (
            n, win, fmt_t(a["vbs_time"]), (fmt_t(rtime) + " s") if rtime else "\\tmo", b["cpu"] if b else 0))
        if rtime:
            ratios.append(rtime / a["vbs_time"])
            bars_v.append("(%g,%s)" % (a["vbs_time"], n))
            bars_r.append("(%g,%s)" % (rtime, n))
            ticks.append(n)
    unsolved = [n for n in names if not vt[n]["vbs_config"]]
    if unsolved:
        cpu = ", ".join("%.0f" % rt[n]["cpu"] for n in unsolved if n in rt)
        K.append("\\midrule")
        K.append("%s & & timeout & timeout & %s s \\\\" % (", ".join(unsolved), cpu))
    K.append("\\bottomrule")
    K.append("\\end{tabular}")
    open(os.path.join(outdir, "compare.tex"), "w").write("\n".join(K) + "\n")
    B = []
    B.append("\\begin{axis}[xbar, width=5.2cm, height=6.2cm, xmode=log, log origin=infty,")
    B.append("  symbolic y coords={%s}, ytick=data, y dir=reverse," % ",".join(ticks))
    B.append("  tick label style={font=\\tiny}, xlabel={time to answer (s)}, xlabel style={font=\\scriptsize},")
    B.append("  xmin=0.02, xmax=400, bar width=3pt, enlarge y limits=0.05,")
    B.append("  legend style={font=\\tiny,at={(0.5,1.02)},anchor=south,legend columns=2}]")
    B.append("\\addplot[fill=black!70] coordinates {%s};" % " ".join(bars_v))
    B.append("\\addplot[fill=purple!60] coordinates {%s};" % " ".join(bars_r))
    B.append("\\legend{virtual best, real portfolio}")
    B.append("\\end{axis}")
    open(os.path.join(outdir, "compare-bars.tex"), "w").write("\n".join(B) + "\n")

    ratios.sort()
    med = ratios[len(ratios) // 2] if ratios else 0
    N = []
    N.append("\\newcommand{\\pfTimeout}{%g}" % v["timeout"])
    N.append("\\newcommand{\\pfVirtual}{%d}" % nv)
    N.append("\\newcommand{\\pfReal}{%d}" % len(rts))
    N.append("\\newcommand{\\pfTotal}{%d}" % len(names))
    N.append("\\newcommand{\\pfWrong}{%d}" % wrong)
    N.append("\\newcommand{\\pfSame}{%d}" % same)
    N.append("\\newcommand{\\pfRatioMin}{%.2f}" % (ratios[0] if ratios else 0))
    N.append("\\newcommand{\\pfRatioMax}{%.2f}" % (ratios[-1] if ratios else 0))
    N.append("\\newcommand{\\pfRatioMed}{%.2f}" % med)
    N.append("\\newcommand{\\pfMaxReal}{%s}" % fmt_t(rts[-1] if rts else 0))
    N.append("\\newcommand{\\pfNumConfigs}{%d}" % len(cfgs))
    N.append("\\newcommand{\\pfJobs}{%s}" % v.get("jobs", 1))
    N.append("\\newcommand{\\pfBestSingle}{%d}" % max(counts.values()))
    best_single = max(counts, key=lambda c: counts[c])
    N.append("\\newcommand{\\pfBestSingleName}{%s}" % SHORT.get(best_single, best_single))
    N.append("\\newcommand{\\pfCvc}{%s}" % v["cvc5_version"].split("[git ")[-1].split(" ")[0])
    N.append("\\newcommand{\\pfBench}{%s}" % v["benchmarks_rev"][:7])
    open(os.path.join(outdir, "numbers.tex"), "w").write("\n".join(N) + "\n")
    print("wrote %s (virtual %d/%d, real %d, wrong %d, ratio %.2f-%.2f)" % (
        outdir, nv, len(names), len(rts), wrong, ratios[0] if ratios else 0, ratios[-1] if ratios else 0))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
