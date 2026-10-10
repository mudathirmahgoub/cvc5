#!/usr/bin/env python3
"""compare_runs.py <out-md> <out-tex-dir> LABEL=RESULTS-DIR ...

Compares portfolio runs written by portfolio.py (each RESULTS-DIR holds
virtual/runs.json and real/runs.json). Writes
  <out-md>                          markdown: per benchmark the virtual best
                                    (time and configuration) and the real
                                    portfolio time of every run; solved counts
                                    per configuration
  <out-tex-dir>/runs-table.tex      the same per-benchmark table for the slides
  <out-tex-dir>/runs-cactus.tex     cactus plot of the virtual best of each run:
                                    time on x (log), solved count on y
"""
import json
import os
import sys

ORDER = ["sc-1-th", "sc-1-th-just-rf", "sc-1-th-no-ltts", "sc-2-th", "sc-2-th-just-rf",
         "plsc-1-th", "plsc-1-th-just-rf", "plsc-1-th-no-ltts", "plsc-2-th", "plsc-2-th-just-rf",
         "tso-1-th", "tso-1-th-just-rf", "tso-1-th-no-ltts"]
SHORT = {"default": "default", "fmf-unsat": "FMF", "nofmf-unsat": "noFMF", "stoponly": "stop-only",
         "fmf-unsat-rules": "FMF+R", "nofmf-unsat-rules": "noFMF+R", "nofmf-unsat-hammer": "noFMF+H"}
STYLES = ["gray!70!black,mark=square*", "orange!80!black,mark=triangle*", "blue,mark=*",
          "green!50!black,mark=diamond*"]


def solved(r):
    return r in ("sat", "unsat")


def fmt(t):
    return "%.2f" % t if t < 10 else "%.1f" % t


def load(d):
    v = json.load(open(os.path.join(d, "virtual", "runs.json")))
    r = json.load(open(os.path.join(d, "real", "runs.json")))
    return v, {row["benchmark"]: row for row in v["table"]}, {row["benchmark"]: row for row in r["table"]}


def main(out_md, out_tex, specs):
    runs = []
    for s in specs:
        label, d = s.split("=", 1)
        v, vt, rt = load(d)
        runs.append((label, v, vt, rt))
    names = [n for n in ORDER if n in runs[0][2]] + [n for n in runs[0][2] if n not in ORDER]

    # ---------------- markdown ----------------
    M = []
    M.append("| benchmark | exp. | " + " | ".join("%s VBS | %s real" % (l, l) for l, _, _, _ in runs) + " |")
    M.append("|---|---|" + "---|---|" * len(runs))
    for n in names:
        cells = []
        for _, v, vt, rt in runs:
            a = vt[n]
            cells.append("%s %s s (%s)" % (a["per_config"][a["vbs_config"]][0], fmt(a["vbs_time"]),
                                           SHORT.get(a["vbs_config"], a["vbs_config"]))
                         if a["vbs_config"] else "timeout")
            b = rt.get(n)
            cells.append("%s s" % fmt(b["time"]) if b and b["winner"] else "timeout")
        M.append("| %s | %s | %s |" % (n, runs[0][2][n]["expected"] or "", " | ".join(cells)))
    tot = []
    for _, v, vt, rt in runs:
        nv = sum(1 for n in names if vt[n]["vbs_config"])
        nr = sum(1 for n in names if n in rt and rt[n]["winner"])
        tv = sum(vt[n]["vbs_time"] for n in names if vt[n]["vbs_config"])
        tot.append("**%d** (%.1f s) | **%d**" % (nv, tv, nr))
    M.append("| solved (total VBS time) | | %s |" % " | ".join(tot))
    M.append("")
    cfgs = list(runs[0][1]["configs"])
    M.append("| configuration | " + " | ".join(l for l, _, _, _ in runs) + " |")
    M.append("|---|" + "---|" * len(runs))
    for c in cfgs:
        row = []
        for _, v, vt, rt in runs:
            if c not in v["configs"]:
                row.append("-")
                continue
            ts = [vt[n]["per_config"][c][1] for n in names if solved(vt[n]["per_config"][c][0])]
            row.append("%d (%.1f s)" % (len(ts), sum(ts)))
        M.append("| %s | %s |" % (SHORT.get(c, c), " | ".join(row)))
    wrong = ["%s: %s" % (l, ", ".join(n for n in names if vt[n]["flags"])) for l, _, vt, _ in runs
             if any(vt[n]["flags"] for n in names)]
    M.append("")
    M.append("Wrong answers: %s." % ("; ".join(wrong) if wrong else "none"))
    M.append("")
    M.append("Runs: " + "; ".join("%s = cvc5 %s, %g s, %s runs at a time" % (
        l, v["cvc5_version"].split("[git ")[-1].split(" ")[0], v["timeout"], v.get("jobs", 1))
        for l, v, _, _ in runs) + ".")
    open(out_md, "w").write("\n".join(M) + "\n")

    # ---------------- LaTeX table ----------------
    os.makedirs(out_tex, exist_ok=True)
    tex = lambda l: l.replace("#", "\\#")
    T = []
    T.append("\\begin{tabular}{@{}ll" + "rl" * len(runs) + "@{}}")
    T.append("\\toprule")
    T.append(" & & " + " & ".join("\\multicolumn{2}{c}{%s}" % tex(l) for l, _, _, _ in runs) + " \\\\")
    T.append("benchmark & exp. & " + " & ".join("VBS & by" for _ in runs) + " \\\\")
    T.append("\\midrule")
    for n in names:
        best = min((vt[n]["vbs_time"] for _, _, vt, _ in runs if vt[n]["vbs_config"]), default=None)
        cells = []
        for _, v, vt, rt in runs:
            a = vt[n]
            if a["vbs_config"]:
                t = fmt(a["vbs_time"])
                t = "\\best{%s}" % t if a["vbs_time"] <= best * 1.05 + 0.01 else "\\good{%s}" % t
                cells.append("%s & %s" % (t, SHORT.get(a["vbs_config"], a["vbs_config"])))
            else:
                cells.append("\\tmo & ")
        T.append("%s & %s & %s \\\\" % (n, runs[0][2][n]["expected"] or "", " & ".join(cells)))
    T.append("\\midrule")
    T.append("solved & & " + " & ".join(
        "\\multicolumn{2}{l}{\\textbf{%d} of %d}" % (sum(1 for n in names if vt[n]["vbs_config"]), len(names))
        for _, _, vt, _ in runs) + " \\\\")
    T.append("\\bottomrule")
    T.append("\\end{tabular}")
    open(os.path.join(out_tex, "runs-table.tex"), "w").write("\n".join(T) + "\n")

    # ---------------- cactus ----------------
    C = []
    timeout = runs[0][1]["timeout"]
    C.append("\\begin{axis}[width=10cm, height=6.2cm, xmode=log, xmin=0.02, xmax=%g," % (timeout * 8))
    C.append("  xlabel={time (s), virtual best}, ylabel={benchmarks solved}, ymin=0, ymax=%d," % (len(names) + 1))
    C.append("  tick label style={font=\\scriptsize}, label style={font=\\scriptsize},")
    C.append("  legend style={font=\\scriptsize,at={(0.03,0.97)},anchor=north west}, legend cell align=left,")
    C.append("  grid=major, grid style={gray!20}]")
    labels = []
    for i, (l, v, vt, rt) in enumerate(runs):
        ts = sorted(vt[n]["vbs_time"] for n in names if vt[n]["vbs_config"])
        st = STYLES[i % len(STYLES)]
        C.append("\\addplot[thick,%s,mark size=1.5pt] coordinates {%s};" %
                 (st, " ".join("(%g,%d)" % (t, k + 1) for k, t in enumerate(ts))))
        C.append("\\addlegendentry{%s}" % tex(l))
        labels.append((ts[-1], len(ts), tex(l), st.split(",")[0]))
    C.append("\\draw[dashed,gray] (axis cs:%g,0) -- (axis cs:%g,%d) node[pos=0.04,left,font=\\scriptsize]{%g s};" %
             (timeout, timeout, len(names) + 1, timeout))
    used = {}
    for t, k, l, color in sorted(labels, key=lambda x: (x[1], x[0])):
        off = used.get(k, 0)
        used[k] = off + 1
        C.append("\\node[font=\\scriptsize,%s,anchor=west,xshift=3pt,yshift=%dpt] at (axis cs:%g,%d) {%s: %d};" %
                 (color, -8 * off, t, k, l, k))
    C.append("\\end{axis}")
    open(os.path.join(out_tex, "runs-cactus.tex"), "w").write("\n".join(C) + "\n")
    print(open(out_md).read())


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3:])
