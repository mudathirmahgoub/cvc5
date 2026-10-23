"""Make the tables and the cactus plot from results.csv.

usage: python3 report.py

Writes summary.csv and summary.md (one row per configuration) and cactus.png
and cactus.pdf next to this script. Requires matplotlib.

In the cactus plot, time is on the x axis (log scale) and the cumulative
number of benchmarks solved is on the y axis: the solved runtimes of each
configuration are sorted and plotted as (t_i, i). The timeout is a vertical
line and each curve's final count is a direct label at its right end.
"""
import csv
import os
import statistics

import matplotlib

matplotlib.use("Agg")
import matplotlib.patheffects as pe
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import FixedFormatter, FixedLocator, NullLocator

HERE = os.path.dirname(os.path.abspath(__file__))
TIMEOUT = 5.0

# (configuration, description in the tables, label in the plot)
CONFIGURATIONS = [
    ("sets", "cvc5, sets solver", "plain sets"),
    ("sets-fmf", "cvc5, sets solver, `--fmf-bound`", None),
    ("setof-stock", "cvc5, `--sets-to-bags=setof`, stock bags solver", "setof + stock bags"),
    ("relaxed-stock", "cvc5, `--sets-to-bags=relaxed`, stock bags solver", "relaxed + stock bags"),
    ("setof-liastar", "cvc5, `--sets-to-bags=setof --bags-to-liastar`", "setof + LIA*"),
    ("relaxed-liastar", "cvc5, `--sets-to-bags=relaxed --bags-to-liastar`", "relaxed + LIA*"),
    ("sls-bapa", "sls-reachability, BAPA", "sls-reachability BAPA"),
    ("sls-mapa", "sls-reachability, MAPA (`--mapa`)", "sls-reachability MAPA"),
    ("sls-mapa-unfold5", "sls-reachability, MAPA, `--unfold=5`", None),
    ("sls-mapa-nointerp", "sls-reachability, MAPA, `--no-interp`", None),
]
# Configurations whose sat answers are answers for the multiset reading of the
# benchmarks rather than for the sets.
MULTISET = {"relaxed-stock", "relaxed-liastar", "sls-mapa", "sls-mapa-unfold5",
            "sls-mapa-nointerp"}

# chart chrome and ink
SURFACE = "#fcfcfb"
INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"

# plotted series, in the fixed order of the categorical palette
SERIES = [
    ("setof-liastar", "#2a78d6"),
    ("relaxed-liastar", "#eb6834"),
    ("sets", "#1baf7a"),
    ("setof-stock", "#eda100"),
    ("relaxed-stock", "#e87ba4"),
    ("sls-bapa", "#008300"),
    ("sls-mapa", "#6250d6"),
]
LABELS = {name: label for name, _, label in CONFIGURATIONS}


def load():
    data = {name: [] for name, _, _ in CONFIGURATIONS}
    with open(os.path.join(HERE, "results.csv")) as fh:
        for row in csv.DictReader(fh):
            for name in data:
                answer = row[name + " answer"]
                if answer not in ("sat", "unsat", "unknown", "timeout"):
                    answer = "error"
                data[name].append((row["benchmark"], answer, float(row[name + " time (s)"])))
    return data


def summarize(data):
    header = ["configuration", "unsat", "sat", "unknown", "timeout", "error",
              "solved", "median time of solved (s)"]
    rows = []
    for name, description, _ in CONFIGURATIONS:
        answers = [a for _, a, _ in data[name]]
        solved = [t for _, a, t in data[name] if a in ("sat", "unsat")]
        rows.append([description] + [answers.count(a) for a in
                                     ("unsat", "sat", "unknown", "timeout", "error")]
                    + [len(solved), "%.3f" % statistics.median(solved)])
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(header)
        w.writerows(rows)
    with open(os.path.join(HERE, "summary.md"), "w") as fh:
        fh.write("| Configuration | unsat | sat | unknown | timeout | error | solved"
                 " | median time |\n")
        fh.write("|---|---|---|---|---|---|---|---|\n")
        for (name, _, _), r in zip(CONFIGURATIONS, rows):
            sat = "%d*" % r[2] if name in MULTISET and r[2] else str(r[2])
            fh.write("| %s | %d | %s | %d | %d | %d | %d | %s s |\n"
                     % (r[0], r[1], sat, r[3], r[4], r[5], r[6], r[7]))


def curve(rows, answers):
    times = sorted(t for _, a, t in rows if a in answers)
    return times, list(range(1, len(times) + 1))


def place_labels(ax, ends, gap_pt=12):
    """Label each curve end with its count.

    Ends whose labels would collide are grouped, and the labels of a group are
    stacked in a column right of its rightmost end, each joined to its end by
    a thin leader in the series color. Labels that would cross the timeout
    line are placed just right of it.
    """
    fig = ax.figure
    fig.canvas.draw()
    to_disp = ax.transData.transform
    to_data = ax.transData.inverted().transform
    pt = fig.dpi / 72.0
    pts = [(to_disp((x, y)), x, y, color) for x, y, color in ends]
    groups = []
    for e in sorted(pts, key=lambda e: e[0][0]):
        for g in groups:
            if any(abs(e[0][1] - o[0][1]) < gap_pt * pt
                   and abs(e[0][0] - o[0][0]) < 60 * pt for o in g):
                g.append(e)
                break
        else:
            groups.append([e])
    limit_x = to_disp((TIMEOUT, 0))[0]
    for g in groups:
        col_x = max(o[0][0] for o in g) + 7 * pt
        beyond = col_x + 22 * pt > limit_x - 3 * pt
        if beyond:
            col_x = limit_x + 5 * pt
        g.sort(key=lambda o: (-o[2], -o[1]))
        center = sum(o[0][1] for o in g) / len(g)
        for k, (disp, x, y, color) in enumerate(g):
            label_y = center + ((len(g) - 1) / 2.0 - k) * gap_pt * pt
            ax.plot([x], [y], marker="o", markersize=4, color=color,
                    markeredgecolor=SURFACE, markeredgewidth=1, zorder=4)
            if len(g) > 1 or beyond:
                lx, ly = to_data((col_x - 2 * pt, label_y))
                ax.plot([x, lx], [y, ly], color=color, linewidth=0.8, zorder=3)
            tx, ty = to_data((col_x, label_y))
            ax.text(tx, ty, str(y), color=INK2, fontsize=8.5, va="center",
                    ha="left", zorder=5,
                    path_effects=[pe.withStroke(linewidth=3, foreground=SURFACE)])


def panel(ax, data, answers, title, ymax, keys):
    ax.set_facecolor(SURFACE)
    ends = []
    for key, color in SERIES:
        if key not in keys:
            continue
        xs, ys = curve(data[key], answers)
        if not xs:
            continue
        ax.plot(xs, ys, color=color, linewidth=2, solid_capstyle="round",
                solid_joinstyle="round", zorder=2)
        ends.append((xs[-1], ys[-1], color))
    ax.axvline(TIMEOUT, color=MUTED, linewidth=1, zorder=1)
    ax.text(TIMEOUT / 1.06, ymax * 0.02, "%g s limit" % TIMEOUT, color=MUTED,
            fontsize=8, ha="right", va="bottom")
    ax.set_xscale("log")
    ax.set_xlim(0.008, 10)
    ax.xaxis.set_major_locator(FixedLocator([0.01, 0.1, 1]))
    ax.xaxis.set_major_formatter(FixedFormatter(["0.01", "0.1", "1"]))
    ax.xaxis.set_minor_locator(NullLocator())
    ax.set_ylim(0, ymax)
    ax.set_title(title, color=INK, fontsize=10.5, loc="left", pad=8)
    ax.set_xlabel("time per benchmark (s, log scale)", color=INK2, fontsize=9)
    ax.set_ylabel("benchmarks solved", color=INK2, fontsize=9)
    ax.grid(True, which="major", color=GRID, linewidth=0.8, linestyle="-")
    ax.set_axisbelow(True)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(AXIS)
        ax.spines[side].set_linewidth(0.8)
    ax.tick_params(which="both", colors=MUTED, labelsize=8, length=0)
    return ends


def plot(data):
    plt.rcParams["font.family"] = ["Helvetica Neue", "Helvetica", "Arial",
                                   "DejaVu Sans"]
    fig, (left, right) = plt.subplots(1, 2, figsize=(11, 4.6), dpi=200)
    fig.patch.set_facecolor(SURFACE)
    # only unsat answers carry over from the multiset reading to the sets
    ends_left = panel(left, data, {"sat", "unsat"},
                      "Solved with set semantics (sat or unsat)", 250,
                      {key for key, _ in SERIES if key not in MULTISET})
    ends_right = panel(right, data, {"unsat"}, "Proved unsat", 100,
                       {key for key, _ in SERIES})
    handles = [Line2D([0], [0], color=c, linewidth=2) for _, c in SERIES]
    leg = fig.legend(handles, [LABELS[k] for k, _ in SERIES], loc="lower center",
                     ncol=4, frameon=False, fontsize=9, handlelength=1.8,
                     bbox_to_anchor=(0.5, 0.0))
    for text in leg.get_texts():
        text.set_color(INK2)
    fig.suptitle("240 BAPA benchmarks of the LIA* paper artifact, %g s limit" % TIMEOUT,
                 color=INK, fontsize=12, x=0.055, ha="left", y=0.975)
    fig.subplots_adjust(left=0.06, right=0.985, bottom=0.24, top=0.83, wspace=0.16)
    # the labels are placed in display coordinates, hence after the layout
    place_labels(left, ends_left)
    place_labels(right, ends_right)
    for ext in ("png", "pdf"):
        fig.savefig(os.path.join(HERE, "cactus." + ext), facecolor=SURFACE)


def main():
    data = load()
    summarize(data)
    plot(data)


if __name__ == "__main__":
    main()
