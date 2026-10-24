"""Make the tables and the cactus plots from results.csv.

usage: python3 report.py [--timeout SECONDS]

The set reading and the bag reading of the benchmarks are reported separately,
since answers for one reading are not answers for the other. For each reading
this writes a table, summary-sets.csv / summary-bags.csv (and .md), and cactus
plots, cactus-sets.png / cactus-bags.png (and .pdf), next to this script.
Requires matplotlib.

Each figure has three cactus plots: the benchmarks solved, sat or unsat, and
those solved sat and unsat separately. In a cactus plot, time is on the x axis
(log scale) and the cumulative number of benchmarks solved is on the y axis:
the solved runtimes of each configuration are sorted and plotted as (t_i, i).
The timeout is a vertical line and each curve's final count is a direct label
at its right end.
"""
import argparse
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
# the time limit of the runs, set by --timeout
TIMEOUT = 5.0

# (configuration, name in the tables and plots, options). cvc5 (sets) is the
# sets solver of cvc5, cvc5 (bags) and cvc5 (bags + LIA*) encode the sets as
# bags and solve them with the bags solver of cvc5 and with its translation to
# LIA*, and SLS is sls-reachability.
READINGS = {
    "sets": [
        ("sets", "cvc5 (sets)", "`--sets-to-bags=none`"),
        ("sets-fmf", "cvc5 (sets), fmf-bound", "`--sets-to-bags=none --fmf-bound`"),
        ("setof-stock", "cvc5 (bags)", "`--sets-to-bags=setof --fmf-bound`"),
        ("setof-liastar", "cvc5 (bags + LIA*)", "`--sets-to-bags=setof --bags-to-liastar`"),
        ("sls-bapa", "SLS", "`lia_star_solver.py`"),
    ],
    "bags": [
        ("relaxed-stock", "cvc5 (bags)", "`--sets-to-bags=relaxed --fmf-bound`"),
        ("relaxed-liastar", "cvc5 (bags + LIA*)", "`--sets-to-bags=relaxed --bags-to-liastar`"),
        ("sls-mapa", "SLS", "`lia_star_solver.py --mapa`"),
        ("sls-mapa-unfold5", "SLS, unfolding", "`lia_star_solver.py --mapa --unfold=5`"),
        ("sls-mapa-nointerp", "SLS, no interpolation",
         "`lia_star_solver.py --mapa --no-interp`"),
    ],
}
TITLES = {
    "sets": "Sets: 240 BAPA benchmarks of the LIA* paper artifact, %g s limit",
    "bags": "Bags: the same benchmarks read as multisets (MAPA), %g s limit",
}

# chart chrome and ink
SURFACE = "#fcfcfb"
INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"
# the color of each name, the same in both readings, from the first slots of
# the categorical palette in their fixed order
COLORS = {"cvc5 (bags + LIA*)": "#2a78d6", "cvc5 (sets)": "#eb6834",
          "cvc5 (bags)": "#1baf7a", "SLS": "#eda100"}
# the plotted configurations of each reading
SERIES = {
    "sets": ["setof-liastar", "sets", "setof-stock", "sls-bapa"],
    "bags": ["relaxed-liastar", "relaxed-stock", "sls-mapa"],
}


def load():
    names = [name for configs in READINGS.values() for name, _, _ in configs]
    data = {name: [] for name in names}
    with open(os.path.join(HERE, "results.csv")) as fh:
        for row in csv.DictReader(fh):
            for name in names:
                answer = row[name + " answer"]
                if answer not in ("sat", "unsat", "unknown", "timeout"):
                    answer = "error"
                data[name].append((row["benchmark"], answer, float(row[name + " time (s)"])))
    return data


def summarize(data, reading):
    header = ["configuration", "options", "unsat", "sat", "unknown", "timeout",
              "error", "solved", "median time of solved (s)"]
    rows = []
    for key, name, options in READINGS[reading]:
        answers = [a for _, a, _ in data[key]]
        solved = [t for _, a, t in data[key] if a in ("sat", "unsat")]
        rows.append([name, options.strip("`")] + [answers.count(a) for a in
                                     ("unsat", "sat", "unknown", "timeout", "error")]
                    + [len(solved), "%.3f" % statistics.median(solved)])
    with open(os.path.join(HERE, "summary-%s.csv" % reading), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(header)
        w.writerows(rows)
    with open(os.path.join(HERE, "summary-%s.md" % reading), "w") as fh:
        fh.write("| Configuration | Options | unsat | sat | unknown | timeout | error"
                 " | solved | median time |\n")
        fh.write("|---|---|---|---|---|---|---|---|---|\n")
        for r in rows:
            fh.write("| %s | `%s` | %d | %d | %d | %d | %d | %d | %s s |\n" % tuple(r))


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


def panel(ax, data, answers, title, ymax, series):
    ax.set_facecolor(SURFACE)
    ends = []
    for key, color in series:
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
    ax.set_xlim(0.008, TIMEOUT * 2)
    ticks = [t for t in (0.01, 0.1, 1, 10, 100) if t < TIMEOUT]
    ax.xaxis.set_major_locator(FixedLocator(ticks))
    ax.xaxis.set_major_formatter(FixedFormatter(["%g" % t for t in ticks]))
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


def plot(data, reading):
    plt.rcParams["font.family"] = ["Helvetica Neue", "Helvetica", "Arial",
                                   "DejaVu Sans"]
    labels = {key: name for key, name, _ in READINGS[reading]}
    series = [(key, COLORS[labels[key]]) for key in SERIES[reading]]
    fig, axes = plt.subplots(1, 3, figsize=(15, 4.6), dpi=200)
    fig.patch.set_facecolor(SURFACE)
    # (answers counted, title, upper limit of the y axis)
    panels = [({"sat", "unsat"}, "Solved (sat or unsat)", 250),
              ({"sat"}, "Sat", 160),
              ({"unsat"}, "Unsat", 100)]
    ends = [panel(ax, data, answers, title, ymax, series)
            for ax, (answers, title, ymax) in zip(axes, panels)]
    handles = [Line2D([0], [0], color=c, linewidth=2) for _, c in series]
    leg = fig.legend(handles, [labels[k] for k, _ in series], loc="lower center",
                     ncol=len(series), frameon=False, fontsize=9, handlelength=1.8,
                     bbox_to_anchor=(0.5, 0.0))
    for text in leg.get_texts():
        text.set_color(INK2)
    fig.suptitle(TITLES[reading] % TIMEOUT, color=INK, fontsize=12, x=0.04,
                 ha="left", y=0.975)
    fig.subplots_adjust(left=0.045, right=0.99, bottom=0.2, top=0.83, wspace=0.18)
    # the labels are placed in display coordinates, hence after the layout
    for ax, e in zip(axes, ends):
        place_labels(ax, e)
    for ext in ("png", "pdf"):
        fig.savefig(os.path.join(HERE, "cactus-%s.%s" % (reading, ext)),
                    facecolor=SURFACE)
    plt.close(fig)


def main():
    global TIMEOUT
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--timeout", type=float, default=5.0,
                        help="the time limit of the runs in seconds")
    TIMEOUT = parser.parse_args().timeout
    data = load()
    for reading in READINGS:
        summarize(data, reading)
        plot(data, reading)


if __name__ == "__main__":
    main()
