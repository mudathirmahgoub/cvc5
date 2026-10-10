# Portfolio experiment scripts (temporary)

These scripts produced the results in rachelcleaveland/cvc5#9 (`rel.cyclic`) on the
litmus-template benchmarks of relational-solver-benchmarks. They are not part of cvc5:
**delete this directory (`git rm -r scripts`) before merging into cvc5 main.**

| file | what it does |
|---|---|
| `portfolio.py` | runs the seven configurations as a **virtual** portfolio (every configuration on every file, the fastest one counts) and as a **real** portfolio (all configurations started together per file, the first sat/unsat wins and the others are killed); writes `runs.json` and `summary.md` per mode |
| `configs-acyclic.json` | the same seven configurations for builds that know `rel.acyclic` (#7, #8): the rules also contain `--rels-acyclic-flatten-union` and `--rels-functional-axioms`, which this branch removed |
| `ablate.py` | reruns selected (file, configuration) pairs with extra options, to attribute a difference between two runs to an option |
| `compare_runs.py` | compares several runs: per file the virtual best of each run, solved files per configuration (markdown; LaTeX table and cactus plot) |
| `pr_report.py` | the charts (cactus plots with time on x, bar chart) and markdown tables of the PR description; needs matplotlib |
| `acyclic_to_cyclic.py` | converts SMT-LIB files from `rel.acyclic` to `rel.cyclic` |

Requirements: python3 (>= 3.8) and git; matplotlib for `pr_report.py`. Every command below runs
from the root of the cvc5 checkout.

## The configurations

| name | options (noFMF: the file without `:finite-model-find`) |
|---|---|
| default | as in the file |
| fmf-unsat (FMF) | `--e-matching --inst-when=full-delay --rels-acyclic-anchor=inclusion --rels-acyclic-backward-chords` |
| nofmf-unsat (noFMF) | `--rels-acyclic-anchor=inclusion --inst-when=full-delay --rels-acyclic-backward-chords` |
| stoponly | `--decision=stoponly` |
| fmf-unsat-rules (FMF+R) | FMF + R + `--rels-tc-down-lazy` |
| nofmf-unsat-rules (noFMF+R) | noFMF + R + `--rels-tc-down-lazy` |
| nofmf-unsat-hammer (noFMF+H) | noFMF + R + `--rels-acyclic-hammer` |

R = `--prenex-quant=none --rels-tc-subset`. A different set can be
given with `--configs-file` (JSON: `{name: {"opts": [...], "nofmf": bool, "desc": "..."}}`)
and a subset with `--configs`; `--benchmarks` restricts the files.

## Reproducing the results of #9

**1. This branch (`rel.cyclic`).** Build cvc5 as usual (`./configure.sh unrestricted
--auto-download && cd build && make`), then

```sh
python3 scripts/portfolio.py --cvc5 build/bin/cvc5 --workdir portfolio-work \
    --mode both --timeout 300 --jobs 6 --results results/cyclic-300s
```

The benchmarks are cloned into `portfolio-work/relational-solver-benchmarks` at the head of
relational-solver-benchmarks#2 (the `rel.cyclic` files). `--jobs 6` runs six virtual runs at a
time (the default, 1, runs them strictly one after another, which takes longer but gives
contention-free times). Without `--cvc5` the script clones and builds this branch in the work
directory.

**2. #8 and #7 (`rel.acyclic`).** Build their branches separately, then run them on the files
of relational-solver-benchmarks#1, with the configurations that include
`--rels-acyclic-flatten-union` and `--rels-functional-axioms`:

```sh
python3 scripts/portfolio.py --cvc5 /path/to/pr8/build/bin/cvc5 --workdir portfolio-work-acyclic \
    --benchmarks-rev f5efdad8e216bfa35549f038b8f6df83de36d35e \
    --configs-file scripts/configs-acyclic.json \
    --mode both --timeout 300 --jobs 6 --results results/pr8-300s
```

**3. Comparison, charts and tables.**

```sh
python3 scripts/compare_runs.py results/comparison.md results/tex \
    "PR #7=results/pr7-300s" "PR #8=results/pr8-300s" "rel.cyclic=results/cyclic-300s"
python3 scripts/pr_report.py results/report "rel.cyclic" \
    "PR #7=results/pr7-300s" "PR #8=results/pr8-300s" "rel.cyclic=results/cyclic-300s"
```

`pr_report.py` writes `cactus-runs.png`, `cactus-configs.png`, `solved-per-config.png`, one
`matrix-<run>.md` per run (every configuration on every file) and `virtual-real.md`.

**4. Where the differences come from.** Rerun #8 with the two witness forms that `rel.cyclic`
always uses on the pairs that differ:

```sh
B=portfolio-work-acyclic/relational-solver-benchmarks
python3 scripts/ablate.py --cvc5 /path/to/pr8/build/bin/cvc5 \
    --bench-dir $B/benchmarks-ltts --nofmf-dir $B/benchmarks-ltts-nofmf \
    --configs-file scripts/configs-acyclic.json \
    --extra="--rels-acyclic-flatten-union --rels-acyclic-self-loop" \
    --timeout 300 --jobs 6 --out results/ablate.json \
    plsc-2-th:nofmf-unsat-rules tso-1-th:nofmf-unsat tso-1-th-no-ltts:stoponly
```

## Converting files to `rel.cyclic`

```sh
python3 scripts/acyclic_to_cyclic.py FILE...                 # in place
python3 scripts/acyclic_to_cyclic.py --out-dir DIR FILE...   # copies
```

It rewrites `(rel.acyclic (tuple R1 ... Rk))` to `(not (rel.cyclic U))` and
`(not (rel.acyclic (tuple R1 ... Rk)))` to `(rel.cyclic U)`, with `U = R1` for `k = 1` and
`(set.union R1 (set.union R2 ... Rk))` otherwise, and removes the deleted options from
`; COMMAND-LINE:` lines.

## Output

`<results>/virtual/runs.json` and `<results>/real/runs.json` hold every run (answer, time,
command line; the real mode also the CPU time of all processes), `summary.md` the tables, and
`<results>/comparison.md` virtual versus real. The output of every cvc5 process is kept next
to them (`virtual/<config>/<file>.out`, `real/<file>/<config>.out`). Answers are checked
against the hand-verified expected results (`EXPECTED` in `portfolio.py`); a wrong or
disagreeing answer is flagged.
