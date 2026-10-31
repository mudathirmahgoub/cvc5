# PR cvc5/cvc5#12831 (liastar7 @ 82618b5c1) vs the FMCAD26 paper logs

Run on 2026-10-31 on the fmcad26 benchmarks (509 int.star-contains files).

- PR head: `~/cvc5/liastar7/build-unrestricted/bin/cvc5`, static unrestricted build of
  82618b5c1 (`configure.sh unrestricted --normaliz --gpl --static`), assertions and
  tracing off, Normaliz on.
- Paper binary: `bin/cvc5-static-mac-arm64` (liastar@dcd2c3110, the binary of the
  paper's logs), rerun under identical conditions as a timing control.
- CLI runs, `--tlimit=100000`, 8 benchmarks in parallel (run_bench.py), so
  per-benchmark times are slower than the paper's sequential python-API logs.
- Files: results.csv (raw), cactus.png, scatter.png, analyze.py (comparison with
  output/*_cvc5*.csv), run_bench.py (runner).

- paper log (Aug 2026, liastar@dcd2c3110): 509 results
- paper binary rerun today: 509 results
- PR head 82618b5c1: 509 results
- PR head, --arith-liastar-assume-nonnegative: 509 results

## Solved per family (100 s limit)

| family | n | paper log (Aug 2026, liastar@dcd2c3110) | paper binary rerun today | PR head 82618b5c1 | PR head, --arith-liastar-assume-nonnegative |
|---|---|---|---|---|---|
| bapa_arith | 120 | 120 | 120 | 120 | 120 |
| bapa_card | 120 | 104 | 104 | 104 | 104 |
| mapa_arith | 120 | 120 | 120 | 120 | 120 |
| mapa_card | 120 | 110 | 110 | 111 | 111 |
| sql | 29 | 29 | 29 | 29 | 29 |
| total | 509 | 483 | 483 | 484 | 484 |

## Outcomes

| run | sat | unsat | unknown | timeout | error | PAR-2 (s) |
|---|---|---|---|---|---|---|
| paper log (Aug 2026, liastar@dcd2c3110) | 284 | 199 | 0 | 26 | 0 | 5521 |
| paper binary rerun today | 284 | 199 | 0 | 26 | 0 | 5614 |
| PR head 82618b5c1 | 285 | 199 | 0 | 25 | 0 | 5374 |
| PR head, --arith-liastar-assume-nonnegative | 285 | 199 | 0 | 25 | 0 | 5387 |

## Paper log vs PR head

- compared benchmarks: 509
- sat/unsat disagreements: 0
- solved only in the paper log: 0
- solved only by the PR head: 1 (card/cvc5_mapa/fol_0000071.smt2)
- on the 483 benchmarks solved by both: total time 321.0 s -> 321.9 s, median per-benchmark ratio 1.12

## Paper log vs paper binary rerun

- compared benchmarks: 509
- sat/unsat disagreements: 0
- solved only in the paper log: 0
- solved only by the paper binary rerun: 0
- on the 483 benchmarks solved by both: total time 321.0 s -> 413.5 s, median per-benchmark ratio 2.14

## Paper nonneg log vs PR head nonneg

- paper nonneg log solved 483, PR head nonneg solved 484, sat/unsat disagreements: 0
