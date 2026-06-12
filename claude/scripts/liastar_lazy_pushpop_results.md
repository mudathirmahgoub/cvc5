# LIA* lazy subsolver: accumulate vs push/pop — changes and benchmark results

Date: 2026-06-11. Branch: `lazy`.

## Background

The lazy LIA* strategy keeps a persistent incremental subsolver per lambda to
enumerate the convex cells of the predicate. Originally it refined the
subsolver by asserting the negation of each discovered cone-disjunct, one
`assertFormula` per disjunct, accumulating assertions forever. Since each
round's refined formula `not(D_1 or ... or D_k)` subsumes the previous
round's, an alternative is to pop the previous refined formula and assert a
single cumulative one in a fresh frame, so the subsolver always holds exactly
two live assertions (the base predicate at user level 0 plus one refined
formula).

On the hard instance `fmcad26/sls-reachability/card/cvc5_bapa/fol_0000100.smt2`
(23 ites), push/pop did not rescue the run: an A/B on production builds
(600 s cap) showed both variants time out with nearly identical memory
(~3.27 GB old vs ~3.24 GB new, 988 vs 937 refinement rounds). The dominant
memory growth is shared by both variants and lives on the main-solver side:
each round emits `g_k => (literal = star_k)` where `star_k` spans all cones
found so far (cumulative lemma content is quadratic in rounds), and lemmas
are permanent. The cell enumeration also fails to converge in time (950+
rounds without exhausting the cells).

## cvc5 changes

- The pure push/pop version is saved as commit `26e3827638` on `lazy`
  ("make lazy subsolver use push/pop with a single cumulative refined
  formula"). That commit also fixes the production build: `!TraceIsOn(...)`
  does not compile when tracing is disabled, so the trace helpers in
  `liastar_utils.cpp` / `liastar_extension.cpp` are guarded positively.
- New option in `src/options/arith_options.toml`:
  `--arith-liastar-push-pop` (bool, default `false`).
  `LiaStarExtension::lazyCheckStar` branches on it; the `Subsolver` struct
  carries `covered`/`pushed` for the push/pop strategy and `negated` for both.
- The three user-selectable modes:

  | mode | options |
  |---|---|
  | eager | `--no-arith-liastar-lazy` |
  | lazy, accumulate assertions (default) | (none) |
  | lazy, push/pop | `--arith-liastar-push-pop` |

- Tests: all 9 `test/regress/cli/regress1/arith/liastar/` tests answer
  correctly in all three modes (production build), and the
  `arith_liastar_white` unit test passes.

## Benchmark verification

Setup: 480 instances (`fmcad26/sls-reachability/{arith,card}/{cvc5_bapa,cvc5_mapa}`,
120 each), 100 s timeout, production build (`build-prod`), 12 parallel
workers, `OMP_NUM_THREADS=1`. Results merged into
`paper-fmcad26-liastar/scripts/comparison.csv`.

Soundness: no sat/unsat answer disagrees anywhere — between the two new
configs, or against the previously recorded runs.

| config | sat | unsat | timeout | solved |
|---|---|---|---|---|
| old recorded "cvc5 lazy" | 272 | 178 | 30 | 450 |
| lazy accumulate (new) | **283** | **180** | **17** | **463** |
| lazy push/pop (new) | 280 | 180 | 20 | 460 |

Sat answers are verified faster than the previous recorded runs:

- On the 272 instances the old run answered sat, both new configs solve all
  272, faster on ~83% of them; cumulative time **107 s (accumulate) /
  99 s (push/pop) vs 319 s previously** (~3x faster).
- Accumulate newly solves 11 sat instances the old run timed out on
  (push/pop: 8). Both gain 2 extra unsat (180 vs 178).

Accumulate vs push/pop within the 100 s budget: **accumulate wins** — 3 more
sat solved (`card/cvc5_bapa/fol_0000049`, `card/cvc5_mapa/fol_0000048`,
`card/cvc5_mapa/fol_0000072`), nothing solved only by push/pop, and it is
faster on their common set (602 s vs 686 s cumulative over 280 common sat).
This matches expectation: push/pop re-preprocesses the cumulative refined
formula and discards the subsolver's learned clauses each round, and its
bounded-memory advantage only pays off on much longer horizons. Keeping
accumulate as the lazy default is the empirically right choice.

## Paper artifacts

- `paper-fmcad26-liastar/scripts/comparison.csv`: six new columns —
  `cvc5 lazy accumulate filename/result/duration` and
  `cvc5 lazy push-pop filename/result/duration` — joined per row on the
  benchmark path; old columns untouched.
- `paper-fmcad26-liastar/scripts/plot.py`: two new cactus-plot curves,
  "cvc5 lazy (accumulate)" (sky-blue `P`, dashed) and "cvc5 lazy (push-pop)"
  (magenta `X`, dashed); `cactus_plot.png`, `cactus_plot_sat.png`,
  `cactus_plot_unsat.png` regenerated. In the sat-only and overall plots the
  two new curves sit above all other solvers, including old cvc5 lazy and
  eager cvc5.

## Main-solver enumeration (option `--arith-liastar-main-solver`, 2026-06-11)

A third lazy variant that removes the per-lambda subsolver entirely: the
lambda's bound variables become fresh integer skolems `y` in the main solver,
and the cell enumeration runs inside the main search.

Design (see `MainEnum` in `liastar_extension.h`):

- Chained stage guards: `h_0 => base(y)`; per discovered cone-disjunct `D_k`
  a fresh `h_k` with `h_k => h_{k-1}` and `h_k => not(D_k(y))` — two
  constant-size lemmas per stage, accumulate style. The current `h_k`
  activates `base and not(D_1) ... and not(D_k)`, i.e. it places `y` in an
  uncovered cell, which is then read off the candidate arithmetic model.
- Driver lemma per (literal, stage): `literal => (p[v] or star_k or h_k)`,
  unguarded and satisfiability-preserving. An asserted-but-uncertified
  literal forces the solver into the enumeration branch itself; once every
  cell is covered the `h_k` branch closes by conflict, which is what lets
  unsat instances terminate (waiting for CDCL to fix `not(h)` at level 0
  alone livelocks). Completeness is additionally detected opportunistically
  via `Valuation::isFixed`, emitting the exact equivalence.
- All enumeration lemmas are re-queued every round; the user-context lemma
  cache drops duplicates and re-sends them after a user pop, so the
  non-context `MainEnum` state cannot get ahead of the asserted lemmas.

An adversarial review confirmed and led to fixing two soundness bugs before
the final version: (1) the driver lemma initially omitted the star branch
before the first cone, wrongly refuting literals whose only witness is the
empty sum (`v = 0` is always in the star set) — regression test
`empty_pred_sat.smt2`; (2) the enumeration lemmas were not re-sent after a
user-context pop, allowing wrong sat in incremental mode. Known remaining
(pre-existing, all modes): `d_processedStarTerms` is not user-context
dependent, so a literal fully reduced before a pop is never re-reduced.

Benchmarks (same setup: 480 instances, 100 s, production):

| config | sat | unsat | timeout | solved |
|---|---|---|---|---|
| old recorded "cvc5 lazy" | 272 | 178 | 30 | 450 |
| lazy accumulate (default) | 283 | 180 | 17 | 463 |
| lazy push/pop | 280 | 180 | 20 | 460 |
| lazy main-solver | 273 | 174 | 33 | 447 |

No answer discrepancies against any other config. The main-solver mode is
dominated by the subsolver modes on this set: accumulate solves 16 instances
(hard `card/` family) that it times out on, wins none back, and is ~2.5x
faster on the commonly solved set (252 s vs 639 s; sat-only 150 s vs 307 s).
It does still beat the old recorded runs on sat (300.6 s vs 319.3 s over the
272 common sat, faster on 215 of them). On the hard fol_0000100 it shows the
same ~3.1 GB / 600 s-timeout profile, with fewer rounds per minute (710 vs
988 accumulate). Interpretation: entangling the enumeration with the user
constraints makes every refinement round pay for the whole search, and one
cell is harvested at most per full-effort check; the dedicated subsolver
remains the better architecture for this workload. Raw results:
`liastar_mainsolver_results.csv` (repo root).

## Cell generalization and partial sums (options added 2026-06-11)

Both follow-up ideas are implemented as opt-in flags and benchmarked:

- `--arith-liastar-generalize` (`LiaStarUtils::generalizeCell`): after reading
  a cell from the model, greedily drop atoms the predicate's truth does not
  depend on (three-valued evaluation of the boolean skeleton; purely
  propositional, no solver probes), so each cone covers more of the
  predicate. Applied in both the subsolver path (`getDisjunct`) and the
  main-solver path (`getModelDisjunct`). Overlapping cells are fine: the
  Minkowski-sum decomposition only needs `S = union of cells`.
- `--arith-liastar-partial-sums`: per-cone multiplier constraints and running
  partial-sum definitions `P_k[i] = P_{k-1}[i] + contribution_k[i]` are
  asserted once as unguarded definitional lemmas (new inference id
  ARITH_LIA_STAR_DEFINITION), and the star formula becomes the constant-size
  `v = P_k`, dropping cumulative lemma content from quadratic to linear.

Benchmarks (480 instances, 100 s, production; no answer discrepancies
anywhere):

| config | sat | unsat | timeout | solved | time on acc-common set |
|---|---|---|---|---|---|
| lazy accumulate (baseline) | 283 | 180 | 17 | 463 | 1110 s (its own) |
| + generalize | **285** | **181** | **14** | **466** | **255 s (4.4x faster)** |
| + partial-sums | 272 | 178 | 30 | 450 | 659 s vs 242 s (2.7x slower) |
| + both | 280 | 180 | 20 | 460 | 513 s vs 819 s |

**Generalization is a clear win**: it strictly dominates the baseline — 3
more solved (card fol_0000048, mapa fol_0000098/102), none lost, and 4.4x
faster on the 463 commonly solved instances (it collapses the
previously-hard near-timeout solves). Disjunct sizes roughly halve (e.g.
paper2008: ~85-token cells become ~45 tokens). **It is now the default**
(`arith-liastar-generalize` defaults to true; disable with
`--no-arith-liastar-generalize`). It still does not crack fol_0000100
(838 rounds / 3.16 GB / 600 s timeout vs 988 / 3.27 GB baseline).

All three configurations are in `paper-fmcad26-liastar/scripts/`:
comparison.csv columns `cvc5 lazy generalize`, `cvc5 lazy partial-sums`,
`cvc5 lazy gen+partial-sums`, plotted in the cactus plots (regular and
zoomed). The partial-sums code is kept for now (option default-off, negative
result documented here); removal is deferred to a future commit.

**Partial-sums is a negative result**: it strictly loses — 13 fewer solved,
2.7x slower on the common set, and on fol_0000100 memory got *worse*
(4.38 GB vs 3.27 GB at 657 vs 988 rounds in 600 s). Two reasons measured:
(1) the per-cone definitional volume is large (~33 lemmas/round; 21,824
ARITH_LIA_STAR_DEFINITION lemmas on fol_0000100), so the linear term has a
big constant and the simplex tableau carries every P-chain row; (2) the
constant-size star `v = P_k` is a pure conjunction of equalities, so
negating it under the guarded equivalences forces disequality splitting
(ARITH_SPLIT_DEQ jumped 14 -> 663), where the old fat star offered cheap
escapes (violate a multiplier bound). The quadratic-lemma-content hypothesis
for the fol_0000100 memory wall is thereby refuted: the dominant cost is the
per-cone skolem/constraint volume itself, which is linear with a large
constant and unavoidable while the round count stays in the hundreds.

Raw results: `liastar_generalize_results.csv`,
`liastar_partialsums_results.csv`, `liastar_gen_psum_results.csv` (repo
root).

## Remaining ideas for fol_0000100-class instances

- The round count there is not driven by propositionally redundant atoms
  (generalization halves the cells but only trims rounds ~15%), so the cell
  structure is genuinely fine-grained: a *semantic* generalization (drop
  atoms whose removal keeps the cell inside the predicate arithmetic-wise,
  via cheap unsat probes) could merge cells the boolean skeleton cannot.
- Reducing the per-cone constraint volume (e.g. sharing multiplier skolems
  across module generators of one cone, or bounding the Hilbert basis size
  Normaliz is asked for) attacks the measured memory term directly.
