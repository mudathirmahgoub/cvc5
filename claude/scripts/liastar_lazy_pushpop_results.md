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

## Semantic generalization (option `--arith-liastar-generalize-semantic`, 2026-06-12)

Implemented as a follow-up to the boolean generalization: drop cell atoms
whose removal keeps the cell inside the predicate *arithmetically*, merging
cells the boolean skeleton cannot (e.g. a model-true equality `z = 1`
subsumed by a kept `z > 0` -- collapsing the family `z = 2, 3, ...` of
future cells).

Design (`LiaStarUtils::semanticGeneralize`): a persistent incremental probe
subsolver per lambda (in `Subsolver`/`MainEnum`, created by
`LiaStarExtension::getProbe`) is seeded once with the negated base
predicate; a literal subset implies the predicate iff checkSat with those
literals as assumptions answers unsat. Core-guided minimization: one
checkSat over all cell literals, the unsat-assumptions core drops everything
else at once, then a greedy deletion pass over the (small) core, equalities
first; any non-unsat probe answer conservatively keeps the literal, so the
result always implies the predicate.

Results: sound (0 discrepancies) and mechanically effective (paper2008
cells: ~45 tokens after boolean generalization -> ~25 after semantic), but a
**net loss on this benchmark set**: 465 solved (vs 466 for boolean
generalization alone; loses card/cvc5_mapa/fol_0000102, gains none) and
2.25x slower on the 465 common instances (883 s vs 392 s) -- the probe
queries plus the fatter cells (larger Hilbert bases, more multiplier skolems
per cone) cost more than the extra cell merging saves. On fol_0000100 the
counter-equality hypothesis was *refuted*: 358 rounds in 600 s (vs 838 for
boolean generalization), 3.63 GB, still timeout -- rounds got ~2.4x slower
and convergence stayed out of reach, so that instance's fine-grained cell
structure is not primarily subsumed equalities. Default stays **off**; raw
results in `claude/scripts/liastar_semantic_results.csv`, config in
comparison.csv / cactus plots as "cvc5 lazy (semantic)".

## fol_0000100 deep dive (2026-06-12): the bottleneck is the endgame, not discovery

Following the profiling advice, the failure is now precisely localized.

Facts established:
- The instance is **sat** (every other solver answers in < 1 s), but `A and
  p[v]` is **unsat** (verified standalone): the vector genuinely needs >= 2
  summands, so the star reduction is unavoidable. (The old "cvc5 lia" 0.02 s
  entry in comparison.csv does not reproduce with the current star encoding;
  eager mode also times out today.)
- The lambda is 14 indicator equations `u_i = ite(cond, 1, 0)` plus a
  min-tree; the A-constraints make v a counting vector (u!10 = n, etc.). A
  hand analysis shows a valid decomposition needs only ~4-6 summand
  bit-patterns (each u!10-summand "deficient" in exactly one counted bit, or
  using the f = UNIV escape bounded by t).
- A traced run shows the enumeration finds **all five needed deficiency
  patterns within the first ~60 rounds** (66 rounds: 66 distinct cells, 46
  decomposition candidates, Hilbert bases median 6 / max 32 vectors). Cell
  discovery is NOT the problem.
- The failure is the **main-solver endgame**: the solver must find integer
  multipliers decomposing v over the discovered cones (an ILP over hundreds
  of multiplier skolems), and it never gets to finish, because:
  (1) `checkFullEffort` runs *before* `sanityCheckIntegerModel`, so candidate
  models routinely carry fractional multipliers, fail the model-value
  shortcut, and trigger yet another refinement -- growing the ILP under the
  solver's feet every round; and
  (2) the star's fresh sum-equality atoms get default SAT phases, so the
  guard is *propagated false* from a false atom before ever being decided
  (the preferPhase on the guard alone never engages) -- measured: the guard
  is essentially never true at check time across 643 rounds.

Two more opt-in mitigations were implemented and tested (both sound, both
pass the regression suite, both default off, neither cracks the instance):
- `--arith-liastar-guided`: bound the subsolver's next cell componentwise by
  the candidate model's vector values (every summand of a nonnegative
  decomposition satisfies y <= v), as assumptions with an unbiased fallback.
  Shapes the cells correctly (the v-zero coordinates go to 0) but still
  times out (449 rounds / 600 s).
- `--arith-liastar-patient`: skip refinement while the current guard is
  asserted true (defer to integer branching), plus phase-bias the star
  conjuncts true so the solver actually commits to the reduction. The gate
  rarely engages (492-643 rounds) because early stars *genuinely* conflict
  with A until enough cones exist, and by then hundreds of stale frozen-true
  atoms from deactivated stars pollute the search.

Conclusion: incremental in-search refinement and the star endgame interfere
structurally. The most promising remaining direction is to **decouple the
endgame**: every R rounds, hand `input-assertions and star_k` to a fresh
dedicated subsolver snapshot (clean search, no stale guards/phases, b&b can
run to completion); a sat answer there yields concrete multiplier witnesses
that can be fed back (e.g. asserted as a model hint), and unsat-with-core
tells which constraints still lack cones. Alternatively, strengthen the ILP
itself on counting structures (cuts), which is beyond the liastar extension.


## Guided enumeration + decoupled endgame: fol_0000100 SOLVED (2026-06-12)

The decoupled-endgame proposal above was implemented and, combined with
guided enumeration and a decision-strategy feedback mechanism, **solves
fol_0000100 in 0.67 s** (from a 600 s timeout in every prior configuration,
model-checked) and nearly closes the whole benchmark set.

The chain, each step driven by a measured failure:

1. `--arith-liastar-guided`: bound the subsolver's next cell componentwise
   by the candidate model's vector (`y <= v`; sound since summands of a
   nonnegative decomposition cannot exceed the sum), as assumptions with an
   unbiased fallback. Without it, the enumeration provably wanders: the
   unsat-assumption core of the endgame query showed the unguided star could
   not supply enough u!20-summands even at 580 cones; with it, all needed
   patterns appear within ~30 cones.
2. `--arith-liastar-endgame=N`: every N new cones, a *fresh* subsolver
   solves `fixed-facts and star_k`, where fixed-facts are the arithmetic
   facts with `Valuation::isFixed` (entailed at level 0). The first version
   used all trail facts and was poisoned by branch decisions (the search's
   purify pins forced n = 1, a region already known contradictory); the
   isFixed filter is essential. With guidance the endgame turns **sat at 30
   cones** and produces a concrete multiplier witness.
3. Witness feedback: a guarded hint lemma `d => (x_1 = c_1 and ...)` alone
   never engages -- traced: the guard is propagated false in every round,
   since with hundreds of pinned variables some are always already bound
   differently on the trail. The fix is a cvc5 **decision strategy**
   (`LiaStarHintStrategy`, new id STRAT_ARITH_LIA_STAR_HINT): while a hint
   is active, the SAT solver is handed the guard and each pinned equality as
   its next decisions, building the witness assignment directly. One hint is
   active per literal (the previous guard is deactivated), since competing
   witnesses pin the same skolems to different values.

Benchmarks (480 instances, 100 s, production,
`--arith-liastar-guided --arith-liastar-endgame=10` on top of the defaults):

| config | sat | unsat | timeout | solved |
|---|---|---|---|---|
| lazy generalize (previous best) | 285 | 181 | 14 | 466 |
| **lazy guided+endgame** | **296** | **180** | **4** | **476** |

Zero answer discrepancies against the generalize config and against all four
recorded reference solvers (sls, cvc5 lia, unfold5, no_interp). It newly
solves the entire hard card/fol_99-106 family (several of which even the
reference SLS solver timed out on for the mapa encoding), loses only
card/cvc5_mapa/fol_0000098, and is faster on the common set (306 s vs
358 s). The four remaining timeouts are card/{bapa,mapa}/fol_0000098 and
fol_0000107. Raw results: `liastar_endgame_results.csv`; plotted as
"cvc5 lazy (guided+endgame)" in the cactus plots.

**Both flags are now the default** (`arith-liastar-guided` defaults to true,
`arith-liastar-endgame` defaults to 10), composing with the default boolean
generalization: a plain `cvc5` invocation runs the guided + endgame
strategy, and solves fol_0000100 in about a second. Disable with
`--no-arith-liastar-guided` / `--arith-liastar-endgame=0`. The
"cvc5 lazy (guided+endgame)" column/curve in the paper artifacts therefore
measures the current default configuration.

Notes for the future: the endgame check requires `produce-models` and reads
the witness over the star formula's symbols; `getUnsatCore` on the internal
endgame subsolver segfaults in debug (use `checkSat(assumptions)` +
`getUnsatAssumptions` instead, which also gives the more informative
fact-side core); the liastar-endgame / liastar-endgame-smt trace channels
dump the query and a replayable script.


## Over-approximation cuts: ALL 480 BENCHMARKS SOLVED (2026-06-12)

The four remaining timeouts (card/{bapa,mapa}/fol_0000098 and fol_0000107,
all unsat) needed the over-approximation half of the VMCAI 2020 approach,
implemented as `--arith-liastar-cuts` (default on):

- **Homogeneous cuts**: any inequality `c . y >= 0` valid for every point of
  the predicate is preserved under addition, hence valid for the whole star
  set, and can be asserted for the vector unconditionally
  (InferenceId ARITH_LIA_STAR_CUT).
- **Conditional cuts**: when a vector coordinate is the constant 0 (frequent
  -- input equalities are substituted into the literal), every summand is 0
  there too, so validity is only needed on that restriction of the
  predicate. The mapa/fol_0000107 refutation needs exactly such a cut
  (4 u!10 - u!14 - u!17 - u!20 - u!23 - u!26 >= 0 on the bits-zero
  restriction).
- **CEGIS synthesis** (`synthesizeCuts`/`synthesizeOneCut`), invoked when
  the endgame finds facts ^ star_k unsat: pick a target vector consistent
  with the fixed facts and cuts so far; solve for sparse integer
  coefficients (escalating L1 budget 4/9/16/30 -- an unconstrained box
  makes CEGIS thrash on dense candidates) nonnegative on all restricted
  sample points (module generators of discovered cones; CEGIS
  counterexamples) and negative on the target; validate against the
  restricted predicate via assumptions on a per-lambda validity subsolver.
  **Hilbert-basis rays must NOT constrain the search**: rays of
  unrestricted cells have zeros on pinned coordinates yet describe
  directions outside the restriction, and requiring nonnegativity on them
  excludes exactly the valid conditional cuts (a real bug, found by
  replicating the loop offline where it converged in 8 cuts / ~33
  iterations while the in-solver version failed).
- Once the cuts refute the fixed facts, the main solver derives unsat by
  itself -- cuts are ordinary lemmas, so no new soundness machinery.

Final results (480 instances, 100 s, all defaults:
generalize + guided + endgame=10 + cuts):

| config | sat | unsat | timeout | solved |
|---|---|---|---|---|
| old recorded lazy | 272 | 178 | 30 | 450 |
| guided+endgame (no cuts) | 296 | 180 | 4 | 476 |
| **final default (+cuts)** | **296** | **184** | **0** | **480** |

**480/480 solved, 143.5 s cumulative, median 45 ms, slowest instance
37.2 s (card/cvc5_bapa/fol_0000099).** Zero answer discrepancies against
every reference solver and every prior configuration. The four previously
impossible unsat instances refute in 0.2--2.0 s. Raw results:
`liastar_final_results.csv`; plotted as "cvc5 lazy (final: +cuts)".

A full LaTeX report covering all strategies, algorithms, soundness
arguments, and measurements: `liastar_lazy_report.tex` / `.pdf` (this
directory).

## Bug fix: constant-lambda predicates crashed the solver (2026-06-12)

Surfaced while constructing the report's "K too small" example. A
*constant* lambda such as `(lambda ((x Int)) (= x 31))` (a function true at
a single point) is canonicalized by the UF rewriter into a
`FUNCTION_ARRAY_CONST` node with zero children. `getVectorPredicate` and the
extension then indexed it as a syntactic lambda (`n[0][0]`), dereferencing a
0-child node -> segfault (reproduced in eager mode and every config, so
pre-existing, unrelated to the lazy/cut work).

Fix: convert the predicate argument back to a lambda with
`uf::FunctionConst::toLambda` at the two entry points --
`LiaStarUtils::getVectorPredicate` (covers the rewriter's constant-vector
optimization) and `LiaStarExtension::getAssertions` (rebuilds each collected
STAR_CONTAINS atom so all structural accesses see a lambda; the rebuilt atom
rewrites back to the asserted one, so the reduction lemma still attaches).
Regression test `const_lambda.smt2` (unsat). Verified: 9 regression tests +
the 4 hard benchmarks unchanged, unit test passes, debug build clean on the
repro.

## Report

`liastar_lazy_report.tex` / `.pdf` (19 pages): example-driven explanation of
every strategy, with TikZ figures for the cut geometry and CEGIS loop, five
pseudocode algorithms (lazy round, GeneralizeCell, Endgame, SynthesizeCuts,
SynthesizeOneCut), and a closing subsection on the limits of cuts:
cuts refute only outside the convex conic hull of the star set (parity-gap
example S={(2,0),(0,2)}, v=(1,1)), and the weight budget can be too small
for an existing cut (S={(1,31)}, v=(1,30) needs weight 32) -- both harmless
because the lazy enumeration remains a complete fallback.
