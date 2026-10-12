# tso-2-th, tso-2-th-just-rf: what stops cvc5 and what fixes it (working notes)

Hand proof: `PROOF.md`. Branch: `cycle-ext-tso2` (worktree `~/cvc5/rachel-tso2`), on top of
`cycle-ext-cyclic-proto` (rachelcleaveland/cvc5#11).

## Facts established by experiment

| experiment | result |
|---|---|
| the 7 portfolio configurations of #9, 300 s, both files | timeout |
| `nofmf-unsat-rules`, `nofmf-unsat-hammer`, 3600 s, both files | timeout |
| `not mcm` split: just-rf `cyc(rf)`; tso-2-th atomicity | unsat, 0.0 s / 0.1 s |
| `not mcm` split: just-rf `cyc(ghb)`; tso-2-th `cyc(ghb)`; tso-2-th SC per location | timeout |
| just-rf, explicit cycle with 2 / 3 / 4 `rfe` edges instead of `cyc(ghb)` | unsat, 0.2 s / 2.6-3.7 s / 6.4-10.5 s |
| just-rf, explicit witness prefix `s1..s5` with the Chord/Backward/Distinct constraints | unsat, 0.1 s (lazy) |
| just-rf `cyc(ghb)` keeping only the 3 templates of the proof (`jrf-B3-min`) | timeout |

So the templates and the minimality reasoning are fast; the **search for the witness** is what
fails.

## Why the witness search fails (traces of the tracing build)

1. **The witness is reset by backtracking.** `d_cycle_sequences` is SAT-context dependent and full
   effort adds one element per round. Conflicts unrelated to the cycle backtrack below the
   rounds that unrolled `s3, s4, …`, so the witness keeps restarting at `s2`: in 60 s it reached
   5 elements twice (`U2 U2 U2 … U3 … U4`).
2. **The unrolled witness starves the quantifiers.** With the prefix kept, the witness grows
   every round (196 elements in 60 s), every round sends a new lemma, and with
   `--inst-when=full-delay` no instantiation round ever comes: no conflict at all.
3. **The flattened operands do not match the templates.** `ghb = ppo ∪ com;sm` is flattened into
   the five components of `ppo` plus `com;sm`; witness edges are in `TC(component)`, the templates
   speak about `TC(ppo)`. Making `ppo` a declared constant is worse: closure induction then no
   longer sees `ppo ⊆ TC(po)` (the self-loop `(s1, s1) ∈ TC(ppo)` times out instead of 0.0 s).
4. **Quadratic lemma volume.** `po` totality is instantiated for every pair of same-thread
   events, so `TC(po)` gets a member for almost every pair; `TCLOSURE_UP` then sends one lemma per
   path prefix with the whole path as explanation, also for pairs that are already members
   (154k lemmas per minute). Products (`Event × Event` in `irreflexive`, `int`, `ext`) are
   composed eagerly for all pairs (46k `PRODUCE_COMPOSE` lemmas per minute).

5. **`co;sm` closures.** Distributing `(rfe ∪ fr ∪ co);sm` into `rfe;sm`, `fr;sm`, `co;sm` (keep-tc
   flattening) makes the closures simple, but `(s, s) ∈ TC(co;sm)` (witness length 2) is refuted only
   by closure induction with `co;sm ⊆ co`, which needs `sm ⊆ iden`, a quantified fact. Without it
   TC-Down descends forever along `co` chains. A plain `ensureLiteral` + `preferPhase` on the subset
   atom is not enough: the justification heuristic never decides an atom that no clause contains;
   a `DecisionStrategySingleton` is.

## Prototype options (all off by default)

| option | problem | change |
|---|---|---|
| `--rels-cycle-keep-prefix` | 1 | remember the longest prefix (user context); continue from it after backtracking: its elements are the same cached skolems and its lemmas are permanent |
| `--rels-cycle-len-decide` | 2 | decision strategy `l ≤ 2`, `l ≤ 3`, … (from #11) |
| `--rels-cycle-unroll-guard` | 2 | do not unroll when `c < l` is false (from #11): with the decisions, rounds become quiet |
| `--rels-cycle-flatten-top` / `--rels-cycle-flatten-keep-tc` | 3 | operands `[ppo, com;sm]`: only the top-level union, or flatten but keep a union `X` whose `TC(X)` is a term |
| `--rels-tc-up-skip-known` | 4 | no TCLOSURE_UP (and join/product composition) lemma for a tuple already in the relation |
| `--rels-product-lazy` | 4 | no product composition; at last call an incomplete product makes the model unsound (`unknown`), or, with `--rels-product-lazy-compose`, its missing members are composed then |
| `--rels-tc-subset-split` | 5 | for `TC(X;Y)`, a decision strategy decides `X;Y ⊆ X` (`X` transitive) or `X;Y ⊆ TC(X)`, true first, so that closure induction applies: `TC(co;sm) ⊆ co`, `TC(fr;sm) ⊆ TC(fr) = fr`, `TC(rfe;sm) ⊆ TC(rfe) ⊆ rf` |

## Results so far

| problem | options | result |
|---|---|---|
| `jrf-B3-min` | keep-prefix, len-decide, guard, flatten-top, product-lazy | unsat, 247 s (154k TC-Up lemmas) |
| `jrf-B3-min` | + skip-known | **unsat, 90 s** (6k TC-Up lemmas) |
| just-rf `cyc(ghb)` (all templates) | all six | **unsat, 160 s** |
| just-rf `cyc(ghb)`, keep-tc flattening | all | **unsat, 175 s** |
| tso-2-th SC per location | all, keep-tc | **unsat, 38 s** |
| `jrf-B3-min`, products completed at last call (`v2`) | all, keep-tc | **unsat, 84 s** |
| ablation on `jrf-B3-min` without keep-prefix | | unsat, 287 s |
| ablation without product-lazy / without len-decide + guard | | timeout (600 s) |
| full just-rf file | all (`v1`) | timeout (1200 s): 396k TC-Up lemmas, 16M decisions, 8 unrolls |
| tso-2-th `cyc(ghb)` | all (`v1`, top or keep-tc) | timeout (1200 s) |
| `(s1, s1) ∈ TC(co;sm)` on `t2-B3-min` | without / with the subset split | timeout / **unsat, 0.7 s** |
| tso-2-th-just-rf `cyc(ghb)`, `v7` (subset split generalised, products checked) | all | **unsat, 1.9 s** |
| **`tso-2-th-just-rf.smt2`** (the benchmark), `v7` | all | **unsat, 2.5 s** |
| tso-2-th `cyc(ghb)` (minimal and full), `v7` | all | timeout (1800 s); the witness reaches 6 elements |

## All 15 benchmarks with the new configuration (300 s, 5 at a time)

`nofmf-unsat-rules` + keep-prefix, len-decide, unroll-guard, flatten-keep-tc, product-lazy,
product-lazy-compose, tc-up-skip-known, tc-subset-split (`v8`):

| benchmark | result | #9 portfolio |
|---|---|---|
| plsc-1-th, plsc-1-th-just-rf, sc-1-th, sc-1-th-just-rf, sc-2-th-just-rf, tso-1-th, tso-1-th-just-rf | unsat, ≤ 1.1 s | solved |
| plsc-2-th | unsat, 10.8 s | 53-79 s |
| plsc-2-th-just-rf | unsat, 0.4 s | solved |
| **tso-2-th-just-rf** | **unsat, 2.9 s** | unsolved |
| sc-2-th | timeout | 3.8 s (`nofmf-unsat-hammer`) |
| tso-2-th | timeout | unsolved |
| the three `no-ltts` (sat) | timeout (unsat-oriented configuration) | solved by FMF configurations |

Without `--rels-product-lazy-compose` the result is the same except plsc-2-th-just-rf: `unknown`
(a quiet last call with an incomplete product). Relations regressions with the new options: no
wrong answer; `unknown` on 7 regressions that need product composition (without `-compose`).

## tso-2-th: what remains

* `not mcm` is three violations. Atomicity: unsat 0.1 s. SC per location (`cyc(po-loc ∪ rf ∪ fr ∪ co)`):
  **unsat 29 s** with the new configuration. `cyc(ghb)`: open.
* `cyc(ghb)` with the new configuration: the witness has four operands (`ppo`, `co;sm`, `fr;sm`,
  `rfe;sm`); lengths up to 5 are refuted within a minute, then the search stays at length 6
  (30-minute runs, minimal and full template sets, lazy or hammer, with or without length
  decisions, any `--decision` mode: all time out).
* Every single cycle shape is quick: explicit cycles `ppo;co;rfe;ppo;fr`, `ppo;co;rfe;ppo;co;rfe`,
  `ppo;fr;rfe;ppo;fr;rfe` (3 and 4 communication edges, beyond the templates, refuted by the run
  argument of `PROOF.md`) are unsat in about 1 s each.
* So the cost is the **number of shapes**: with four operands, every edge of the witness is a
  choice among four closures, and the proof bounds the length only at about 10 edges (five
  pairwise non-adjacent elements contain three of one thread; three such elements in `po` order
  `x < y < z` force `x ∈ W, y ∈ R` and `y ∈ W, z ∈ R`, a contradiction, so `l ≥ 11` is refuted by a
  prefix). For just-rf the witness has two operands, so it strictly alternates and has one
  shape per length.
* Removing the quantified `co` totality and the definition of the initial reads (not used by the
  proof of Theorem B) does not help.
* The full `tso-2-th` with the new configuration, lazy split or hammer: timeout at 3600 s.
* Two operands (`--rels-cycle-flatten-top`) or the default full flattening on the minimal problem:
  timeout at 1200 s. All `--decision` modes: timeout at 300 s.
* The assertions build agrees on the solved files (`tso-2-th-just-rf` unsat in 4.5 s) and on the
  relations regressions (137 runs, no wrong answer, 2 timeouts, no assertion failure).

Ideas not tried yet:
1. A witness rule for the pigeonhole argument: three pairwise non-adjacent witness elements
   related by a total order (here `po+` restricted to a thread) must contain a chord; this needs a
   notion of "total on a class", which `rel.cyclic` does not have today.
2. Fewer operands for the communication edges (`(fr ∪ co);sm` is transitive given `fr;co ⊆ fr`),
   which needs the solver to prove `fr;co ⊆ fr` from the definition of `fr`.
3. Proving the run lemma of `PROOF.md` once (as an SMT query) and adding it as a template-like
   assertion, which would change the benchmark, not the solver.
