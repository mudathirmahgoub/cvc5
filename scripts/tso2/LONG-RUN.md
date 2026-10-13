# tso-2-th as one query: the 9-hour run and why it ran out of memory

The run: `tso-2-th.smt2` as a single query with the plain-edge witness (snapshot of this branch at
5e45d4bc57, release build with tracing), no time limit, the options of `README.md` plus
`--rels-cycle-plain-edges`. Started 2026-10-12 20:55 CDT, paused at 9 h 07 min, killed after the
investigation below. No answer.

## Timeline

| elapsed | event |
|---|---|
| 42 s - 2 h 43 min | ghb witness (`cyclen_181`): cycles up to 5, 6, 7, 8, 9 edges ruled out at 42 s, 157 s, 373 s, 1323 s, 9806 s |
| 3 h 13 min - 7 h 20 min | per-location witness (`cyclen_10`, `po-loc ∪ rf ∪ fr ∪ co`): up to 2, 3, 4, 5 at 11561 s, 12042 s, 15500 s, 26402 s |
| 8 h 02 min | resident memory 2.6 GB |
| about 8 h 05 min | memory starts growing by about 2 GB per minute |
| 9 h 05 min | footprint 135 GB (118 GB compressed, 23.6 GB swap) on a 64 GB machine; paused |

## What filled the memory

* `vmmap`: 2.88 billion live heap blocks, 140 GB, 49 bytes on average: small objects, no large
  arrays.
* CPU sample: most time in arithmetic, setting up new atoms
  (`TheoryArithPrivate::setupAtom`, `ArithCongruenceManager` → `EqualityEngine` →
  `normalizeEquality`), called from `DecisionStrategyFmf::getLiteral` → `ensureLiteral` and from
  `TheoryArith::preNotifyFact`.
* lldb on the paused process (printing the atoms with `NodeValue::toStream`): the atoms are
  `(>= cyclen_10 K+1)` and `(= cyclen_10 K)` for consecutive K, with K = 29,372,211 at the first
  look and 34,226,339 at the last. The cycle-length decision strategy (`--rels-cycle-len-decide`:
  `l <= 2`, `l <= 3`, ...) was enumerating the length of the per-location witness one integer at a
  time, about 8,000 values per second. The newest term node had id 4.1 billion.
* Per value of K, about 4.3 KB that is never freed (footprint 140 → 161 GB while K went from
  29.37 M to 34.23 M): 13 new term nodes (the two atoms, the constant, rewrites), two SAT variables
  (watch lists, variable data, activity, and the learned unit stays on the level-0 trail),
  CNF-stream maps, arithmetic constraints for both atoms (each arithmetic variable keeps a sorted
  map of all its constraints, so about 68 M constraints on `cyclen_10`), equality-engine nodes,
  explanation clauses, rewrite and preregistration caches.

## Why the walk never stops

lldb breakpoints on `TheoryEngine::conflict`, `TheoryEngine::lemma` and `Minisat::Solver::analyze`,
and a dump of the SAT trail (field offsets of `Minisat::Solver` from the headers, checked against
the disassembly), show one identical cycle per value of K:

1. The level-0 trail holds 34.28 M literals, nearly all of them learned units `cyclen_10 >= K`.
   The first decision is the strategy's literal `cyclen_10 <= K` (decision level 1), so arithmetic
   gets `cyclen_10 = K`.
2. Only now does arithmetic falsify the existing equality atoms `cyclen_10 = c`, c = 2..6, with
   explanations that contain the decision, e.g. `¬(l = 4) ∨ (l >= K+1) ∨ ¬(l >= K)`.
3. Through the Distinct lemmas of the witness (`applyContrMinimalRule`, case q = 1:
   `cyclic ∧ r <= l ∧ ¬(r = l) ⇒ s1 ≠ s_r`) these give `cyc_9 ≠ cyc_14`, `cyc_9 ≠ cyc_11285`, ...,
   then `¬rf(cyc_9, cyc_14)`, `¬co(...)`, `¬fr(...)` and so on: about 2,950 propagations in all.
   They end in a Boolean conflict on the same clause every time (clause reference 21989708):
   `¬(th0 = ⟨thread cyc_11114⟩) ∨ thread cyc_9 = thread cyc_11114 ∨ ¬(th0 = ⟨thread cyc_9⟩)`.
4. No theory conflict and no lemma is involved. The decision is the only literal at level 1, so
   conflict analysis learns the unit `cyclen_10 >= K+1`, backjumps to level 0, and the strategy
   proposes `cyclen_10 <= K+1`.

The conflict follows from `l ≠ 2`, ..., `l ≠ 6`, and these follow from `l >= 7`, which has been on
the level-0 trail all along. So the run had in fact refuted the per-location cycle at level 0
(that part is unsat in 29 s on its own), but did not see it. Three gaps combine:

* **Arithmetic does not falsify `l = c` from a lower bound `l >= K > c`.** Unate propagation of a
  new lower bound `l >= c+1` walks down the constraints of `l` and stops at the previous lower bound
  `l >= c`; the disequality `l ≠ c` sits at that same value, so it is skipped, although `l >= c+1`
  implies it (`l >= c` does not). A bound that rises one value at a time therefore never falsifies
  the equalities it passes (`unatePropLowerBound`, likewise for upper bounds and equalities in
  `constraint.cpp`). Unate lemmas (`--unate-lemmas=all`, the default) would also cover it, but they
  are generated before the search, and `cyclen_10` and its atoms are created during it.
* **The Distinct premise uses an equality atom:** `r <= l ∧ ¬(r = l)` instead of `r < l`.
* **The decision strategy is unbounded** (`mkLiteral(i)` always returns `l <= i+2`). Every decision
  is refuted during propagation, so the SAT solver never reaches a full assignment: no full-effort
  or last-call check runs, the relations solver sends no lemma, and nothing ever generalises
  `l >= K+1`.

## Fixes (implemented as options, off by default)

| fix | option | change |
|---|---|---|
| 1 | `--rels-cycle-lt-premise` | the Distinct premise "s_r is not the closing element" is `r < l` (a bound atom) instead of `r <= l ∧ ¬(r = l)` |
| 2 | `--rels-cycle-len-decide-bound` | the length strategy decides `l <= k` only for `k` at most one more than the number of unrolled elements; when that grows, the strategy resumes |
| 3a | `--arith-unate-prop-prev-diseq` | unate propagation of a new bound also implies the disequality at the value of the previous bound (lower bounds, upper bounds, equalities) |
| 3b | `--arith-unate-lemmas-search` | an equality atom created during the search gets the unate lemmas relating it to its nearest bounds (`l = c ⇒ l >= c'`, `l = c ⇒ l <= c''`), as presolve gives the input atoms |

Fix 3a on a 5-line example (`l >= 4`, then `l >= 5`, atom `l = 4`, `--no-arith-rewrite-equalities`
so that the equality atom stays): without the option the unate propagation of `l >= 5` stops next to
`¬(l = 4)`; with it, `l >= 5` implies `¬(l = 4)`.

A first version of 3b gave lemmas to every atom created during the search (bounds too). That
changed the integer and nonlinear search: three regress0 files (`nl/dd.sin-cos-346-b-chunk-0210`,
`proofs/issue12240-cyclic-proof`, `proofs/issue12631-check-proofs-arith`) went from at most 1.6 s to
timeouts (571 unate lemmas for branch-and-bound and nonlinear atoms in one of them). Restricted to
equality atoms, they are back to 0.0 to 1.6 s.

### Results (snapshot `v11`)

* **sc-2-th was stuck in the same loop.** With the configuration of `README.md` it times out; in 30 s
  it makes 467k conflicts for 714k decisions and grows to 2.6 GB. With any one of fix 1, fix 2 or
  fix 3 it is **unsat in 6.5 s** (fix 1: 108 conflicts, 87 MB).
* **The 15 benchmarks** (300 s, configuration of `README.md` plus the four options): all 12 unsat
  files are solved except `tso-2-th` (sc-2-th 6.1 s, plsc-2-th 8.9 s, tso-2-th-just-rf 2.8 s, the
  others at most 1.3 s); the 3 sat files time out as before (unsat-oriented configuration).
* **Relations regressions** (assertions build, the configuration plus the four options, with and
  without plain edges): no wrong answer, no assertion failure; 136 and 135 of 137. The others fail
  without the options too: `garbage_collect.cvc` (a type error with the flattening options, also
  with `v9`) and one hammer regression (timeout).
* **regress0 and the arithmetic regressions of regress1 and regress2** (2818 files, 1879 runs with an
  expected sat/unsat answer, assertions build, fix 3 options): no wrong answer, no assertion failure.
  The 59 runs without the expected answer: 51 need CoCoA or CryptoMiniSat (not in this build), 5 check
  printed output or reject expert options in safe mode, and 3 (`issue7984-quant-trans`: unknown,
  `miplib-opt1217--27` twice: timeout) do the same without the options.
* **The single query** is running again with the four options (`tso2/single-v11` of the analysis
  directory); see below when it ends.
