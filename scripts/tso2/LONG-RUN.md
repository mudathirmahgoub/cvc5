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

* **Arithmetic does not falsify `l = c` from a lower bound `l >= K > c`.** It propagates bound atoms
  (`l >= j`) but falsifies an equality atom only when `l` is merged with a constant. Unate lemmas
  (`--unate-lemmas=all`, the default) would cover this, but they are generated before the search,
  and `cyclen_10` and its atoms are created during it.
* **The Distinct premise uses an equality atom:** `r <= l ∧ ¬(r = l)` instead of `r < l`.
* **The decision strategy is unbounded** (`mkLiteral(i)` always returns `l <= i+2`). Every decision
  is refuted during propagation, so the SAT solver never reaches a full assignment: no full-effort
  or last-call check runs, the relations solver sends no lemma, and nothing ever generalises
  `l >= K+1`.

## Fixes (not implemented yet)

1. Write the "not the closing element" premises with an inequality, `r < l` (an atom that
   arithmetic propagates at level 0), instead of `r <= l ∧ ¬(r = l)`. With it, `l >= 7` gives
   `s1 ≠ s_r` at level 0, and the conflict above becomes a level-0 conflict, i.e. unsat. Check the
   other rules whose premises contain `(= r l)` or `(not (= r l))` the same way.
2. Bound the length strategy: return no literal beyond the unrolled prefix (for example
   `i + 2 > |s| + 1`), so that the search reaches full effort and the unroll and minimality rules run
   between decisions.
3. In general: when the solver introduces integer terms during the search, their equality atoms
   need the unate implications (`l = c ⇒ l <= c ∧ l >= c`) that preprocessing adds only for input
   atoms.

Fix 1 is the direct one: the same propagations would then run at level 0, so this run should
have ended with unsat at about 8 h (not tested). It would not change
the 2.7 h needed to rule out ghb cycles up to 9 edges; `DECOMPOSITION.md` remains the fast route
(about 23 minutes).
