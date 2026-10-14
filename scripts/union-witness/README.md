# Cycle witnesses over unions: notes and a prototype (temporary)

These notes and the prototype on this branch answer two review questions about `rel.cyclic`
over a union `R = R1 ∪ … ∪ Rk`:

1. Why is there no rule `(rel.cyclic R) ⇒ (s, s) ∈ TC(R)` for a union, as there is for a
   relation that is not a union?
2. What does the solver do when two predicates have unions that are equal but written with
   different operands, `R1 ∪ … ∪ Rk` and `P1 ∪ … ∪ Pn`?

While answering them we found a third problem, which predates this work: a trivially
satisfiable union cycle does not terminate.

The prototype adds three expert options, **all off by default**, so the default behaviour of
the branch is unchanged. **Delete this directory and the options before merging into cvc5
main**, or keep only what the discussion below decides.

| option | what it does |
|---|---|
| `--rels-cycle-def-union` | for `(rel.cyclic R)`, `R` a union, also send `(rel.cyclic R) ⇒ (s1, s1) ∈ TC(R)`, with `s1` the first element of the witness |
| `--rels-cycle-len-decide` | a decision strategy that decides `l ≤ 2`, `l ≤ 3`, … for the length `l` of every witness |
| `--rels-cycle-unroll-guard` | at full effort, do not unroll a witness `s1..sc` when `c < l` is false in the current assignment |

## 1. What the solver does for `rel.cyclic` over a union

`applyInstCycleRule` collects the operands of the predicate's argument after rewriting
(`collectUnionOperands`). The witness `s1, s2, …` and its length `l` are keyed by that operand
list (`d_cycleAtoms`, `d_cycle_sequences`); the skolems are cached by the union of the operands.
So the witness follows what the input wrote:

| case | what happens | example (`examples/`) | result |
|---|---|---|---|
| same operands, different nesting: `A ∪ (B ∪ C)`, `(A ∪ B) ∪ C` | **Same-Operands**: the second atom implies the first; one witness | regression `cyclic-same-operands*.smt2` | — |
| commuted operands: `A ∪ B`, `B ∪ A` | the rewriter gives both the same normal form: one atom | `e5-commuted`: `cyc(A∪B) ∧ ¬cyc(B∪A)` | unsat, 0.01 s, every configuration |
| different operands, equal in the current context: `A ∪ B = C ∪ D` asserted | `rel.cyclic` is a congruence kind of the sets equality engine (`theory_sets.cpp`), so the two atoms are in one equivalence class | `e2-congruence`: `cyc(A∪B) ∧ ¬cyc(C∪D)` | unsat, 0.01 s, every configuration |
| both asserted true, equal unions | **two witnesses**, two lengths, each unrolled every round | `e1-two-witnesses` | 2 Inst-Cycle lemmas; see section 3 for why it does not terminate |
| equal only semantically (not in the equality engine) | the atoms are not merged; only the rules can find a contradiction | — | — |

Two witnesses for equal unions are **not unsound**: each witness is satisfiable on its own
(section 2.2), and in a model both may lie on the same cycle. They are redundant work. One
witness per equivalence class of the relation would remove it (keep the witness of the first
atom whose relation is in the class); this is not implemented, and it would have to pick one
decomposition into operands.

## 2. The definition of `rel.cyclic` for unions (`--rels-cycle-def-union`)

### 2.1 The rule

```
  (rel.cyclic R)    R = R1 ∪ … ∪ Rk
  ---------------------------------  CYCLE-DEF-UNION
         (s1, s1) ∈ TC(R)
```

`s1` is the first element of the witness of `R` (the skolem cached for `(R, 1)`), not a fresh
element. The rule is stated on the **union** `R`, the argument of the predicate as written,
never on one operand.

### 2.2 Soundness

The witness lemmas are satisfiable by extending any model `M` of the input: if `R` is cyclic in
`M`, take a shortest cycle of `TC(R1) ∪ … ∪ TC(Rk)` with `L − 1` edges, set `l := L` and put
`s1, …, sL` along it (`sL = s1`). Every edge of that cycle is in some `TC(Rj) ⊆ TC(R)`, so
`(s1, s1) ∈ TC(R)` holds in the same extension; if `R` is not cyclic, the premise is false.

The rule must not be stated for one operand: for `l ≥ 3`, **Chord** with `(q, r) = (1, l)`
says `(s1, sl) = (s1, s1) ∉ TC(Rj)` for every operand `Rj`. A self-loop of `s1` in one `TC(Rj)`
would be a cycle with one edge, shorter than the witness. So `(x, x) ∈ TC(R1 ∪ … ∪ Rk)` is
safe, `(x, x) ∈ TC(Ri)` is not.

### 2.3 Why the witness alone is not enough

Logically the witness implies the membership: its edges are in `TC(R1) ∪ … ∪ TC(Rk)` and
`sl = s1`. But the solver derives `(s1, s1) ∈ TC(R)` only after the witness closes, that is
under `l = N` for one particular `N`: **Split-Len**`N` gives `sN = s1`, and the edges must be
moved from `TC(Rj)` into `TC(R)` (TC-Down to the members of `Rj`, then the members of the
union, then TC-Up on `TC(R)`, if `TC(R)` is a term at all). Every refutation is therefore a
refutation of one length, and `l` is unbounded.

`examples/e3-transitive-superset.smt2` (also the regression
`cyclic-union-def-transitive-superset.smt2`):

```smt2
(assert (set.subset (set.union A B) H))
(assert (set.subset (rel.join H H) H))     ; H is transitive
(assert (not (rel.cyclic H)))
(assert (rel.cyclic (set.union A B)))      ; unsat: a cycle of A ∪ B is one of H
```

| | `#9` | with `--rels-cycle-def-union` |
|---|---|---|
| `e3` (union) | timeout (10 s) in all four configurations | **unsat, 0.01 s** with `--rels-tc-subset` (eager, lazy or hammer); timeout without it |
| `e4` (the same with a single relation `A`) | unsat, 0.01 s with `--rels-tc-subset`; timeout without it | the same |

With the rule, **TC-Subset** turns `(s1, s1) ∈ TC(A ∪ B)` into `(s1, s1) ∈ H` (the union is
included in the transitive `H`), and **Register** and **Acyclic-Down** on `¬cyc(H)` give
`s1 ≠ s1`: no length is involved. Without `--rels-tc-subset` both `e3` and `e4` time out.

The membership is also shared with every union equal to `R` in the equality engine: `TC(R)` and
`TC(P)` are congruent when `R = P`.

### 2.4 Cost

The new membership `(s1, s1) ∈ TC(R)` is a closure membership like any other:

* **eager TC-Down** (the default) splits it at once, with fresh elements, and keeps splitting:
  a second, unstructured unrolling of the same cycle next to the witness. The regression
  `acyclic-ltts-sc-1-th.smt2` (`--e-matching --inst-when=full --rels-acyclic-anchor=inclusion
  --rels-acyclic-backward-chords`) goes from **unsat in 0.8 s to a timeout at 120 s**;
* **lazy** (`--rels-tc-down-lazy`) and **hammer** (`--rels-acyclic-hammer`) do not split it at
  full effort. At last call the witness's own edges already explain it (a path from `s1` to
  `s1` through the members of `R`), so it adds no element. No lazy or hammer regression changed
  its answer or timed out with the option.

On the 13 litmus-template benchmarks (section 5) the rule neither adds nor loses a benchmark
in `nofmf-unsat-rules` (lazy split) and `nofmf-unsat-hammer` (10 → 10, 3 → 3);
`fmf-unsat-rules` (finite model finding, lazy split) loses `tso-1-th`, which `#9` solves in
266 s, close to the limit (12 → 11). None of these benchmarks needs the rule: it pays off on problems like `e3`,
where a union is included in a transitive relation.

### 2.5 Recommendation

Add the rule to the calculus, and send it only when the closure split is lazy or skipped
(`--rels-tc-down-lazy`, `--rels-acyclic-hammer`): the configurations that use closure
induction, which is where it pays off. Before making it the default there, look at
`tso-1-th` under `fmf-unsat-rules` (266 s on `#9`, a timeout with the rule).

On uniformity (a reviewer may ask why unions get a witness sequence and single relations do
not): with this rule **Cycle-Def** applies to every relation. For a single relation, TC-Down
on `(s, s) ∈ TC(R)` builds the path; for a union, the witness is TC-Down specialised to the
operands (one operand per edge, consecutive edges in different operands, minimality), and it
comes in addition to the definition.

## 3. A pre-existing divergence: trivially satisfiable union cycles

`examples/e0-one-witness.smt2` is only `(assert (rel.cyclic (set.union A B)))`, satisfiable
with `A = {(a, a)}`. It **times out in every configuration** of `#9`, also with `Int` elements
(`e0-int`), and the same problem with `(not (rel.acyclic (tuple A B)))` times out on `#8` and
on `cycle-ext` (merged with main). Finite model finding solves it, and so does a single
relation (`single.smt2`: `(rel.cyclic A)` is sat at once, except under the hammer, which is
meant for unsat problems).

**Cause** (found with temporary debug output in `doCycleInference` and
`checkAcyclicityLastCall`): the last call does run, but every candidate model gives `l` the next
value:

```
unroll? c=2 atom=(>= cyclen_3 3) has=1 val=1    full effort: the SAT value of 2 < l is true
unroll? c=2 atom=(>= cyclen_3 3) has=1 val=1
unroll? c=2 atom=(>= cyclen_3 3) has=1 val=1
lastcall c=3 l=4                                 last call: complete the witness to 4
unroll? c=2 atom=(>= cyclen_3 3) has=1 val=1    after backtracking: re-unrolled, quiet
unroll? c=2 atom=(>= cyclen_3 3) has=1 val=1
lastcall c=3 l=5                                 the next candidate model has l = 5
...
lastcall c=3 l=12
```

(The instrumentation is not in the branch.)

Each last call completes the witness to the new length with new lemmas (new atoms such as
`l = N`), the SAT solver backtracks, and the next candidate model moves `l` one further. Nothing
makes the search prefer a short cycle.

**`--rels-cycle-unroll-guard`** (do not unroll when `c < l` is false) has no effect: `c < l`
stays true.

**`--rels-cycle-len-decide`** registers a decision strategy for every witness length, in the
finite-model-complete group of the decision manager (`STRAT_SETS_CYCLE_LEN`, next to the length
strategy of strings): the SAT solver decides `l ≤ 2`, then `l ≤ 3`, … before its own decisions.
Decisions add no lemma, so they cannot change an answer, only the search.

| | `#9` | with `--rels-cycle-len-decide` |
|---|---|---|
| `e0-one-witness`, `e0-int`, `e0b-one-atom-equal`, `e1-two-witnesses` | timeout, every configuration | **sat in at most 0.04 s** with eager, lazy and closure-induction configurations; `--check-models` passes. Under the hammer `e0` and `e0-int` are sat, `e0b` and `e1` still time out |
| regression `acyclic-ltts-plsc-2-th-just-rf-isf.smt2` (lazy, unsat) | unsat, 0.3 s | **timeout at 300 s** |

On the 13 litmus-template benchmarks (section 5) it costs unsat proofs: `nofmf-unsat-rules`
solves 7 instead of 10 (loses `plsc-2-th`, `plsc-2-th-just-rf`, `sc-2-th`); `default` and
`stoponly` keep 5 and 3 (`stoponly` loses `sc-1-th-just-rf` and gains `tso-1-th-no-ltts`).
So the decision strategy fixes satisfiable problems and hurts unsat ones: it is not a default.
It fits a configuration aimed at satisfiable problems, or a variant that decides on the length
only when the search is otherwise stuck.

## 4. Regressions

`regress_check.py` runs every relations regression (`regress*/rels`: 129 files with `sat` or
`unsat` expected, 137 runs counting files with several command lines) with extra options and a
time limit of 60 s, 8 at a time:

| extra options | agree with EXPECT | wrong | unfinished in 60 s |
|---|---|---|---|
| none | 136 | 0 | `garbage_collect.cvc` (also on `#9`: timeout at 120 s) |
| `--rels-cycle-def-union` | 135 | 0 | `garbage_collect.cvc`; `acyclic-ltts-sc-1-th` (eager split, section 2.4; 0.8 s on `#9`) |
| `--rels-cycle-len-decide` | 135 | 0 | `garbage_collect.cvc`; `acyclic-ltts-plsc-2-th-just-rf-isf` (section 3; 0.3 s on `#9`) |
| `--rels-cycle-unroll-guard` | 136 | 0 | `garbage_collect.cvc` |
| all three | 134 | 0 | the three above |

No option gives a wrong answer. Two new regressions exercise the options:
`cyclic-union-def-transitive-superset.smt2` (unsat) and `cyclic-union-len-decide-sat.smt2`
(sat).

## 5. Portfolio

Virtual portfolio, 300 s per run, 5 runs at a time, on an Apple machine with 6 performance
cores (`configs-prototype.json`; 169 runs). The 7 configurations of `#9` were run again in the
same run, so the comparison is under the same load. **No wrong or disagreeing answer.**

Solved benchmarks per configuration (of 13):

| configuration | `#9` | `+def` | `+decide` |
|---|---|---|---|
| `default` | 5 | — | 5 |
| `fmf-unsat` | 7 | — | — |
| `nofmf-unsat` | 2 | — | — |
| `stoponly` | 3 | — | 3 |
| `fmf-unsat-rules` | 12 | 11 | — |
| `nofmf-unsat-rules` | 10 | 10 | 7 |
| `nofmf-unsat-hammer` | 3 | 3 | — |
| **virtual best** | **13** | 13 (all 13 configurations) | |

Seconds per benchmark, `#9` → with the option (`–`: not solved in 300 s):

| benchmark | fmf-unsat-rules +def | nofmf-unsat-rules +def | nofmf-unsat-hammer +def | default +decide | stoponly +decide | nofmf-unsat-rules +decide |
|---|---|---|---|---|---|---|
| plsc-1-th | 4.0 → 8.1 | 0.9 → 0.8 | – | – | – | 0.9 → 1.0 |
| plsc-1-th-just-rf | 0.3 → 0.3 | 0.1 → 0.1 | – | – | – | 0.1 → 0.1 |
| plsc-1-th-no-ltts (sat) | 0.1 → 0.1 | – | – | 0.1 → 0.0 | 0.3 → 0.5 | – |
| plsc-2-th | – | 77.5 → 96.9 | – | – | – | **77.5 → –** |
| plsc-2-th-just-rf | 1.1 → 1.0 | 0.4 → 0.4 | – | – | – | **0.4 → –** |
| sc-1-th | 0.4 → 0.2 | 0.1 → 0.1 | – | – | – | 0.1 → 0.1 |
| sc-1-th-just-rf | 0.1 → 0.1 | 0.1 → 0.0 | 0.1 → 0.1 | 0.2 → 0.2 | **4.7 → –** | 0.1 → 0.1 |
| sc-1-th-no-ltts (sat) | 0.1 → 0.1 | – | – | 0.0 → 0.1 | 0.1 → 0.1 | – |
| sc-2-th | 20.3 → 15.9 | 94.3 → 94.5 | 3.8 → 3.8 | – | – | **94.3 → –** |
| sc-2-th-just-rf | 0.2 → 0.2 | 0.2 → 0.2 | 0.2 → 0.2 | 1.1 → 0.9 | – | 0.2 → 0.3 |
| tso-1-th | **266.2 → –** | 6.8 → 6.8 | – | – | – | 6.8 → 3.2 |
| tso-1-th-just-rf | 0.2 → 0.3 | 0.1 → 0.1 | – | – | – | 0.1 → 0.1 |
| tso-1-th-no-ltts (sat) | 1.2 → 1.6 | – | – | 4.3 → 2.9 | **– → 18.7** | – |

Summary: neither option adds a benchmark to the virtual best (13 of 13 already). The rule
`+def` is neutral in `nofmf-unsat-rules` and `nofmf-unsat-hammer`; `fmf-unsat-rules` loses
`tso-1-th`, which `#9` solved in 266 s, close to the limit. `+decide` loses three unsat benchmarks in
`nofmf-unsat-rules`. Results: `benchmarks-ltts-analysis/results/portfolio/proto-300s` on the
machine that ran them.

## 6. Reproducing

From the root of the cvc5 checkout, with this branch built:

```sh
# the examples: 4 base configurations x {none, def, guard, decide, def+decide}
python3 scripts/union-witness/run_examples.py build/bin/cvc5 10

# every relations regression with extra options
python3 scripts/union-witness/regress_check.py build/bin/cvc5 "--rels-cycle-def-union" 60

# the virtual portfolio: the 7 configurations of #9 and 6 with the new options
python3 scripts/portfolio.py --cvc5 build/bin/cvc5 --mode virtual --timeout 300 --jobs 5 \
    --configs-file scripts/union-witness/configs-prototype.json --results results/proto-300s
```

| file | what it is |
|---|---|
| `examples/*.smt2` | the examples of these notes (`e0`–`e5`, `single`) |
| `run_examples.py` | runs them under every combination of options |
| `regress_check.py` | runs the relations regressions with extra options |
| `configs-prototype.json` | the portfolio configurations: the 7 of `#9`, `+def` for the three closure-induction configurations, `+decide` for `default`, `stoponly`, `nofmf-unsat-rules` |
