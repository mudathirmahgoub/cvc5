# Reproducing the LIA\* experiments

This is the lab notebook for the report `liastar_lazy_report.pdf`: the exact
commands behind every measured number, and the reasoning that led from one
bottleneck to the next until all 480 benchmarks were solved. Everything here
is runnable; the helper scripts live next to this file in `repro/`.

Paths assumed (edit if yours differ):
- cvc5 checkout: `/home/mudathir/all/cvc5/mudathir`
- benchmarks root: `/home/mudathir/fmcad26` (so a benchmark is e.g.
  `/home/mudathir/fmcad26/sls-reachability/card/cvc5_bapa/fol_0000100.smt2`)
- comparison sheet (1 row per benchmark, reference-solver columns):
  `/home/mudathir/all/paper-fmcad26-liastar/scripts/comparison.csv`

A note on honesty up front: timings are wall-clock on one shared 24-core
machine, 12 jobs in parallel, and will vary run-to-run by 10-30%. The
*qualitative* conclusions (which config solves more, which is faster, where
the memory goes) are stable; treat absolute seconds as approximate.

---

## 0. Builds

Two builds. The **production** build is used for ALL timing/memory numbers
(assertions off, optimized). The **debug** build (`build/`, assertions on) is
used only for tracing and for catching crashes -- it is 10-50x slower, so
never time with it.

```bash
cd /home/mudathir/all/cvc5/mudathir

# production build with Normaliz (the LIA* backend)
./configure.sh production --normaliz --auto-download --name=build-prod
cmake --build build-prod --target cvc5-bin -j$(nproc)        # -> build-prod/bin/cvc5

# debug build (already present as build/) -- for traces and assertions
cmake --build build       --target cvc5-bin -j$(nproc)        # -> build/bin/cvc5
```

The configuration flags that exist (final defaults in parentheses):

| flag | default | what it does |
|---|---|---|
| `--no-arith-liastar-lazy` | lazy on | eager: full DNF up front |
| `--arith-liastar-generalize` | on | boolean (prime-implicant) cell generalization |
| `--arith-liastar-generalize-semantic` | off | arithmetic cell generalization (probe) |
| `--arith-liastar-guided` | on | bias the cell search by `y <= v` |
| `--arith-liastar-endgame=N` | 10 | decoupled witness/cut search every N cells |
| `--arith-liastar-cuts` | on | over-approximating homogeneous cuts |
| `--arith-liastar-push-pop` | off | cumulative subsolver refinement |
| `--arith-liastar-main-solver` | off | enumerate cells in the main solver |
| `--arith-liastar-partial-sums` | off | constant-size reduction lemmas |

---

## 1. The benchmark harness

`repro/run_one.sh` runs one instance under one config; `repro/run_campaign.sh`
fans it out 12-way over all 480. Conditions held fixed across configs: 100 s
timeout, 6 GB memory cap, single solver thread, production build.

```bash
cd repro
./run_one.sh final sls-reachability/card/cvc5_bapa/fol_0000100.smt2
# -> sls-reachability/card/cvc5_bapa/fol_0000100.smt2,sat,1.143

# a full campaign for one config (writes <config>.csv):
./run_campaign.sh final          # the shipped default  -> final.csv
./run_campaign.sh acc            # lazy-accumulate baseline
./run_campaign.sh gen            # +boolean generalization
./run_campaign.sh guided_endgame # gen+guided+endgame, no cuts
# ... pp ms sem psum eager
```

Because the shipped defaults changed over the project (generalize / guided /
endgame / cuts all became default-on), each *historical* config is reproduced
by starting from "everything off" and switching exactly one feature back on.
The exact flag set per config is in `run_one.sh` (read the `case`).

---

## 2. Turning runs into the headline numbers

`repro/analyze.py` joins a campaign CSV to the comparison sheet and prints the
solved counts, cumulative/median/max time, and -- crucially -- the
**soundness audit**: answer discrepancies against every recorded
reference-solver column.

```bash
python3 analyze.py final.csv
```
yields (final default):
```
counts: {'sat': 296, 'unsat': 184} | solved: 480 / 480
cumulative time over solved: 143.5s  median: 45ms  max: 37.2s
soundness audit (discrepancies vs every reference column):
  vs sls result            0 discrepancies
  vs cvc5 lia result       0 discrepancies
  vs unfold5 result        0 discrepancies
  vs no_interp result      0 discrepancies
  vs sqlsolver result      5 discrepancies   <-- inspect
  ...
```

**The 5 SQLSolver discrepancies are SQLSolver being unsound, not us.** On
those 5 MAPA instances SQLSolver reports SAT while we report UNSAT, and:
- the *independent eager* cvc5 encoding (`cvc5 lia`, a completely different
  algorithm) agrees with our UNSAT on 4 of them and times out on the 5th;
- `sls` agrees with our UNSAT on 4 and times out on the 5th;
- the corrected `modified_sqlsolver` downgrades all 5 to `unknown`.

Independent confirmation you can run yourself:
```bash
for f in arith/cvc5_mapa/fol_0000055 arith/cvc5_mapa/fol_0000078 \
         arith/cvc5_mapa/fol_0000116 arith/cvc5_mapa/fol_0000120; do
  echo -n "$f: "; build-prod/bin/cvc5 -q --no-arith-liastar-lazy \
    /home/mudathir/fmcad26/sls-reachability/$f.smt2 | tail -1   # eager: all UNSAT
done
```
So the report's "no discrepancy against the four reference solvers" means the
four *sound* ones (sls, cvc5-lia, unfold5, no_interp); SQLSolver is excluded
because it is unsound here (and its own fixed version retracts the answer).

---

## 3. Per-instance measurement primitives

These three commands produce every "rounds / MB / cell-size" number in the
report.

**Wall time + peak memory + round count** (on one instance):
```bash
/usr/bin/time -v timeout 600 build-prod/bin/cvc5 -q --stats <bench>.smt2 2>&1 \
  | grep -E "ARITH_LIA_STAR_(EXISTS|CUT|HINT)|Maximum resident set size|Elapsed \(wall"
# ARITH_LIA_STAR_EXISTS ~ number of refinement rounds (one reduction lemma/round)
# ARITH_LIA_STAR_CUT    = cuts emitted ;  ARITH_LIA_STAR_HINT = endgame hints
# Maximum resident set size (kbytes) = peak memory
```

**Round count via trace** (independent of stats):
```bash
build/bin/cvc5 -q -t liastar-ext <bench>.smt2 2>&1 | grep -c "cones for lambda"
```

**Cell sizes** (how many atoms each discovered cell has -- the generalization
metric):
```bash
build/bin/cvc5 -q -t liastar-ext paper2008.smt2 2>&1 \
  | grep "^disjunct: (and" | awk '{print NF}' | sort -n
#   default (generalize on):      42 42 42 42 42 47 47
#   --no-arith-liastar-generalize: 83 83 83 83 86 86 91 94     (cells ~2x bigger)
```

---

## 4. The reasoning chain (bottleneck by bottleneck)

Each step: the hypothesis, the command that tested it, the number observed,
and the conclusion that set the next action.

### 4.1 Push/pop -- "measure before optimizing"
**Hypothesis:** the subsolver accumulating one negated cell per round is the
memory bottleneck; combining them under push/pop will help.
**Test (A/B on the hard instance + full campaign):**
```bash
./run_one.sh acc sls-reachability/card/cvc5_bapa/fol_0000100.smt2   # baseline
./run_one.sh pp  sls-reachability/card/cvc5_bapa/fol_0000100.smt2   # push/pop
/usr/bin/time -v timeout 600 build-prod/bin/cvc5 -q --stats <inst> 2>&1 | grep "Maximum resident"
./run_campaign.sh acc; ./run_campaign.sh pp; python3 analyze.py pp.csv --vs acc.csv
```
**Observed:** identical ~3.2 GB peak, ~1000 rounds for both; campaign 460 (pp)
vs 463 (acc) -- push/pop slightly *worse*.
**Conclusion:** the memory is in the MAIN solver's accumulated lemmas, not the
subsolver. Abandon push/pop as default; stop optimizing the subsolver.
(The A/B build recipe used for an apples-to-apples binary diff is in section 5.)

### 4.2 Boolean generalization -- the win
**Hypothesis:** cells are far finer than the predicate's logical structure;
shrinking them to prime implicants cuts the round count.
**Test:** cell-size command (section 3) -- cells 83->42 tokens; then campaign.
```bash
./run_campaign.sh gen; python3 analyze.py gen.csv --vs acc.csv
```
**Observed:** 466 vs 463 solved, +3 / -0, ~4.4x faster on the common set.
**Conclusion:** make it the default.

### 4.3 Partial sums -- a refuted hypothesis
**Hypothesis:** each round's lemma carries sum constraints over all k cones,
so lemma text is quadratic in rounds; running partial sums make it linear and
should cut memory.
**Test:**
```bash
/usr/bin/time -v timeout 600 build-prod/bin/cvc5 -q --stats --arith-liastar-partial-sums <inst> 2>&1 \
  | grep -E "Maximum resident|ARITH_SPLIT_DEQ"
./run_campaign.sh psum; python3 analyze.py psum.csv --vs acc.csv
```
**Observed:** memory got *worse* (4.4 vs 3.3 GB); 450 vs 463 solved;
`ARITH_SPLIT_DEQ` jumped 14 -> 663.
**Conclusion:** the quadratic-lemma hypothesis is wrong -- the dominant cost is
the per-cone constraint volume, and the all-equality star `v = P_k` forces
disequality splitting. Keep off. (This is what pointed the search at the
*round count* and the *main-solver endgame* next.)

### 4.4 The hard SAT instance -- three diagnostics
`fol_0000100` timed out everywhere at ~1000 rounds. Three commands localized
why.

*(a) Does a one-summand witness exist?* Extract `A and p[v]` and check it
standalone -- if UNSAT, the star is unavoidable:
```bash
# (the report's helper builds A and p[v]; the result was UNSAT, i.e. >=2 summands needed)
```
*(b) Is cell discovery the bottleneck?* Count distinct cells found:
```bash
build/bin/cvc5 -q -t liastar-ext <inst> > /tmp/tr.log 2>&1   # (let run ~minutes)
python3 analyze_cells.py /tmp/tr.log
#   rounds 66, distinct cells 66, Hilbert basis sizes 0/6/32/506
```
The five cells a hand-decomposition needs all appear within ~30 rounds ->
discovery is NOT the problem.
*(c) Is the endgame starved?* Trace the guard value each round:
```bash
build/bin/cvc5 -q --arith-liastar-guided --arith-liastar-endgame=10 \
  -t liastar-endgame <inst> 2>&1 | grep -E "endgame query|hint guard" | head
#   "hint guard: false" at EVERY round -> the solver never tries the star
```
**Conclusion:** the multipliers form an integer program the main solver never
gets to finish (refinement keeps rewriting it; the guard is propagated false
before it is ever decided). Fix = guided enumeration + a *decoupled* endgame
solver + feeding the witness back as *decisions* (not a phase-preferred lemma).
**Verify the fix:**
```bash
./run_one.sh final sls-reachability/card/cvc5_bapa/fol_0000100.smt2   # sat, ~1s
build-prod/bin/cvc5 -q --check-models <inst>                          # model-checked
./run_campaign.sh guided_endgame; python3 analyze.py guided_endgame.csv --vs gen.csv
#   476 vs 466, +11 (the whole fol_0099..0106 family) / -1
```

### 4.5 The hard UNSAT instances -- cuts
Four instances remained, all UNSAT; eager also times out, so completing the
enumeration is hopeless. They need an over-approximation.
**Diagnosis -- dump the endgame's unsat query and minimize it:**
```bash
build/bin/cvc5 -q --arith-liastar-endgame=20 -t liastar-endgame <inst> 2>&1 \
  | grep "core:"              # the unsat-assumptions core: which input facts block the decomposition
```
The core pointed at a counting contradiction. To design the synthesis loop I
re-implemented the in-solver CEGIS in Python and watched every step:
```bash
python3 cegis_replica.py
#   round 0..7: one cut each; "REFUTED after 8 cuts"  (~33 CEGIS iterations)
```
The replica **converged where the in-solver version did not**, which exposed
the bug: the in-solver code was constraining candidates with the cells'
Hilbert-basis ray *directions* as if they were sample *points* (a ray of a
bit-pinned cell has 0 in that coordinate, so it passes the zero filter while
pointing outside the restriction, excluding the one valid cut). Fix: use only
genuine predicate points as samples. **Verify:**
```bash
for x in card/cvc5_bapa/fol_0000098 card/cvc5_mapa/fol_0000098 \
         card/cvc5_bapa/fol_0000107 card/cvc5_mapa/fol_0000107; do
  echo -n "$x: "; ./run_one.sh final sls-reachability/$x.smt2
done
#   all unsat, 0.2-2.0s
./run_campaign.sh final; python3 analyze.py final.csv     # 480/480, 0 sound discrepancies
```

---

## 5. A/B build recipe (apples-to-apples binary diff)

For the push/pop comparison I needed the *same* benchmark run by the old and
new code. cvc5 links `libcvc5.so` dynamically, so just rebuilding overwrites
the library -- a naive A/B accidentally runs the new code twice. The correct
recipe bundles each side's own library and selects it with `LD_LIBRARY_PATH`:

```bash
# build NEW, stash the change, build OLD into a separate dir, restore:
cmake --build build-prod --target cvc5-bin -j$(nproc)
cp build-prod/bin/cvc5 build-prod/src/libcvc5.so.1* /tmp/prod-new/   # + parser lib + symlinks
git stash
cmake --build build-prod --target cvc5-bin -j$(nproc)
cp build-prod/bin/cvc5 build-prod/src/libcvc5.so.1* /tmp/prod-old/
git stash pop && cmake --build build-prod --target cvc5-bin -j$(nproc)

# run each bundle against ITS OWN library (verify with: ldd / md5sum the .so):
LD_LIBRARY_PATH=/tmp/prod-old /tmp/prod-old/cvc5 -q <inst>
LD_LIBRARY_PATH=/tmp/prod-new /tmp/prod-new/cvc5 -q <inst>
```
(For configs gated by a runtime flag -- which is all of them in the final
code -- this dance is unnecessary: just pass the flag. It was only needed
during development when old vs new differed by uncommitted source.)

---

## 6. Trace channels (for deeper digging)

| channel | shows |
|---|---|
| `-t liastar-ext` | discovered cells, cones, `"N cones for lambda"` per round |
| `-t liastar-endgame` | endgame query results, hint guard values, unsat cores |
| `-t liastar-endgame-smt` | a replayable SMT-LIB dump of each endgame query |
| `-t liastar-cuts` | cut targets and synthesized cuts |
| `-t liastar-ext-smt` | a replayable soundness script for the reduction |

---

## 7. End-to-end: reproduce the results table

```bash
cd repro
for cfg in acc pp ms gen sem psum guided_endgame final; do ./run_campaign.sh $cfg; done
for cfg in acc pp ms gen sem psum guided_endgame final; do
  echo "== $cfg =="; python3 analyze.py $cfg.csv | head -2
done
```
Expected solved counts: acc 463, pp 460, ms 447, gen 466, sem 465, psum 450,
guided_endgame 476, final **480**. (Each full campaign is ~10-40 min wall
depending on how many instances hit the 100 s timeout.)
