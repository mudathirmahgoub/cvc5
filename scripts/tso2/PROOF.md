# Why `tso-2-th` and `tso-2-th-just-rf` are unsat

Benchmarks: `benchmarks-ltts/tso-2-th.smt2` and `tso-2-th-just-rf.smt2` of
rachelcleaveland/relational-solver-benchmarks (`eb43bca`). Both describe a candidate
execution with **two threads**, assert the litmus-test templates (LTTs), and ask for an
execution that X86-TSO forbids: `(assert (not mcm))`. Both are unsat. The proof below uses only
a few of the templates; the fence templates are not needed.

## 1. What the files say

Writing `;` for `rel.join`, `X+` for `rel.tclosure X`, `[S]` for `rel.iden S`:

* `Event = MemEvent ⊎ Fence`, `MemEvent = Read ⊎ Write`.
* `po ⊆ Event × Event`; `po` and `po⁻¹` are functional (`rel.is-functional`); `¬cyc(po)`
  (template); two distinct events of the same thread are `po+`-related.
* `thread(e) ∈ Thread_set = {th0, th1}` for every event, `th0 ≠ th1`.
* `loc = address ; address⁻¹`, `address` functional and total on `MemEvent`.
* `rf ⊆ Write × Read`, each read reads from at most one write (`rf ; rf⁻¹ ⊆ iden`), `rf ⊆ loc`.
* (`tso-2-th` only) `co ⊆ Write × Write`, transitive, `co ⊆ loc`;
  `fr = rf⁻¹ ; co ∪ (rd_from_initial × Write)`, `fr ⊆ Read × Write`, `fr ⊆ loc`.
* `int` = same-thread pairs of events, `ext = Event² ∖ int`, `rfe = rf ∩ ext`,
  `fre = fr ∖ int`, `coe = co ∖ int`.
* `sm = iden ∩ MemEvent²`, `po-loc = po+ ∩ loc`.
* `ppo = [Read];po+;[Read] ∪ [MemEvent];po+;[Write] ∪ [MemEvent];po+;[MFENCE];po+;[MemEvent] ∪ implied`,
  `implied ⊆ [Write];po+;[Read]`.
* `ghb = ppo ∪ (rfe ∪ fr ∪ co);sm` (`tso-2-th`), `ghb = ppo ∪ rfe;sm` (`just-rf`).
* `mcm = ¬cyc(po-loc ∪ rf ∪ fr ∪ co) ∧ rmw ∩ fre;coe = ∅ ∧ ¬cyc(ghb)` (`tso-2-th`),
  `mcm = ¬cyc(rf) ∧ ¬cyc(ghb)` (`just-rf`).

Templates used below (`c, c1, c2 ∈ {rf, co, fr}`; only `rf` in `just-rf`):

| name | templates |
|---|---|
| T-po | `¬cyc(po)` |
| T-loc | `irr(c)`, `irr(po-loc+;c)`, `irr(c1;c2)`, `irr(po-loc+;c1;c2)`, `irr(c1;po-loc+;c2)`, `irr(po-loc+;c1;po-loc+;c2)` |
| T-ppo | `irr(c)`, `irr(ppo+;c)`, `irr(c1;c2)`, `irr(ppo+;c1;c2)`, `irr(c1;ppo+;c2)`, `irr(ppo+;c1;ppo+;c2)` |
| T-rmw | `irr(fre;coe;rmw⁻¹)` |

`irr(X)` is irreflexivity: no `(x, x) ∈ X`. Irreflexivity is invariant under rotation
(`irr(X;Y)` iff `irr(Y;X)`), so a template excludes every cycle of its shape, from any starting
point.

## 2. Basic facts

**F1 (chains).** `po` and `po⁻¹` are functional and `po` is acyclic, so `po` is a disjoint union
of finite paths (*chains*), and `po+` totally orders each chain. The events of one thread are
pairwise `po+`-related, so they lie on one chain. All events belong to one of two threads, so
**events lie on at most two chains**; if on two, each chain holds exactly the events of one
thread (all events of a thread are on one chain), so then *same chain = same thread*.

**F2 (`ppo`).** `ppo ⊆ po+`. For memory events `x po+ y`, `(x, y) ∈ ppo` unless `x ∈ Write` and
`y ∈ Read`: `R po+ R` and `M po+ W` are in `ppo`.

**F3 (locations).** `rf, co, fr, po-loc ⊆ loc`, and `loc` is an equivalence on memory events
(`address` is a function). So all events of a cycle of `po-loc ∪ rf ∪ co ∪ fr` access the same
address.

**F4 (`sm`).** Communication edges end at memory events and `sm` is the identity there, so
`ghb = ppo ∪ rfe ∪ fr ∪ co` (`ppo ∪ rfe` in `just-rf`).

**F5 (edge types).** `rf : W → R`, `co : W → W`, `fr : R → W`. In particular a communication edge
that starts at a read is an `fr` edge, and one that ends at a read is an `rf` edge.

**F6 (minimal cycles).** Let `G = P ∪ C` with `P ⊆ po+` (so `P` alone is acyclic, T-po). Every
cycle of `G` has a `C` edge. Take a cycle `κ` with the **fewest `C` edges**. It is simple: a
repeated event splits `κ` into two cycles, each with a `C` edge, so each with fewer `C` edges.
**Shortcut:** if `x, y` are events of `κ` with `(x, y) ∈ P`, the arc of `κ` from `x` to `y` has no
`C` edge, for otherwise replacing it by the edge `(x, y)` gives a cycle with fewer `C` edges.

## 3. Atomicity and `cyc(rf)`

* `tso-2-th`, `rmw ∩ fre;coe ≠ ∅`: for `(r, w)` in both, `(r, r) ∈ fre;coe;rmw⁻¹`, against T-rmw.
* `just-rf`, `cyc(rf)`: `rf ⊆ Write × Read` and `Write ∩ Read = ∅`, so `rf;rf = ∅`, `rf+ = rf`,
  and `rf` is irreflexive (T-ppo `irr(rf)`).

## 4. Theorem A: no cycle of `po-loc ∪ rf ∪ co ∪ fr` (`tso-2-th`)

Apply F6 with `P = po-loc`, `C = rf ∪ co ∪ fr`. All events of `κ` access one address (F3), so
two distinct events `x po+ y` of `κ` on the same chain satisfy `(x, y) ∈ po-loc`: **the arc of `κ`
from `x` to `y` is a `po-loc` path** (shortcut).

Let `a` and `b` be the `po`-first and `po`-last events of `κ` on a chain `K`. For every event `z`
of `κ` on `K`, the arcs `a → z` and `a → b` are `po-loc` paths starting at `a`, so one is a prefix
of the other: **the events of `κ` on `K` form one contiguous arc `a → b` of `po-loc` edges.** The
edge leaving `b` is a `C` edge (an edge into `K` before `a` or out of `K`).

* One chain: `κ = (a → b) + (b, a)` with `(b, a) ∈ C`: `κ ∈ po-loc* ; c`. Excluded by
  `irr(c)`, `irr(po-loc+;c)`.
* Two chains `K1, K2`: leaving the arc of `K1` the cycle enters the arc of `K2` (no other events),
  and only at its first event (the arc is contiguous and `κ` is simple), and vice versa:
  `κ = po-loc* ; c1 ; po-loc* ; c2` with chain-crossing `C` edges. Excluded by T-loc.

## 5. Theorem B: no cycle of `ghb` (both files)

Apply F6 with `P = ppo`, `C = rfe ∪ fr ∪ co` (F4). A **run** is a maximal arc of `κ` made of
`ppo` edges (possibly a single event); runs and `C` edges alternate, so `κ` has `m` runs and `m`
`C` edges, `m ≥ 1`. `ppo` edges stay on a chain (F2), so every run lies on one chain.

**Claim 1.** If `x, y` are events of `κ` in *different* runs on the same chain and `x po+ y`, then
`x ∈ Write` and `y ∈ Read`. *Otherwise `(x, y) ∈ ppo` (F2) while the arc `x → y` contains a `C`
edge (it leaves a run): the shortcut of F6 is violated.*

**Claim 2.** A chain holds at most two runs; if two, a run of writes `U` lies entirely
`po`-before a run of reads `V`. *Let `U ≠ V` be runs on one chain and `u₀` the `po`-first event
of `U ∪ V`, say `u₀ ∈ U`. By Claim 1, `u₀ ∈ Write` and every event of `V` is a read. If some
`u ∈ U` were `po`-after some `v ∈ V`, Claim 1 would make `v` a write. So `U` is before `V` and,
by Claim 1 again, `U ⊆ Write`. Three runs `U < V < X` on one chain would make `V` both reads
(after `U`) and writes (before `X`).*

So `m ≤ 4`, and `m ≤ 2` if all events are on one chain.

* **`m ≤ 2`**: `κ` is `ppo* ; c1 (; ppo* ; c2)` with `c1, c2 ∈ {rfe, fr, co} ⊆ {rf, fr, co}`.
  Excluded by T-ppo.
* **`m ∈ {3, 4}`**: then two chains (each a thread, F1), and some chain carries a write run `U`
  before a read run `V`. The `C` edge leaving `V` starts at a read, so it is an `fr` edge (F5);
  **in `just-rf` there is no `fr`, so this case cannot occur.** The `C` edge entering `V` ends at
  a read, so it is an `rf` edge, and in `ghb` an `rfe` edge: it comes from the other chain.
  * `m = 3`: the third run `X` is on the other chain, so `X → V` by `rfe`. The `fr` edge leaving
    `V` goes to `U` or `X`; to `X` would close the cycle `X, V` without `U`. So `V → U` by `fr`.
  * `m = 4`: both chains carry runs `Uᵢ < Vᵢ`. Each `Vᵢ` is entered by `rfe` from a write run of
    the other chain, `U₁ → V₂` and `U₂ → V₁`; each `Vᵢ` is left by `fr` into a write run; for the
    four runs to form one cycle, `V₂ → U₂` and `V₁ → U₁`.

  In both cases some `fr` edge goes from the last event `r` of a read run `V` to the first event
  `w` of the write run `U` before it on the same chain: `w po+ r`, and `w`, `r` access the same
  address (`fr ⊆ loc`), so `(w, r) ∈ po-loc` and `(w, w) ∈ po-loc ; fr`. Excluded by
  `irr(po-loc+;fr)`.

## 6. Conclusion

* `tso-2-th`: `¬mcm` needs a cycle of `po-loc ∪ rf ∪ co ∪ fr` (Theorem A), an atomicity
  violation (section 3) or a cycle of `ghb` (Theorem B). All three are impossible: **unsat**.
* `tso-2-th-just-rf`: `¬mcm` needs `cyc(rf)` (section 3) or a cycle of `ghb` (Theorem B, where
  `m ≤ 2` because there is no `fr`): **unsat**.

The fence templates and `implied` play no role: Theorem B only uses `ppo ⊆ po+` and that `R po+ R`
and `M po+ W` are in `ppo`. Thread structure enters only through F1 (at most two chains, chain =
thread when there are two).

## 7. The proof in terms of the cycle witness of cvc5

For `cyc(ghb)` cvc5 builds a shortest cycle `s1 → s2 → … → sl = s1` of the closures of the
operands of `ghb`. With the operands `ppo` and `rfe;sm` (`just-rf`), edges alternate between
`ppo+` and `rfe`, so `l = 2k + 1`:

* `l = 3` (`ppo+;rfe`) and `l = 5` (`ppo+;rfe;ppo+;rfe`): T-ppo.
* `l ≥ 7`: the prefix `s1 →ppo+ s2 →rfe s3 →ppo+ s4 →rfe s5` already gives a conflict that holds
  for every such `l`. `s1`, `s3`, `s5` are reads (targets of `rfe`, the first one of the closing
  edge); there are two threads, so two of them, `s_q` and `s_r` (`q < r`), are in one thread
  (pigeonhole: a case split on `thread(s1)`, `thread(s3)`, `thread(s5)`). They are distinct
  (**Distinct**), so `po` totality makes them `po+`-related, and both are reads, so `ppo` (F2)
  contains `(s_q, s_r)`, a **chord**, or `(s_r, s_q)`, a **backward edge** closing the shorter
  cycle `s_q → … → s_r → s_q`. The minimality lemmas of the witness forbid both (Chord,
  Backward). Unlike section 5 this needs neither chains nor `fr`.

So every rule cvc5 needs is already in the calculus (witness, minimality with backward chords,
closure membership through joins with `rel.iden`, `po` totality by instantiation); what is
missing is finding this short argument in the search.
