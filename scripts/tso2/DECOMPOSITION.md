# tso-2-th is unsat: a proof by bounded cvc5 queries

`tso-2-th` asserts `(not mcm)` with `mcm` the conjunction of three conditions, so it is unsat
iff each of the three violations is unsat (files in `split/`):

| violation | cvc5 (all options of `README.md`) |
|---|---|
| atomicity, `rmw ∩ fre;coe ≠ ∅` (`tso-2-th.B2-atom`) | unsat, 0.1 s |
| SC per location, `cyclic(po-loc ∪ rf ∪ fr ∪ co)` (`tso-2-th.B1-scloc`) | unsat, 29 s |
| `cyclic(ghb)` (`tso-2-th.B3-ghb`) | timeout as a single query (see below) |

`cyclic(ghb)` is proved unsat by the following decomposition. Every step except the lemma is a
cvc5 query.

## The lemma

Let `G` be a finite relation and `K ≥ 1`. If

* (a) for every `n = 1 … K` there are no `n` distinct elements `e0 → e1 → … → e(n-1) → e0`
  with every edge in `G`, and
* (b) there are no `K` distinct elements `p0 → p1 → … → p(K-1)` with every edge in `G` and
  no other edge of `G` between any two of them, in either direction,

then `G` is acyclic.

*Proof.* If `G` has a cycle, it has a shortest one, with `m` edges and `m` distinct elements.
If `m ≤ K`, (a) excludes it. If `m > K`, take `K` consecutive elements `p0 … p(K-1)` of the
cycle. An edge `(pi, pj) ∈ G` with `j > i + 1` would shortcut the cycle (`m − (j − i) + 1 < m`
edges); one with `j < i` would close the cycle `pj → … → pi → pj` of `i − j + 1 ≤ K < m`
edges. So the `pi` satisfy (b), which is excluded. ∎

## The queries

With `G = ghb` and `K = 9` on `split/t2-B3-min.smt2` (the axioms and the 44 templates the hand
proof uses; fewer assumptions than the benchmark, so unsat there means unsat for the
benchmark), configuration of `README.md`:

| query | result |
|---|---|
| (b) path of 9 elements | **unsat, 26.8 s** (10 elements: 23.6 s) |
| (a) n = 1 | unsat, 0.1 s |
| n = 2 | unsat, 0.2 s |
| n = 3 | unsat, 0.8 s |
| n = 4 | unsat, 3.5 s |
| n = 5 | unsat, 11.9 s |
| n = 6 | unsat, 43.2 s |
| n = 7 | unsat, 95.5 s |
| n = 8 | unsat, 305.6 s |
| n = 9 | **unsat, 879.4 s** |

Total about 23 minutes of cvc5 time; run in parallel, the 9-edge cycle bounds it to about
15 minutes. With the atomicity and SC-per-location queries this proves `tso-2-th` unsat.

Paths of 4 to 8 elements did not finish in 15 minutes: short chord-free paths may well exist
(the queries are then satisfiable, which this unsat-oriented configuration does not establish).
9 is therefore the bound used.

## Reproducing

```sh
python3 scripts/tso2/decompose.py build/bin/cvc5 scripts/tso2/split/t2-B3-min.smt2 ghb 9 \
    /tmp/decomp 3600 5 -- \
    --rels-acyclic-anchor=inclusion --inst-when=full-delay --rels-acyclic-backward-chords \
    --prenex-quant=none --rels-tc-subset --rels-tc-down-lazy --rels-product-lazy \
    --rels-product-lazy-compose --rels-tc-up-skip-known --rels-tc-subset-split
```

## What this says about cvc5

* **No inference rule is missing.** Every query is a bounded problem that cvc5 decides with
  its existing rules (minimality-free: plain membership, totality instances, joins, closure
  induction, templates), in seconds to minutes.
* **The single query asks cvc5 to find the bound itself.** The witness of `rel.cyclic` is a
  shortest cycle unrolled by iterative deepening: every length is refuted inside one CDCL
  search, which re-derives the same facts position by position. Measured: the plain-edge
  witness needs 3, 19, 79 s to refute lengths up to 4, 5, 6 (×4-6 per length; about 11 hours
  extrapolated to length 10, where the 9-element prefix conflict covers all longer lengths); the
  closure-edge witness (the default) stays at length 6 for more than 80 minutes. The explicit
  queries grow by ×3 per edge and are independent.
* So it is an **algorithmic / scalability** problem of the search, not of the calculus: what
  the decomposition does by hand is (1) establish a length bound once, by a query that does
  not depend on the length (the chord-free path), and (2) refute each length in its own small
  search. A solver strategy doing the same (bound first, then bounded cycles, possibly in
  parallel) would solve `tso-2-th` in about 15 minutes.
