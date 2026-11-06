| configuration | solved / 509 | sat / 304 | unsat / 205 | timeouts | PAR-2 (s) | time on the 482 commonly solved (s) |
|---|---|---|---|---|---|---|
| main (eager) | 484 | 285 | 199 | 25 | 5398 | 333.9 |
| PR 1 (lazy strategy) | 490 | 290 | 200 | 19 | 4488 | 320.5 |
| this PR (+ endgame hints) | 496 | 296 | 200 | 13 | 3112 | 171.7 |

Solved per family (sat + unsat):

| configuration | arith BAPA (120) | arith MAPA (120) | card BAPA (120) | card MAPA (120) | SQL (29) |
|---|---|---|---|---|---|
| main (eager) | 120 | 120 | 104 | 111 | 29 |
| PR 1 (lazy strategy) | 120 | 120 | 110 | 112 | 28 |
| this PR (+ endgame hints) | 120 | 120 | 114 | 114 | 28 |

PR 1 (lazy strategy) vs main (eager): solves 8 benchmarks more and 2 fewer; among the 39 benchmarks both solve that take at least 1 s on either side, 19 are at least 2x faster and 14 at least 2x slower; 0 answer disagreements.
  gained: `card/cvc5_bapa/fol_0000049.smt2`, `card/cvc5_bapa/fol_0000071.smt2`, `card/cvc5_bapa/fol_0000072.smt2`, `card/cvc5_bapa/fol_0000096.smt2`, `card/cvc5_bapa/fol_0000097.smt2`, `card/cvc5_bapa/fol_0000118.smt2`, `card/cvc5_mapa/fol_0000048.smt2`, `card/cvc5_mapa/fol_0000097.smt2`
  lost: `card/cvc5_mapa/fol_0000072.smt2`, `sql/linear/calcite-query044-call-0.smt2`

this PR (+ endgame hints) vs main (eager): solves 13 benchmarks more and 1 fewer; among the 42 benchmarks both solve that take at least 1 s on either side, 24 are at least 2x faster and 15 at least 2x slower; 0 answer disagreements.
  gained: `card/cvc5_bapa/fol_0000048.smt2`, `card/cvc5_bapa/fol_0000049.smt2`, `card/cvc5_bapa/fol_0000071.smt2`, `card/cvc5_bapa/fol_0000072.smt2`, `card/cvc5_bapa/fol_0000096.smt2`, `card/cvc5_bapa/fol_0000097.smt2`, `card/cvc5_bapa/fol_0000102.smt2`, `card/cvc5_bapa/fol_0000103.smt2`, `card/cvc5_bapa/fol_0000105.smt2`, `card/cvc5_bapa/fol_0000118.smt2`, `card/cvc5_mapa/fol_0000048.smt2`, `card/cvc5_mapa/fol_0000097.smt2`, `card/cvc5_mapa/fol_0000104.smt2`
  lost: `sql/linear/calcite-query044-call-0.smt2`

