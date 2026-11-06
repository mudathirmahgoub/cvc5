| configuration | solved / 509 | sat / 304 | unsat / 205 | timeouts | PAR-2 (s) | time on the 484 commonly solved (s) |
|---|---|---|---|---|---|---|
| main (eager) | 484 | 285 | 199 | 25 | 5398 | 397.9 |
| PR 4 (+ guided enumeration) | 506 | 304 | 202 | 3 | 769 | 72.1 |
| this PR (+ cuts) | 509 | 304 | 205 | 0 | 79 | 62.1 |

Solved per family (sat + unsat):

| configuration | arith BAPA (120) | arith MAPA (120) | card BAPA (120) | card MAPA (120) | SQL (29) |
|---|---|---|---|---|---|
| main (eager) | 120 | 120 | 104 | 111 | 29 |
| PR 4 (+ guided enumeration) | 120 | 120 | 118 | 119 | 29 |
| this PR (+ cuts) | 120 | 120 | 120 | 120 | 29 |

PR 4 (+ guided enumeration) vs main (eager): solves 22 benchmarks more and 0 fewer; among the 32 benchmarks both solve that take at least 1 s on either side, 26 are at least 2x faster and 0 at least 2x slower; 0 answer disagreements.
  gained: `card/cvc5_bapa/fol_0000048.smt2`, `card/cvc5_bapa/fol_0000049.smt2`, `card/cvc5_bapa/fol_0000071.smt2`, `card/cvc5_bapa/fol_0000072.smt2`, `card/cvc5_bapa/fol_0000096.smt2`, `card/cvc5_bapa/fol_0000097.smt2`, `card/cvc5_bapa/fol_0000099.smt2`, `card/cvc5_bapa/fol_0000100.smt2`, `card/cvc5_bapa/fol_0000102.smt2`, `card/cvc5_bapa/fol_0000103.smt2`, `card/cvc5_bapa/fol_0000104.smt2`, `card/cvc5_bapa/fol_0000105.smt2`, `card/cvc5_bapa/fol_0000106.smt2`, `card/cvc5_bapa/fol_0000118.smt2`, `card/cvc5_mapa/fol_0000048.smt2`, `card/cvc5_mapa/fol_0000097.smt2`, `card/cvc5_mapa/fol_0000098.smt2`, `card/cvc5_mapa/fol_0000099.smt2`, `card/cvc5_mapa/fol_0000100.smt2`, `card/cvc5_mapa/fol_0000102.smt2`, `card/cvc5_mapa/fol_0000104.smt2`, `card/cvc5_mapa/fol_0000106.smt2`

this PR (+ cuts) vs main (eager): solves 25 benchmarks more and 0 fewer; among the 32 benchmarks both solve that take at least 1 s on either side, 29 are at least 2x faster and 1 at least 2x slower; 0 answer disagreements.
  gained: `card/cvc5_bapa/fol_0000048.smt2`, `card/cvc5_bapa/fol_0000049.smt2`, `card/cvc5_bapa/fol_0000071.smt2`, `card/cvc5_bapa/fol_0000072.smt2`, `card/cvc5_bapa/fol_0000096.smt2`, `card/cvc5_bapa/fol_0000097.smt2`, `card/cvc5_bapa/fol_0000098.smt2`, `card/cvc5_bapa/fol_0000099.smt2`, `card/cvc5_bapa/fol_0000100.smt2`, `card/cvc5_bapa/fol_0000102.smt2`, `card/cvc5_bapa/fol_0000103.smt2`, `card/cvc5_bapa/fol_0000104.smt2`, `card/cvc5_bapa/fol_0000105.smt2`, `card/cvc5_bapa/fol_0000106.smt2`, `card/cvc5_bapa/fol_0000107.smt2`, `card/cvc5_bapa/fol_0000118.smt2`, `card/cvc5_mapa/fol_0000048.smt2`, `card/cvc5_mapa/fol_0000097.smt2`, `card/cvc5_mapa/fol_0000098.smt2`, `card/cvc5_mapa/fol_0000099.smt2`, `card/cvc5_mapa/fol_0000100.smt2`, `card/cvc5_mapa/fol_0000102.smt2`, `card/cvc5_mapa/fol_0000104.smt2`, `card/cvc5_mapa/fol_0000106.smt2`, `card/cvc5_mapa/fol_0000107.smt2`

