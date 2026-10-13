; COMMAND-LINE: --unate-lemmas=none --no-arith-rewrite-equalities --simplification=none
; COMMAND-LINE: --no-arith-rewrite-equalities
; EXPECT: unsat
; Unate propagation of a new bound implies the disequality at the value of the
; previous bound: x >= 5 after x >= 4 implies (not (= x 4)), y <= 4 after
; y <= 5 implies (not (= y 5)), and z = 6 within 4 <= z <= 8 implies
; (not (= z 4)) and (not (= z 8)).
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const p Bool)
(assert (>= x 4))
(assert (>= x 5))
(assert (or (= x 4) p))
(assert (<= y 5))
(assert (<= y 4))
(assert (or (= y 5) p))
(assert (>= z 4))
(assert (<= z 8))
(assert (= z 6))
(assert (or (= z 4) (= z 8) p))
(assert (not p))
(check-sat)
