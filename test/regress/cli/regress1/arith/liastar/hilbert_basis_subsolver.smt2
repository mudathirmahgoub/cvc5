; COMMAND-LINE: --arith-liastar-subsolver-hilbert-basis
; DISABLE-TESTER: proof
; The DNF disjuncts are pruned with the Hilbert basis computation instead of
; a cvc5 subsolver. Distributing the conjunction gives four disjuncts, and
; the two with y <= -1 contradict x >= 0. The others give the vectors
; (2y, y) and (2y + 1, y) with y >= 1, so the only vectors whose second
; component is 1 are (2, 1) and (3, 1), and (4, 1) is not a sum of them.
(set-logic HO_ALL)
(set-info :status unsat)
(set-option :quiet true)
(declare-const a Int)
(declare-const b Int)
(assert (= a 4))
(assert (= b 1))
(assert (int.star-contains
  (lambda ((x Int) (y Int))
    (and (or (= x (* 2 y)) (= x (+ (* 2 y) 1)))
         (or (>= y 1) (<= y (- 1)))
         (>= x 0)))
  a b))
(check-sat)
