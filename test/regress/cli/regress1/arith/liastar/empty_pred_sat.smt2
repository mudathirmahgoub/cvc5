; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --arith-liastar-main-solver
; COMMAND-LINE:
; COMMAND-LINE: --arith-liastar-push-pop
; COMMAND-LINE: --no-arith-liastar-lazy
;
; The predicate under the star is infeasible, so the star set is exactly the
; zero vector (the empty sum). The vector is forced to zero by non-constant
; bounds, so the answer is sat. Regression test for the main-solver driver
; lemma omitting the empty-sum branch of the star under-approximation.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const a Int)
(declare-const b Int)
(assert (>= a 0))
(assert (<= a 0))
(assert (>= b 0))
(assert (<= b 0))
(assert (int.star-contains
  (lambda ((x Int) (y Int))
    (and (>= (+ x y) 1) (>= (* (- 1) (+ x y)) 0)))
  a b))
(check-sat)
