; COMMAND-LINE: --learned-rewrite
; REQUIRES: unrestricted-mode
; --learned-rewrite is not supported with proofs or unsat cores because
; the preprocessing pass does not track its non-local reasoning.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; The learned-rewrite pass rewrites the aggregate by the key of X, and keeps
; the assertion of the key: a row of X twice contradicts it
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
(declare-const Z (Bag (Tuple Int Int Int)))
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t)
         (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
         (+ ((_ tuple.select 2) acc) 1)))
(assert (= Z ((_ table.aggr 0) f (tuple 0 0 0) X)))
(assert (= (bag.count (tuple 1 5) X) 2))
(check-sat)
