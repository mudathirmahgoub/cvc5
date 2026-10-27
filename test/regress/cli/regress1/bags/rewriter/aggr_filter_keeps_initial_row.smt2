; FILTER_AGGREGATE moves a filter on group columns below the aggregate only when
; the conjuncts that stay reject the row of initial values, which the aggregate
; of an empty table has: here no conjunct stays, and the claim is false for
; X = {(1)}
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X (Bag (Tuple Int)))
(define-fun f ((t (Tuple Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
(define-fun G () (Bag (Tuple Int Int)) ((_ table.aggr 0) f (tuple 0 0) X))
(define-fun F ((r (Tuple Int Int))) Bool (> ((_ tuple.select 0) r) 3))
(define-fun Gp () (Bag (Tuple Int Int))
  ((_ table.aggr 0) f (tuple 0 0) (bag.filter (lambda ((t (Tuple Int))) (> ((_ tuple.select 0) t) 3)) X)))
; claim: (bag.filter F G) = Gp, false for X = {(1)}: the left is empty, the right is {(0, 0)}
(assert (not (= (bag.filter F G) Gp)))
(check-sat)
