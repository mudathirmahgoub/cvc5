; A keyed aggregate in a product whose filter tests its counter is the map of
; its rows (AGGREGATE_KEYED)
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
(declare-const Y (Bag (Tuple Int)))
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
(define-fun G () (Bag (Tuple Int Int)) ((_ table.aggr 0) f (tuple 0 0) X))
; the filter tests G's counter: the keyed rows give the same result
(assert (not (= (bag.filter (lambda ((r (Tuple Int Int Int))) (>= ((_ tuple.select 1) r) 1)) (table.product G Y))
                (table.product (bag.map (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t) 1)) X) Y))))
(check-sat)
