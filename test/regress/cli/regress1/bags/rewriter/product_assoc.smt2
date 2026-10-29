; PRODUCT_ASSOC: products are right-nested, so the two groupings of three
; factors are one term, and so are the aggregates over them
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const A (Bag (Tuple Int)))
(declare-const B (Bag (Tuple Int)))
(declare-const C (Bag (Tuple Int)))
(define-fun f ((t (Tuple Int Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 2) t))))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0) (table.product (table.product A B) C))
                ((_ table.aggr 0) f (tuple 0 0) (table.product A (table.product B C))))))
(check-sat)
