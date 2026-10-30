; REQUIRES: unrestricted-mode
; DISABLE-TESTER: cpc
; (the cpc proof signature has no table.aggr)
; INTERSECTION_SORT: the arguments of bag.inter_min are in one order, so the
; aggregates over two orders are one term
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const A (Bag (Tuple Int Int)))
(declare-const B (Bag (Tuple Int Int)))
(declare-const C (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0) (bag.inter_min (bag.inter_min A B) C))
                ((_ table.aggr 0) f (tuple 0 0) (bag.inter_min C (bag.inter_min B A))))))
(check-sat)
