; REQUIRES: unrestricted-mode
; DISABLE-TESTER: cpc
; (the cpc proof signature has no table.aggr)
; SORTED_KEYS: the group columns of an aggregate are sorted and distinct, so
; listing them in another order or twice gives the same term
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int Int)))
(define-fun f ((t (Tuple Int Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) (+ ((_ tuple.select 2) acc) ((_ tuple.select 2) t))))
(assert (not (= ((_ table.aggr 1 0) f (tuple 0 0 0) X)
                ((_ table.aggr 0 1 0) f (tuple 0 0 0) X))))
(check-sat)
