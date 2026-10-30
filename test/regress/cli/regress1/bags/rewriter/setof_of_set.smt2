; REQUIRES: unrestricted-mode
; DISABLE-TESTER: cpc
; (the cpc proof signature has no table.aggr)
; SETOF_SETOF and SETOF_OF_SET: the set of a set is that set, so the
; aggregates over (bag.setof (bag.setof X)) and (bag.setof X) are one term
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0) (bag.setof (bag.setof X)))
                ((_ table.aggr 0) f (tuple 0 0) (bag.setof X)))))
(check-sat)
