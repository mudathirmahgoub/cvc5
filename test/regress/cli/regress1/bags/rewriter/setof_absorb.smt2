; REQUIRES: unrestricted-mode
; DISABLE-TESTER: cpc
; (the cpc proof signature has no table.aggr)
; SETOF_ABSORB: an inner bag.setof under a union and a bag.setof goes, so the
; aggregates over the two sets are one term
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const A (Bag (Tuple Int Int)))
(declare-const B (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0) (bag.setof (bag.union_disjoint (bag.setof A) B)))
                ((_ table.aggr 0) f (tuple 0 0) (bag.setof (bag.union_disjoint A B))))))
(check-sat)
