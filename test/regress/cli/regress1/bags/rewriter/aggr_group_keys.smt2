; REQUIRES: unrestricted-mode
; AGGREGATE_GROUP_KEYS: an aggregate that only copies its group columns has
; their distinct values as its rows, but a map that adds two group columns up
; can give two groups one row: for X = {(1, 2), (2, 1)} the sums are (3) twice.
; The terms are ground: a wrong value makes the problem unsat.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X (Bag (Tuple Int Int)))
(assert (= X (bag.union_disjoint (bag (tuple 1 2) 1) (bag (tuple 2 1) 1))))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
(define-fun S () (Bag (Tuple Int))
  (bag.map
    (lambda ((r (Tuple Int Int)))
      (tuple (+ ((_ tuple.select 0) r) ((_ tuple.select 1) r))))
    ((_ table.aggr 0 1) f (tuple 0 0) X)))
(assert (= (bag.count (tuple 3) S) 2))
(check-sat)
