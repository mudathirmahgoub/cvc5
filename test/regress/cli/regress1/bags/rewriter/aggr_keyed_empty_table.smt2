; AGGREGATE_KEYED turns an aggregate grouped by a key into a map only where its
; row of initial values is dropped: for an empty X the aggregate is {(0, 0)},
; the map is empty
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X (Bag (Tuple Int Int)))
; column 0 is a key of X
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
; claim: the aggregate is the map of its one-row groups, false for X empty:
; the left is {(0, 0)}, the right is empty
(assert (not (= ((_ table.aggr 0) f (tuple 0 0) X)
                (bag.map (lambda ((t (Tuple Int Int))) (f t (tuple 0 0))) X))))
(check-sat)
