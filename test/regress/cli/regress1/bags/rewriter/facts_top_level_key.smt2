; A key asserted at the top level makes X a set: (bag.setof X) is X
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
; column 0 is a key of X, asserted: X has no row twice
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
(assert (not (= (bag.setof X) X)))
(check-sat)
