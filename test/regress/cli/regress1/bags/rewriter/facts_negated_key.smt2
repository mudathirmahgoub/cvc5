; A key equality under a negation is no fact: the rewriter reads keys off
; top-level assertions only (the bags-facts pass)
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X (Bag (Tuple Int Int)))
; column 0 is NOT a key of X: the rewriter must not record it as one
(assert (not (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X))))
; and X has a row twice; X = (bag (tuple 1 1) 2) satisfies both
(assert (not (= (bag.setof X) X)))
(check-sat)
