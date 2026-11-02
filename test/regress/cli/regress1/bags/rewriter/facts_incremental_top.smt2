; A key asserted in the outermost scope is a fact for every later check
; EXPECT: sat
; EXPECT: unsat
(set-logic HO_ALL)
(set-option :incremental true)
(declare-const X (Bag (Tuple Int Int)))
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
(check-sat)
(assert (not (= (bag.setof X) X)))
(check-sat)
