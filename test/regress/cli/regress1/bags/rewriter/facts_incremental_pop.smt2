; A key asserted in a popped scope is no fact after the pop
; EXPECT: sat
; EXPECT: sat
(set-logic HO_ALL)
(set-option :incremental true)
(declare-const X (Bag (Tuple Int Int)))
(push 1)
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
(check-sat)
(pop 1)
; the key was asserted in a popped scope: X may repeat a row
(assert (not (= (bag.setof X) X)))
(check-sat)
