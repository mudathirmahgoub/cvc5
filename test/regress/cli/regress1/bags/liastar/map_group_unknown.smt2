; REQUIRES: normaliz
; DISABLE-TESTER: proof
; a fresh row of a group is a fresh element of the source of the map whose
; image is the group, which the subsolver mode does not invent, so the model
; is marked unsound
; COMMAND-LINE: --bags-to-liastar
; EXPECT: unknown
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int))) Int ((_ tuple.select 0) t))
(assert (= (bag.card (bag.setof A)) 3))
(assert (= (bag.card (bag.setof (bag.map f A))) 2))
(check-sat)
