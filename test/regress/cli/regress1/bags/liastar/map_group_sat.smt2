; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the fresh elements of the groups cannot be read back by the subsolver mode
; (which answers unknown here, see map_group_unknown.smt2), so the elements
; mode introduces them as terms the theory reasons about
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar --bags-liastar-model=elements
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int))) Int ((_ tuple.select 0) t))
; three distinct rows whose first columns take two values
(assert (= (bag.card (bag.setof A)) 3))
(assert (= (bag.card (bag.setof (bag.map f A))) 2))
(check-sat)
