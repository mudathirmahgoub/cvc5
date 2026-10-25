; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag (Tuple Int Int)))
(declare-fun B () (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int))) Int ((_ tuple.select 1) t))
; both projections group the rows by the second column, so a group that is
; nonempty in the projection of A is nonempty in the projection of B
(assert (bag.subbag A B))
(assert (> (bag.card (bag.setof (bag.map f A))) (bag.card (bag.setof (bag.map f B)))))
(check-sat)
