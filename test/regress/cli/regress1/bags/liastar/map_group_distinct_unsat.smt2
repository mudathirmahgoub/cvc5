; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int))) Int ((_ tuple.select 0) t))
; the rows of A with the same first column form one group of the projection,
; so the projection has at most as many distinct values as A has distinct rows
(assert (> (bag.card (bag.setof (bag.map f A))) (bag.card (bag.setof A))))
(check-sat)
