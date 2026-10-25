; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag (Tuple Int Int)))
(declare-fun B () (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int))) Int ((_ tuple.select 0) t))
; every row of the intersection is a row of A, group by group, so the
; projection of the intersection has no more distinct values than that of A
(assert (> (bag.card (bag.setof (bag.map f (bag.inter_min A B))))
           (bag.card (bag.setof (bag.map f A)))))
(check-sat)
