; REQUIRES: normaliz
; DISABLE-TESTER: proof
; two projections in a row: the star alone relates each map to its source, and
; the element-wise rules of the elements mode supply the rows of the middle bag
; COMMAND-LINE: --bags-to-liastar --bags-liastar-model=elements
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag (Tuple Int Int Int)))
(define-fun f ((t (Tuple Int Int Int))) (Tuple Int Int) (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
(define-fun g ((t (Tuple Int Int))) Int ((_ tuple.select 0) t))
; projections only merge rows, so the number of distinct values never grows
(assert (> (bag.card (bag.setof (bag.map g (bag.map f A)))) (bag.card (bag.setof A))))
(check-sat)
