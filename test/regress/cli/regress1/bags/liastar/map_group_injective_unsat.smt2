; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(define-fun f ((i Int)) Int (+ i 1))
; an injective map sends distinct elements to distinct elements, so the
; number of distinct elements is preserved
(assert (= (bag.card (bag.setof A)) 2))
(assert (= (bag.card (bag.setof (bag.map f A))) 1))
(check-sat)
