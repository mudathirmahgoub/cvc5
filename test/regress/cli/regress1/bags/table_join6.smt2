; REQUIRES: unrestricted-mode
; A join with no indices is a product; the proof prints it as
; (table.join @list.nil A B)
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Table Int))
(declare-fun B () (Table String))
(assert (bag.member (tuple 1) A))
(assert (bag.member (tuple "a") B))
(assert (not (bag.member (tuple 1 "a") (table.join A B))))
(check-sat)
