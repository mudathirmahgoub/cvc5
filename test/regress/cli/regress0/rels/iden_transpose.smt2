; REQUIRES: unrestricted-mode
; EXPECT: unsat
; An identity relation is symmetric.
(set-logic ALL)
(declare-fun A () (Set (Tuple Int)))
(assert (not (= (rel.transpose (rel.iden A)) (rel.iden A))))
(check-sat)
