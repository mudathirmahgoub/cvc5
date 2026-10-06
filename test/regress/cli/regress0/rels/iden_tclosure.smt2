; REQUIRES: unrestricted-mode
; EXPECT: unsat
; An identity relation is its own transitive closure.
(set-logic ALL)
(declare-fun A () (Set (Tuple Int)))
(assert (not (= (rel.tclosure (rel.iden A)) (rel.iden A))))
(check-sat)
