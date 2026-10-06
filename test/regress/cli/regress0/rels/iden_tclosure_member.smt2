; REQUIRES: unrestricted-mode
; EXPECT: unsat
; A membership in the closure of an identity relation has equal components.
(set-logic ALL)
(declare-fun A () (Set (Tuple Int)))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (set.member (tuple x y) (rel.tclosure (rel.iden A))))
(assert (distinct x y))
(check-sat)
