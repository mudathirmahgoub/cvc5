; EXPECT: unsat   -- same shape but the base relation has no asserted member
(set-logic ALL)
(declare-fun x () (Relation Int Int))
(assert (set.member (tuple 2 3) (rel.tclosure x)))
(assert (set.member (tuple 1 2) (rel.tclosure x)))
(assert (not (set.member (tuple 1 3) (rel.tclosure x))))
(check-sat)
