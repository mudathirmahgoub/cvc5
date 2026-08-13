; EXPECT: unsat   -- Example 3 of the paper: both premises in the base relation
(set-logic ALL)
(declare-fun x () (Relation Int Int))
(assert (set.member (tuple 1 2) x))
(assert (set.member (tuple 2 3) x))
(assert (not (set.member (tuple 1 3) (rel.tclosure x))))
(check-sat)
