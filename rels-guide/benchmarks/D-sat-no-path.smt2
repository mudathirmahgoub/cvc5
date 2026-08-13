; EXPECT: sat   -- no path from 1 to 4, must NOT be refuted
(set-logic ALL)
(declare-fun x () (Relation Int Int))
(assert (set.member (tuple 3 4) x))
(assert (set.member (tuple 1 2) (rel.tclosure x)))
(assert (not (set.member (tuple 1 4) (rel.tclosure x))))
(check-sat)
