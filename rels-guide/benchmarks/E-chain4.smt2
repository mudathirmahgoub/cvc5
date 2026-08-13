; EXPECT: unsat  -- longer mixed chain 1 ->t 2 ->x 3 ->t 4 ->x 5
(set-logic ALL)
(declare-fun x () (Relation Int Int))
(assert (set.member (tuple 1 2) (rel.tclosure x)))
(assert (set.member (tuple 2 3) x))
(assert (set.member (tuple 3 4) (rel.tclosure x)))
(assert (set.member (tuple 4 5) x))
(assert (not (set.member (tuple 1 5) (rel.tclosure x))))
(check-sat)
