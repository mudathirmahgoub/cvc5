; EXPECT: unsat   -- TClos Up I then TClos Up II
(set-logic ALL)
(declare-fun x () (Relation Int Int))
(assert (set.member (tuple 2 3) x))
(assert (set.member (tuple 1 2) (rel.tclosure x)))
(assert (not (set.member (tuple 1 3) (rel.tclosure x))))
(check-sat)
