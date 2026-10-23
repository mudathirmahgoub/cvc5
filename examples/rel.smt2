(set-logic ALL)
(declare-fun R () (Relation Int Int))
(assert (set.member (tuple 1 2) (rel.transpose R)))
(check-sat)
