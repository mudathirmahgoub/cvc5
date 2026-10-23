(set-logic ALL)
(declare-fun p () (Tuple (Set Int) Int))
(assert (set.member 1 ((_ tuple.select 0) p)))
(check-sat)
