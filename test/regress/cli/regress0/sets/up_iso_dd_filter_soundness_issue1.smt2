; EXPECT: unsat
(set-logic HO_ALL)
(declare-const A (Set (Tuple Int)))
(declare-const n (Set (Tuple Int Int)))
(assert (distinct (rel.product A n) (as set.empty (Set (Tuple Int Int Int)))))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_2 (Tuple Int))) true) A)))
(check-sat)
