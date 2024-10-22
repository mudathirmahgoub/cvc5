; EXPECT: sat
(set-logic HO_ALL)
(set-option :produce-models true)
(set-option :dag-thresh 0)
(declare-const A (Set Int))
(assert (not (set.is_empty A)))
(assert (set.all (lambda ((x Int)) (set.some (lambda ((y Int)) (>= x y)) A)) A))
;; (assert (forall ((x Int)) (=> (set.member x A) (exists ((y Int)) (and (set.member y A) (>= x y))))))
(check-sat)

