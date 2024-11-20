; EXPECT: sat
(set-logic HO_ALL)
(set-option :produce-models true)
(set-option :dag-thresh 0)
(declare-const A (Set Int))
(assert (set.some (lambda ((x Int)) (set.some (lambda ((y Int)) (> x y)) A)) A))
;; (assert (exists ((x Int)) (and (set.member x A) (exists ((y Int)) (and (set.member y A) (> x y))))))
(check-sat)
