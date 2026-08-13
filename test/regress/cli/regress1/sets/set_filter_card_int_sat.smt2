; EXPECT: sat
(set-logic HO_ALL)
(set-option :sets-exp true)
(set-info :status sat)
; As set_filter_card_sat.smt2, but the elements excluded from the filtered set
; must additionally *not* satisfy the predicate.
(declare-fun S () (Set Int))
(assert (= (set.card (set.minus S (set.filter (lambda ((x Int)) (> x 100)) S))) 2))
(assert (> (set.card S) 3))
(check-sat)
