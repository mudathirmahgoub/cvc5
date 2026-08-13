; EXPECT: unknown
(set-logic HO_ALL)
(set-option :sets-exp true)
; this problem is unsat, but the solver returns unknown for now: cardinality
; forces a slack element into S, and the only value satisfying the filter
; predicate is 5, which is already in S. Since we cannot justify the slack
; element, we report the model as untrustworthy rather than claim sat.
;(set-info :status unsat)
(set-info :status unknown)
(declare-fun S () (Set Int))
(assert (= (set.filter (lambda ((x Int)) (= x 5)) S) S))
(assert (> (set.card S) 1))
(check-sat)
