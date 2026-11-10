; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fmf-set-membership
; COMMAND-LINE:
; EXPECT: sat
; Membership of a variable in ground sets of an uninterpreted sort.
(set-logic ALL)
(set-option :finite-model-find true)
(declare-sort O 0)
(declare-fun S () (Set O))
(declare-fun T () (Set O))
(declare-fun U () (Set O))
(declare-const a O)
(declare-const b O)
(declare-const c O)
(assert (forall ((e O)) (=> (set.member e S) (set.member e T))))
(assert (forall ((e O)) (or (set.member e T) (set.member e U))))
(assert (distinct a b c))
(assert (set.member a S))
(assert (not (set.member b T)))
(assert (not (set.member c U)))
(check-sat)
