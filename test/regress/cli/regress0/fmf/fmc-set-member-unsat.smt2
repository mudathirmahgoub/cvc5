; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fmf-set-membership
; COMMAND-LINE:
; EXPECT: unsat
; As fmc-set-member-tuple, but the cycle has an edge in R outside A and B.
(set-logic ALL)
(set-option :finite-model-find true)
(declare-sort O 0)
(declare-fun R () (Relation O O))
(declare-fun A () (Relation O O))
(declare-fun B () (Relation O O))
(assert (forall ((u O) (v O)) (=> (set.member (tuple u v) R) (or (set.member (tuple u v) A) (set.member (tuple u v) B)))))
(assert (forall ((u O) (v O)) (=> (set.member (tuple u v) A) (set.member (tuple v u) A))))
(assert (exists ((t1 O) (t2 O) (t3 O))
  (and (distinct t1 t2 t3)
       (set.member (tuple t1 t2) R) (set.member (tuple t2 t1) A)
       (set.member (tuple t2 t3) R)
       (not (set.member (tuple t2 t3) A)) (not (set.member (tuple t2 t3) B)))))
(check-sat)
