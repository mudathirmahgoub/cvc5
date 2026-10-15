; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fmf-set-membership
; COMMAND-LINE:
; EXPECT: sat
; The full model checker reads (set.member (tuple u v) R) from the model value
; of R, like an uninterpreted predicate R(u, v) (--fmf-set-membership): the
; axioms are checked on the model without instantiating them for every pair.
(set-logic ALL)
(set-option :finite-model-find true)
(declare-sort O 0)
(declare-fun R () (Relation O O))
(declare-fun A () (Relation O O))
(declare-fun B () (Relation O O))
(assert (forall ((u O) (v O)) (=> (set.member (tuple u v) R) (or (set.member (tuple u v) A) (set.member (tuple u v) B)))))
(assert (forall ((u O) (v O)) (=> (set.member (tuple u v) A) (set.member (tuple v u) A))))
(assert (exists ((t1 O) (t2 O) (t3 O) (t4 O))
  (and (distinct t1 t2 t3 t4)
       (set.member (tuple t1 t2) R) (set.member (tuple t1 t2) A)
       (set.member (tuple t2 t3) R) (set.member (tuple t2 t3) B)
       (set.member (tuple t3 t4) R) (set.member (tuple t3 t4) A)
       (set.member (tuple t4 t1) R) (set.member (tuple t4 t1) B))))
(check-sat)
