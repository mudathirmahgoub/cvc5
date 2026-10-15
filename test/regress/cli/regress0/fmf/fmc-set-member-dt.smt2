; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fmf-set-membership
; COMMAND-LINE:
; EXPECT: sat
; A relation between an uninterpreted sort and a datatype, defined by a
; function, as the anomaly benchmarks state the types of events.
(set-logic ALL)
(set-option :finite-model-find true)
(declare-sort O 0)
(declare-datatypes ((K 0)) (((k1) (k2) (k3))))
(declare-fun kind (O) K)
(declare-fun kind_rel () (Relation O K))
(declare-fun R () (Relation O O))
(assert (forall ((a O) (b K)) (= (set.member (tuple a b) kind_rel) (= (kind a) b))))
(assert (forall ((u O) (v O)) (=> (set.member (tuple u v) R) (set.member (tuple v k2) kind_rel))))
(assert (exists ((t1 O) (t2 O)) (and (distinct t1 t2) (set.member (tuple t1 t2) R) (set.member (tuple t1 k1) kind_rel))))
(check-sat)
