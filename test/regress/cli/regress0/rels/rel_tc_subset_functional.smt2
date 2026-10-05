; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-tc-subset --rels-functional-axioms
; EXPECT: unsat
; DISABLE-TESTER: cpc
;
; The rels-axioms pass turns the functionality axiom of J into
; J^T;J subset (rel.iden universe); hence J;J^T is transitive and contains the
; closure of every relation included in it.
(set-logic ALL)
(set-option :sets-exp true)
(declare-sort A 0)
(declare-fun J () (Set (Tuple A A)))
(declare-fun R () (Set (Tuple A A)))
(assert (forall ((x A) (y A) (z A)) (=> (and (set.member (tuple x y) J) (set.member (tuple x z) J)) (= y z))))
(define-fun loc () (Set (Tuple A A)) (rel.join J (rel.transpose J)))
(assert (set.subset R loc))
(declare-fun a () A)
(declare-fun b () A)
(assert (set.member (tuple a b) (rel.tclosure R)))
(assert (not (set.member (tuple a b) loc)))
(check-sat)
