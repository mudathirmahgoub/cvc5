; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-tc-subset
; EXPECT: unsat
; DISABLE-TESTER: cpc
;
; Closure induction: R subset X x Y with X and Y disjoint means no two edges
; of R compose, so (rel.tclosure R) = R.
(set-logic ALL)
(set-option :sets-exp true)
(declare-sort A 0)
(declare-fun R () (Set (Tuple A A)))
(declare-fun X () (Set (Tuple A)))
(declare-fun Y () (Set (Tuple A)))
(assert (set.subset R (rel.product X Y)))
(assert (= (set.inter X Y) (as set.empty (Set (Tuple A)))))
(declare-fun a () A)
(declare-fun b () A)
(assert (set.member (tuple a b) (rel.tclosure R)))
(assert (not (set.member (tuple a b) R)))
(check-sat)
