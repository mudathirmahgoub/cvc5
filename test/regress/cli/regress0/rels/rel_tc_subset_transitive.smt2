; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-tc-subset
; EXPECT: unsat
; DISABLE-TESTER: cpc
;
; Closure induction (RELATION_TCLOSURE_SUBSET): R;R subset R makes R
; transitive, so (rel.tclosure R) subset R. Without the rule the closure-down
; split descends forever.
(set-logic ALL)
(set-option :sets-exp true)
(declare-sort A 0)
(declare-fun R () (Set (Tuple A A)))
(assert (set.subset (rel.join R R) R))
(declare-fun a () A)
(declare-fun b () A)
(assert (set.member (tuple a b) (rel.tclosure R)))
(assert (not (set.member (tuple a b) R)))
(check-sat)
