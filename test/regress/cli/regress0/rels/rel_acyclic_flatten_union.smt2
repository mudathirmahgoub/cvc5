; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-tc-subset
; EXPECT: unsat
; DISABLE-TESTER: cpc
;
; The negated acyclicity of a union is handled as the acyclicity of the list
; of its operands; every edge of R and S goes from X to Y, so no cycle exists.
(set-logic ALL)
(set-option :sets-exp true)
(declare-sort A 0)
(declare-fun R () (Set (Tuple A A)))
(declare-fun S () (Set (Tuple A A)))
(declare-fun X () (Set (Tuple A)))
(declare-fun Y () (Set (Tuple A)))
(assert (set.subset R (rel.product X Y)))
(assert (set.subset S (rel.product X Y)))
(assert (= (set.inter X Y) (as set.empty (Set (Tuple A)))))
(assert (rel.cyclic (set.union R S)))
(check-sat)
