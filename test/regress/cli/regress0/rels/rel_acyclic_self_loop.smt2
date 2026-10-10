; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-tc-subset
; EXPECT: unsat
; DISABLE-TESTER: cpc
;
; A single-relation negated acyclicity constraint is a self-loop of the
; closure; with R subset X x Y, X and Y disjoint, the loop (s,s) would put s
; in both X and Y.
(set-logic ALL)
(set-option :sets-exp true)
(declare-sort A 0)
(declare-fun R () (Set (Tuple A A)))
(declare-fun X () (Set (Tuple A)))
(declare-fun Y () (Set (Tuple A)))
(assert (set.subset R (rel.product X Y)))
(assert (= (set.inter X Y) (as set.empty (Set (Tuple A)))))
(assert (rel.cyclic R))
(check-sat)
