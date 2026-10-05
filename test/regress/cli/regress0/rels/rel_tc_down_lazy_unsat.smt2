; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-tc-down-lazy
; EXPECT: unsat
; DISABLE-TESTER: cpc
(set-logic ALL)
(set-option :sets-exp true)
(declare-sort A 0)
(declare-fun R () (Set (Tuple A A)))
(declare-fun a () A)
(declare-fun b () A)
(assert (= R (as set.empty (Set (Tuple A A)))))
(assert (set.member (tuple a b) (rel.tclosure R)))
(check-sat)
