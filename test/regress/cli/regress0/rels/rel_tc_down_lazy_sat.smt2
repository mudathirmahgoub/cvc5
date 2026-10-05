; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-tc-down-lazy
; EXPECT: sat
;
; With the lazy closure split the membership is still grounded, at last call.
(set-logic ALL)
(set-option :sets-exp true)
(declare-sort A 0)
(declare-fun R () (Set (Tuple A A)))
(declare-fun a () A)
(declare-fun b () A)
(assert (set.member (tuple a b) (rel.tclosure R)))
(assert (not (set.member (tuple a b) R)))
(check-sat)
