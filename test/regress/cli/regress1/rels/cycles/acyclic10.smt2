; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; EXPECT: unknown
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :rels-exp true)
; Test reflexive and reflexive transitive closure parsing. The solver has no
; rules for the reflexive closure of a variable, so it answers unknown.

(declare-fun R1 () (Set (Tuple Int Int))) 
(declare-fun R2 () (Set (Tuple Int Int))) 

(assert (= R1 (rel.rclosure R2)))
(assert (= R1 (rel.rtclosure R2)))
(check-sat)