; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; EXPECT: unsat
; (rel.rclosure (A U B)) is rewritten to (rel.rclosure A) U (rel.rclosure B).
(set-logic ALL)
(set-option :rels-exp true)
(declare-const A (Relation Int Int))
(declare-const B (Relation Int Int))
(assert (set.member (tuple 5 5) (rel.rclosure (set.union A B))))
(assert (= A (as set.empty (Relation Int Int))))
(assert (= B (as set.empty (Relation Int Int))))
(check-sat)
