; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-acyclic-hammer
; EXPECT: sat
; Join grounding conflict of --rels-acyclic-hammer when the membership is on a
; set S that equals the join only in one branch: the conflict must state
; S = A;B. Without it, the conflict refuted (a, c) in S also in the branch
; S = T, which is a model, and the answer was unsat.
(set-logic ALL)
(declare-sort U 0)
(declare-fun A () (Relation U U))
(declare-fun B () (Relation U U))
(declare-fun S () (Relation U U))
(declare-fun T () (Relation U U))
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(assert (distinct a b c d))
(assert (= A (set.singleton (tuple a b))))
(assert (= B (set.singleton (tuple d c))))
(assert (set.member (tuple a c) S))
(assert (or (= S (rel.join A B)) (= S T)))
(check-sat)
