; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; Two cyclicity atoms over the same union operands, nested differently; the
; first branch is refuted, the second has a cycle of A U B U C.
; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic ALL)
(set-option :sets-exp true)
(set-option :rels-exp true)
(declare-const A (Relation Int Int))
(declare-const B (Relation Int Int))
(declare-const C (Relation Int Int))
(declare-const p Bool)
(assert (set.subset A (set.insert (tuple 1 2) (tuple 2 3) (set.singleton (tuple 3 1)))))
(assert (set.subset B (set.insert (tuple 1 2) (tuple 2 3) (set.singleton (tuple 3 1)))))
(assert (set.subset C (set.insert (tuple 1 2) (tuple 2 3) (set.singleton (tuple 3 1)))))
(assert (=> p (and (rel.cyclic (set.union A (set.union B C))) (not (set.member (tuple 3 1) A)) (not (set.member (tuple 3 1) B)) (not (set.member (tuple 3 1) C)))))
(assert (=> (not p) (rel.cyclic (set.union (set.union A B) C))))
(assert (not (set.member (tuple 1 2) B)))
(check-sat)
