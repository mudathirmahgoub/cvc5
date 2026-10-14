; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; Two cyclicity atoms over the same union operands, nested differently;
; A, B and C lie in an acyclic relation, so both branches are unsat.
; EXPECT: unsat
(set-logic ALL)
(set-option :sets-exp true)
(set-option :rels-exp true)
(declare-const A (Relation Int Int))
(declare-const B (Relation Int Int))
(declare-const C (Relation Int Int))
(declare-const p Bool)
(assert (set.subset A (set.insert (tuple 1 2) (tuple 2 3) (set.singleton (tuple 3 4)))))
(assert (set.subset B (set.insert (tuple 1 2) (tuple 2 3) (set.singleton (tuple 3 4)))))
(assert (set.subset C (set.insert (tuple 1 2) (tuple 2 3) (set.singleton (tuple 3 4)))))
(assert (=> p (rel.cyclic (set.union A (set.union B C)))))
(assert (=> (not p) (rel.cyclic (set.union (set.union A B) C))))
(check-sat)
