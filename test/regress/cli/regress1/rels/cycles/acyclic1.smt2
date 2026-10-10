; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
(set-logic ALL)
(set-info :status sat)
(set-option :rels-exp true)

(assert (not (rel.cyclic (as set.empty (Relation Int Int)))))
(assert (not (rel.cyclic (set.singleton (tuple 0 1)))))
(check-sat)