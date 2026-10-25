; REQUIRES: normaliz
; COMMAND-LINE: --sets-to-bags=setof --bags-to-liastar
; EXPECT: unsat
; --sets-to-bags enables the higher-order logic and non-linear arithmetic that
; --bags-to-liastar requires.
(set-logic QF_UFLIAFS)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(assert (set.subset A B))
(assert (> (set.card A) (set.card B)))
(check-sat)
