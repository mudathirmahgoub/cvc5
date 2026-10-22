; REQUIRES: unrestricted-mode
; COMMAND-LINE: --no-arith-liastar-subsolver
; DISABLE-TESTER: proof
; The predicate x = 2z and x = 2w + 1 has rational solutions but no integer
; one, so the star of its solutions is {0} and (0, 0, 0, 5) is not in it,
; although y >= 0 has the recession direction (0, 0, 0, 1). The subsolver,
; which would prune the predicate, is disabled, so the Hilbert basis
; computation must find that there are no module generators.
(set-logic HO_ALL)
(set-info :status unsat)
(set-option :quiet true)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(assert (= a 0))
(assert (= b 0))
(assert (= c 0))
(assert (= d 5))
(assert (int.star-contains (lambda ((x Int) (z Int) (w Int) (y Int)) (and (= x (* 2 z)) (= x (+ (* 2 w) 1)) (>= y 0))) a b c d))
(check-sat)
