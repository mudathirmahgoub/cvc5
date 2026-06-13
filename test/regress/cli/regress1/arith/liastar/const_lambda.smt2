; REQUIRES: normaliz
; A constant-function predicate (lambda x y. x=1 and y=31) is rewritten by the
; UF rewriter into a FUNCTION_ARRAY_CONST; the lia* code must convert it back
; to a lambda instead of indexing a 0-child node (previously a segfault).
(set-logic HO_ALL)
(set-info :status unsat)
(assert (int.star-contains
  (lambda ((x Int)(y Int)) (and (= x 1)(= y 31))) 1 30))
(check-sat)
