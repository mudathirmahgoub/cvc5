; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bags-lazy-fold
; A lazy fold is assigned a value in model construction, like set.choose: its
; value is stated by its unrolling at last call. Evaluating it instead waits
; for the value of its bag, and here the bag's elements wait for the fold:
; (bag.fold (lambda ((t T) (acc U)) ((_ tuple.select 0) t)) i B) is in one
; equivalence class with column 0 of a row of B. That was a deadlock in model
; construction, and a fatal error.
; SELECT b, COUNT(*) FROM t GROUP BY b and SELECT b, COUNT(a) FROM t GROUP BY b
; differ on t = {(NULL, 'A')}: COUNT(a) is 0 there.
(set-logic HO_ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-const t (Bag (Tuple (Nullable Int) (Nullable String))))
; COUNT(*) by b
(define-fun star ((x (Tuple (Nullable String))) (y (Tuple (Nullable String) (Nullable Int))))
                 (Tuple (Nullable String) (Nullable Int))
  (tuple ((_ tuple.select 0) x)
         (nullable.some (+ (nullable.val ((_ tuple.select 1) y)) 1))))
; COUNT(a) by b
(define-fun of_a ((x (Tuple (Nullable String) (Nullable Int))) (y (Tuple (Nullable String) (Nullable Int))))
                 (Tuple (Nullable String) (Nullable Int))
  (tuple ((_ tuple.select 0) x)
         (ite (nullable.is_null ((_ tuple.select 1) x))
              ((_ tuple.select 1) y)
              (nullable.some (+ (nullable.val ((_ tuple.select 1) y)) 1)))))
(assert
  (not (= ((_ table.aggr 0) star (tuple (as nullable.null (Nullable String)) (nullable.some 0))
                            ((_ table.project 1) t))
          ((_ table.aggr 0) of_a (tuple (as nullable.null (Nullable String)) (nullable.some 0))
                            ((_ table.project 1 0) t)))))
(check-sat)
