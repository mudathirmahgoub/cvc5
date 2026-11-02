; REQUIRES: unrestricted-mode
; DISABLE-TESTER: cpc
; (the cpc proof signature has no table.aggr)
; The rules read the columns of an accumulator only when it is a tuple: the
; accumulator below is a (Nullable Int), whose step is (nullable.some ..),
; and AGGREGATE_INTEGER_SUM took that for the tuple of its columns. The two
; aggregates differ in the names of their variables only.
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const T (Bag (Tuple Int Int)))
(assert
  (not (= ((_ table.aggr 0)
            (lambda ((t (Tuple Int Int)) (acc (Nullable Int)))
              (nullable.some (+ 1 (nullable.val acc))))
            (nullable.some 0)
            T)
          ((_ table.aggr 0)
            (lambda ((s (Tuple Int Int)) (a (Nullable Int)))
              (nullable.some (+ 1 (nullable.val a))))
            (nullable.some 0)
            T))))
(check-sat)
