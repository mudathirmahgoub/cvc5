; REQUIRES: unrestricted-mode
; EQ_EMPTY_ARG, by static learning: the rows of emp with no row in dept, a
; NOT EXISTS whose subquery filters a map of dept, and the same over dept
;   SELECT * FROM emp e WHERE NOT EXISTS
;     (SELECT * FROM (SELECT d.id, 1 FROM dept d) v WHERE v.id = e.dept)
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun emp () (Table Int Int))
(declare-fun dept () (Table Int String))
(assert
 (not
  (= (bag.filter
       (lambda ((e (Tuple Int Int)))
         (= (bag.filter
              (lambda ((v (Tuple Int Int)))
                (= ((_ tuple.select 0) v) ((_ tuple.select 1) e)))
              (bag.map
                (lambda ((d (Tuple Int String))) (tuple ((_ tuple.select 0) d) 1))
                dept))
            (as bag.empty (Bag (Tuple Int Int)))))
       emp)
     (bag.filter
       (lambda ((e (Tuple Int Int)))
         (= (bag.filter
              (lambda ((d (Tuple Int String)))
                (= ((_ tuple.select 0) d) ((_ tuple.select 1) e)))
              dept)
            (as bag.empty (Bag (Tuple Int String)))))
       emp))))
(check-sat)
