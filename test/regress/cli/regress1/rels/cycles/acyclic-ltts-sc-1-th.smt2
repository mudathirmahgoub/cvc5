; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --e-matching --inst-when=full --rels-acyclic-anchor=inclusion --rels-acyclic-backward-chords --no-check-unsat-cores
; EXPECT: unsat
; DISABLE-TESTER: cpc
;
; Litmus-template completeness query for sequential consistency with one
; thread (sc-1-th of rachelcleaveland/relational-solver-benchmarks): is there
; an execution with a cycle in rf U po U co U fr that none of the coherence
; templates ((po+ inter same-address) ; rf/co/fr irreflexive) catches? With one
; thread program order is total, so every com edge of such a cycle is either
; backward in po+ (caught by a template) or forward, and then the whole cycle
; lies in po+, which is acyclic. The cycle witness of the negated acyclicity
; has no a-priori length bound; with --rels-acyclic-backward-chords the
; minimality rule forbids closure edges in both directions between
; non-adjacent witness elements, so the totality axiom bounds the witness to
; three elements. Without the option this query does not terminate within
; minutes under --inst-when=full. The unsat-core check is disabled because the
; core is re-checked without these options; the CPC proof check is disabled
; because the exported proof has a quant-dt-split step whose side condition
; mentions rel.acyclic, which the CPC signature does not define.
(set-logic ALL)
(set-option :finite-model-find true)
(set-option :sets-exp true)
(declare-sort Atom 0)
(declare-sort Thread 0)
(declare-fun iden () (Set (Tuple Atom Atom)))
(declare-fun univ () (Set (Tuple Atom)))
(declare-fun Address () (Set (Tuple Atom)))
(declare-fun Event () (Set (Tuple Atom)))
(declare-fun po () (Set (Tuple Atom Atom)))
(declare-fun address () (Set (Tuple Atom Atom)))
(declare-fun Read () (Set (Tuple Atom)))
(declare-fun Write () (Set (Tuple Atom)))
(declare-fun rf () (Set (Tuple Atom Atom)))
(declare-fun co () (Set (Tuple Atom Atom)))
(declare-fun fr () (Set (Tuple Atom Atom)))
(declare-fun Thread_set () (Set (Tuple Thread)))
(declare-fun thread (Atom) Thread)
(declare-fun rd_from_initial () (Set (Tuple Atom)))
(declare-fun addr_addr_set () (Set (Tuple Atom Atom)))
(define-fun irreflexive ((r (Set (Tuple Atom Atom)))) Bool
  (and
    (set.subset r (rel.product Event Event))
    (= (set.inter r iden) (as set.empty (Set (Tuple Atom Atom))))
  )
)
(define-fun transitive ((r (Set (Tuple Atom Atom)))) Bool
  (and
    (set.subset r (rel.product Event Event))
    (set.subset (rel.join r r) r)
  )
)
(define-fun total ((r (Set (Tuple Atom Atom))) (bag (Set (Tuple Atom)))) Bool
  (and
    (set.subset r (rel.product Event Event))
    (set.subset bag Event)
    (forall ((e1 Atom) (e2 Atom))
        (=> (and
                (not (= e1 e2))
                (set.member (tuple e1) bag)
                (set.member (tuple e2) bag))
            (set.member (tuple e1 e2) (set.union r (rel.transpose r)))
        )
    )
    (not (rel.cyclic r))
  )
)
(define-fun lone_set ((r (Set (Tuple Atom)))) Bool
  (or (set.is_singleton r) (= r (as set.empty (Set (Tuple Atom)))))
)
(define-fun not_sc_mcm () Bool
  ;; === CHANGED FOR FULL: SC = acyclic(rf U po U co U fr)  (was rf U po) ===
  (rel.cyclic (set.union rf (set.union po (set.union co fr))))
)
(assert (forall ((a Atom) (b Atom)) (and
  (=> (set.member (tuple a b) iden) (and (= a b) (set.member (tuple a) univ)))
  (=> (and (= a b) (set.member (tuple a) univ)) (set.member (tuple a b) iden))
  )))
(assert (forall ((a Atom)) (set.member (tuple a) univ)))
(assert (= (set.inter Event Address) (as set.empty (Set (Tuple Atom)))))
(assert (set.subset po (rel.product Event Event)))
(assert (forall ((e Atom))
  (=> (set.member (tuple e) Event)
      (lone_set (rel.join (set.singleton (tuple e)) po)))))
(assert (set.subset address (rel.product Event Address)))
(assert (forall ((e1 Atom) (e2 Atom) (e3 Atom))
  (=> (and (set.member (tuple e1 e2) address) (set.member (tuple e1 e3) address)) ; pre
      (= e2 e3) ; post
)))
(assert (forall ((e1 Atom)) (=> (set.member (tuple e1) Event)
      (exists ((addr Atom)) (set.member (tuple e1 addr) address))))
)
(assert (= (set.inter Read Write) (as set.empty (Set (Tuple Atom)))))
(assert (= (set.union Read Write) Event))
(assert (set.subset rf (rel.product Write Read)))
(assert (set.subset co (rel.product Write Write)))
  ;;   thread(x) = thread(y)  =>  (x,y) in po+  \/  (y,x) in po+  \/  x = y
(assert (forall ((x Atom) (y Atom))
(=> (and (set.member (tuple x) Event) (set.member (tuple y) Event)
            (= (thread x) (thread y)))
    (or (set.member (tuple x y) (rel.tclosure po))
        (set.member (tuple y x) (rel.tclosure po))
        (= x y)))))
(assert (= (set.union Address Event) univ))
(assert (= rd_from_initial (set.minus Read (rel.join Write rf))))
(assert (forall ((e1 Atom) (e2 Atom))
  (=> (set.member (tuple e1 e2) addr_addr_set)
    (and (set.member (tuple e1) rd_from_initial) (set.member (tuple e2) Write))
  )))
  ; This may be a bug -- do we need to say that e1 and e2 are to the same address?
(assert (forall ((e1 Atom) (e2 Atom))
  (=> (and (set.member (tuple e1) rd_from_initial) (set.member (tuple e2) Write))
    (set.member (tuple e1 e2) addr_addr_set)
  )))
(assert (= fr (set.union
  (rel.join (rel.transpose rf) co)
  addr_addr_set)))
(assert (set.subset fr (rel.product Read Write)))
(assert (forall ((e (Tuple Atom)) (r (Tuple Atom Atom)))
  (=> (set.member e Event)
      (lone_set (rel.join (set.singleton e) (rel.transpose po))))))
(assert (set.subset
  (set.union (set.union fr rf) co)  ; com
  (rel.join address (rel.transpose address))))
(assert (set.subset (rel.join rf (rel.transpose rf)) iden))
(assert (= rf (rel.tclosure rf)))
(assert (transitive co))
(assert (forall ((a (Tuple Atom)))
  (=> (set.member a Address)
      (total co (set.inter (rel.join (set.singleton a) (rel.transpose address)) Write)))))
(assert (not (rel.cyclic po)))
(assert (irreflexive (rel.join
  (set.inter (rel.tclosure po) (rel.join address (rel.transpose address)))
  rf)))
(assert (irreflexive (rel.join
  (set.inter (rel.tclosure po) (rel.join address (rel.transpose address)))
  co)))
(assert (irreflexive (rel.join
  (set.inter (rel.tclosure po) (rel.join address (rel.transpose address)))
  fr)))
(assert (forall ((e Atom)) (=> (set.member (tuple e) Event)
    (set.member (tuple (thread e)) Thread_set))))
(assert (set.is_singleton Thread_set))
(assert not_sc_mcm)
(check-sat)
