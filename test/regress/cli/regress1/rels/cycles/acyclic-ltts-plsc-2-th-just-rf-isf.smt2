; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-acyclic-anchor=inclusion --inst-when=full-delay --rels-acyclic-backward-chords --prenex-quant=none --rels-tc-subset --rels-tc-down-lazy --no-check-unsat-cores
; EXPECT: unsat
; DISABLE-TESTER: cpc
;
; plsc-2-th-just-rf of rachelcleaveland/relational-solver-benchmarks (finite model finding off) with the
; functionality axioms of po, po^T and address stated with rel.is-functional. Closure
; induction uses (rel.is-functional address) to see that loc = address;address^T is
; transitive, without the rels-axioms pass.
;; ==== mcm: Toy ====
(set-logic ALL)
(set-option :produce-models true)
;; finite-model-find: needed for sat with the universally-quantified constraints
;; (set-option :finite-model-find true)
;; sets/relations extensions (this cvc5 uses :sets-exp / :rels-exp; the older
;; :sets-ext name prints "unsupported"). Needed for set.universe / set.complement.
(set-option :sets-exp true)
(set-option :rels-exp true)

(declare-sort Atom 0)
(declare-sort Thread 0)

;; ---- fundamental relations / sets of a candidate execution ----
(declare-fun iden () (Set (Tuple Atom Atom)))
(declare-fun univ () (Set (Tuple Atom)))
(declare-fun Address () (Set (Tuple Atom)))
(declare-fun Event () (Set (Tuple Atom)))       ;; all events
(declare-fun MemEvent () (Set (Tuple Atom)))    ;; memory events (Read u+ Write)
(declare-fun Fence () (Set (Tuple Atom)))       ;; fence events
(declare-fun Read () (Set (Tuple Atom)))
(declare-fun Write () (Set (Tuple Atom)))
(declare-fun po () (Set (Tuple Atom Atom)))
(declare-fun address () (Set (Tuple Atom Atom)))
(declare-fun rf () (Set (Tuple Atom Atom)))
(declare-fun Thread_set () (Set (Tuple Thread)))
(declare-fun thread (Atom) Thread)
;; herd primitives used by cat models:
(declare-fun loc () (Set (Tuple Atom Atom)))

;; ---- helpers (memory-relation domain restrictions use MemEvent) ----
(define-fun irreflexive ((r (Set (Tuple Atom Atom)))) Bool
  (and (set.subset r (rel.product Event Event))
       (= (set.inter r iden) (as set.empty (Set (Tuple Atom Atom))))))
(define-fun transitive ((r (Set (Tuple Atom Atom)))) Bool
  (and (set.subset r (rel.product Event Event))
       (set.subset (rel.join r r) r)))
(define-fun total ((r (Set (Tuple Atom Atom))) (bag (Set (Tuple Atom)))) Bool
  (and (set.subset r (rel.product MemEvent MemEvent))
       (set.subset bag MemEvent)
       (forall ((e1 Atom) (e2 Atom))
         (=> (and (not (= e1 e2))
                  (set.member (tuple e1) bag) (set.member (tuple e2) bag))
             (set.member (tuple e1 e2) (set.union r (rel.transpose r)))))
       (not (rel.cyclic r))))
(define-fun lone_set ((r (Set (Tuple Atom)))) Bool
  (or (set.is_singleton r) (= r (as set.empty (Set (Tuple Atom))))))

;; ---- iden / univ ----
(assert (forall ((a Atom) (b Atom)) (and
  (=> (set.member (tuple a b) iden) (and (= a b) (set.member (tuple a) univ)))
  (=> (and (= a b) (set.member (tuple a) univ)) (set.member (tuple a b) iden)))))
(assert (forall ((a Atom)) (set.member (tuple a) univ)))

;; ---- event universe: Event = MemEvent u+ Fence ; univ = Event u+ Address ----
(assert (= (set.inter MemEvent Fence) (as set.empty (Set (Tuple Atom)))))
(assert (= (set.union MemEvent Fence) Event))
(assert (= (set.inter Event Address) (as set.empty (Set (Tuple Atom)))))
(assert (= (set.union Event Address) univ))
;; ---- memory events: MemEvent = Read u+ Write ----
(assert (= (set.inter Read Write) (as set.empty (Set (Tuple Atom)))))
(assert (= (set.union Read Write) MemEvent))

;; ---- po: over ALL events (memory and fences); at most one successor/
;;      predecessor, acyclic; same-thread events are po-ordered ----
(assert (set.subset po (rel.product Event Event)))
;; REDUCTION change of po unique child definition
(assert (rel.is-functional po))
(assert (rel.is-functional (rel.transpose po)))
(assert (forall ((x Atom) (y Atom))
  (=> (and (set.member (tuple x) Event) (set.member (tuple y) Event)
           (= (thread x) (thread y)))
      (or (set.member (tuple x y) (rel.tclosure po))
          (set.member (tuple y x) (rel.tclosure po))
          (= x y)))))

;; ---- address (each MEMORY event accesses one address); loc = same-address ----
(assert (set.subset address (rel.product MemEvent Address)))
(assert (rel.is-functional address))
(assert (forall ((e1 Atom)) (=> (set.member (tuple e1) MemEvent)
  (exists ((a Atom)) (set.member (tuple e1 a) address)))))
(assert (= loc (rel.join address (rel.transpose address))))

;; ---- rf: Write->Read, each read reads from at most one write; rf+ = rf ----
(assert (set.subset rf (rel.product Write Read)))
(assert (set.subset (rel.join rf (rel.transpose rf)) iden))
(assert (= rf (rel.tclosure rf)))

;; ---- communication (rf) stays within the same address ----
(assert (set.subset rf
                    (rel.join address (rel.transpose address))))

;; ---- Thread_set = { thread(e) | e in Event }. The thread COUNT / cardinality
;;      is user-provided (with the litmus test), so it is NOT asserted here. ----
(assert (forall ((e Atom)) (=> (set.member (tuple e) Event)
    (set.member (tuple (thread e)) Thread_set))))

;; ---- mcm definitions (translated `let`s) ----
(define-fun com () (Set (Tuple Atom Atom)) rf)
(define-fun po-loc () (Set (Tuple Atom Atom)) (set.inter (rel.tclosure po) loc))
(define-fun ghb () (Set (Tuple Atom Atom)) (set.union po-loc com))

;; ---- memory consistency model (conjunction of checks) ----
(define-fun mcm () Bool
  (and
    (not (rel.cyclic ghb))   ; sc-per-loc
    (irreflexive com)   ; no-self-com
  ))

;; ==== litmus templates: Unknown ====
(assert (not (rel.cyclic po)))
(assert (irreflexive (rel.join (rel.tclosure po-loc) rf)))
(assert (irreflexive (rel.join (rel.join (rel.join (rel.tclosure po-loc) rf) (rel.tclosure po-loc)) rf)))

;; ---- core count = 2 thread(s) ----
(declare-fun th0 () (Tuple Thread))
(declare-fun th1 () (Tuple Thread))
(assert (distinct th0 th1))
(assert (= Thread_set (set.insert th1 (set.singleton th0))))

;; look for an execution the model forbids
(assert (not mcm))

(check-sat)
