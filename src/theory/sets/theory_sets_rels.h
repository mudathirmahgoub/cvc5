/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Extension to Sets theory.
 */

#ifndef SRC_THEORY_SETS_THEORY_SETS_RELS_H_
#define SRC_THEORY_SETS_THEORY_SETS_RELS_H_

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "smt/env_obj.h"
#include "theory/decision_strategy.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/rels_utils.h"
#include "theory/sets/solver_state.h"
#include "theory/sets/term_registry.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {

class Valuation;

namespace sets {

class TheorySetsPrivate;

/**
 * A prefix tree for tuples and their elements' representatives.
 * Suppose we have a tuple representative t = <e1, ..., en>,
 * then the tuple tree would be
 * e1 -> e2 -> ... -> e_n -> t
 */
class TupleTrie
{
 public:
  /** the data */
  std::map<Node, TupleTrie> d_data;

 public:
  std::vector<Node> findTerms(std::vector<Node>& reps, int argIndex = 0);
  std::vector<Node> findSuccessors(std::vector<Node>& reps, int argIndex = 0);
  Node existsTerm(std::vector<Node>& reps, int argIndex = 0);
  bool addTerm(Node n, std::vector<Node>& reps, int argIndex = 0);
  void debugPrint(const char* c, Node n, unsigned depth = 0);
  void clear() { d_data.clear(); }
}; /* class TupleTrie */

/**
 * Hash function for vector of nodes, used for the context-dependent map
 * d_cycle_sequences, which maps a relation list to its sequence representation
 * and count.
 */
struct VectorNodeHashFunction
{
  size_t operator()(const std::vector<Node>& v) const
  {
    size_t h = 0;
    for (const Node& n : v) h = h * 31 + std::hash<Node>()(n);
    return h;
  }
};

/** The relations extension of the theory of sets
 *
 * This class implements inference schemes described in Meng et al. CADE 2017
 * for handling quantifier-free constraints in the theory of relations.
 *
 * In cvc5, relations are represented as sets of tuples. The theory of
 * relations includes constraints over operators, e.g. RELATION_TRANSPOSE,
 * RELATION_JOIN and so on, which apply to sets of tuples.
 *
 * Since relations are a special case of sets, this class is implemented as an
 * extension of the theory of sets. That is, it shares many components of the
 * TheorySets object which owns it.
 */
class TheorySetsRels : protected EnvObj
{
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashSet<Node> NodeSet;
  typedef context::CDHashMap<Node, Node> NodeMap;

 public:
  TheorySetsRels(Env& env,
                 SolverState& s,
                 InferenceManager& im,
                 SkolemCache& skc,
                 TermRegistry& treg);

  ~TheorySetsRels();
  /**
   * Invoke the check method for the basic relational-operator rules. At a
   * high level, this class will make calls to
   * TheorySetsPrivate::processInference to assert facts, lemmas, and
   * conflicts. If this class makes no such call, then the current set of
   * assertions is satisfiable with respect to relations.
   */
  void check(Theory::Effort e);
  /**
   * Unroll the cycle witness of every asserted (rel.cyclic R) by one element
   * and split on its length (doCycleInference). The witnesses are created by
   * applyInstCycleRule, from collectRelsInfo, which check(Theory::Effort) ran
   * earlier in the same check.
   */
  void checkAcyclicity();
  /**
   * Seed the closure graph of every TC term with the members of its base
   * relation, then apply the transitive-closure DOWN rule for each asserted TC
   * membership. The down rule introduces fresh skolem elements (see
   * applyTCRule) and may do so unboundedly, so the caller should invoke this at
   * most once per postCheck.
   *
   * Both operations add edges to the closure graph (d_tcr_tcGraph) that
   * checkTransitiveClosureUp consumes. Requires the caches collected by
   * check(Theory::Effort) earlier in the same check.
   */
  void checkTransitiveClosureDown();
  /**
   * Apply the transitive-closure UP rule: chain the edges of the graph left by
   * checkTransitiveClosureDown (doTCInference), which must have run earlier in
   * the same check.
   */
  void checkTransitiveClosureUp();
  /**
   * Last call: complete every cycle witness to its length in the candidate
   * model, and send the branching anchor lemma for it. Example: for a witness
   * s1, s2 whose length l is 4 in the model, add s3 and s4 (with s4 = s1)
   * and the rules for them. If l has no practical value in the model (not a
   * constant, or more than 10000), the model is marked unsound.
   */
  void checkAcyclicityLastCall(Valuation& val);
  /** Whether a cycle witness exists, which requires the last-call check. */
  bool hasOpenCycleObligation() const;
  /**
   * Last call, with --rels-acyclic-hammer or --rels-tc-down-lazy (neither
   * splits closure memberships at full effort). For every (a, b) in TC(R) that
   * the known members of R do not explain, e.g. (a, c) in TC(R) with
   * R = {(a, b)}, send the TCLOSURE_DOWN split in the lazy mode and the
   * grounding conflict (applyTCGroundingConflict) otherwise. If cardinality
   * constraints are present (cardinalityUsed), the cardinality solver may
   * still add members to R, so the model is marked unsound instead.
   */
  void checkTransitiveClosureLastCall(bool cardinalityUsed);
  /**
   * Last call, with --rels-acyclic-hammer (which does not split join
   * memberships at full effort). For every (x, z) in (rel.join A B) that the
   * known members of A and B do not explain, e.g. (a, c) in A;B with
   * A = {(a, b)} and B = {(d, c)}, send the grounding conflict
   * (applyJoinGroundingConflict), or mark the model unsound if cardinality
   * constraints are present (cardinalityUsed).
   */
  void checkJoinLastCall(bool cardinalityUsed);
  /** PROTOTYPE: compose the members of every product (--rels-product-lazy) */
  void checkProductLastCall();
  /** Is kind k a kind that belongs to the relation theory? */
  static bool isRelationKind(Kind k);

 private:
  /** True and false constant nodes */
  Node d_trueNode;
  Node d_falseNode;

  /** Reference to the state object for the theory of sets */
  SolverState& d_state;
  /** Reference to the inference manager for the theory of sets */
  InferenceManager& d_im;
  /** Reference to the skolem cache */
  SkolemCache& d_skCache;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  NodeSet d_shared_terms;

  std::unordered_set<Node> d_rel_nodes;
  /** a map from tuples to their elements' representatives*/
  std::map<Node, std::vector<Node> > d_tuple_reps;
  /** a map from relation terms to their member tuples*/
  std::map<Node, TupleTrie> d_membership_trie;

  /** Symbolic tuple variables that has been reduced to concrete ones */
  std::unordered_set<Node> d_symbolic_tuples;

  /** Mapping between relation and its member representatives */
  std::map<Node, std::vector<Node> > d_rReps_memberReps_cache;

  /** Mapping between relation and its member representatives explanation */
  std::map<Node, std::vector<Node> > d_rReps_memberReps_exp_cache;

  /** Mapping between a relation representative and its equivalent relations
   * involving relational operators */
  std::map<Node, std::map<Kind, std::vector<Node> > > d_terms_cache;

  /**
   * Maps the representative of a relation to the asserted literals
   * (not (rel.cyclic S)) with S in its class, e.g. po -> [(not (rel.cyclic
   * po))]. Used by the acyclic-down rule and as the S of the anchor rules.
   */
  std::map<Node, std::vector<Node> > d_acyclic_cache;
  /**
   * (R, S) for which the inclusion anchor lemma was sent, R the union of the
   * operands of a witness and S an acyclic relation.
   */
  std::set<std::pair<Node, Node> > d_anchorInclusionSent;
  /**
   * ((R, S), length) for which the branching anchor lemma was sent; the
   * length is part of the key since the length of the witness in the
   * candidate model may change between last-call checks.
   */
  std::set<std::pair<std::pair<Node, Node>, size_t> > d_anchorBranchSent;

  /**
   * Maps the operands [R1, ..., Rk] of an asserted (rel.cyclic (R1 U ... U
   * Rk)), k >= 2, to its cycle witness: the elements unrolled so far
   * [s1, ..., s_cnt] and the length l, with s_l = s1. Example:
   * [rf, po] -> ([s1, s2, s3], l) for the cycle s1 -rf+-> s2 -po+-> s3 ...
   * Context-dependent, so that elements unrolled in a branch are forgotten on
   * backtracking.
   */
  context::CDHashMap<std::vector<Node>,
                     std::pair<std::vector<Node>, Node>,
                     VectorNodeHashFunction>
      d_cycle_sequences;
  /**
   * PROTOTYPE (--rels-cycle-keep-prefix): the longest witness prefix unrolled
   * so far for each operand list. User-context dependent, like the lemma
   * cache: the lemmas of the prefix stay sent until the user context is
   * popped.
   */
  context::
      CDHashMap<std::vector<Node>, std::vector<Node>, VectorNodeHashFunction>
          d_cyclePrefixes;

  /**
   * Maps the representative of a relation to the asserted atoms
   * (rel.is-functional R) with R in its class, e.g. po -> [(rel.is-functional
   * po)].
   */
  std::map<Node, std::vector<Node> > d_functional_cache;
  /** (rel.is-functional R) atoms asserted false for which we sent a witness */
  std::unordered_set<Node> d_notFunctionalSent;

  /**
   * Transitive closure (TC) graphs.
   *
   * For a term (rel.tclosure r), we maintain a "TC graph": an adjacency-list
   * representation of the known members of a binary relation, i.e. a map
   * from element representative a to the set of element representatives b
   * such that the pair (a, b) is currently asserted to be a member. These
   * graphs are built during a full-effort check (see buildTCGraphForRel) and
   * cleared at the start of the next one; they are caches for a single
   * full-effort check, not context-dependent data structures. Edges are only
   * ever added to a graph, never removed; see addTCEdge for the one case in
   * which an edge's explanation is replaced.
   */
  /**
   * Mapping between the representative of a base relation r (the argument of a
   * rel.tclosure term) and the TC graph induced by the asserted members of r
   * only. Used by isTCReachable to recognize memberships of TC(r) that are
   * already derivable from the members of r, in which case applyTCRule
   * skips sending a redundant lemma.
   */
  std::map<Node, std::map<Node, std::unordered_set<Node> > > d_rRep_tcGraph;
  /**
   * Mapping between a transitive closure term TC(r) = (rel.tclosure r) and its
   * TC graph. Seeded by buildTCGraphForRel with the asserted members of r, and
   * extended by applyTCRule with pairs that are asserted to be members of TC(r)
   * directly. Both go through addTCEdge, so the two sets of edges accumulate.
   * Once per full-effort check, doTCInference() closes each of these graphs
   * transitively and infers the implied memberships.
   */
  std::map<Node, std::map<Node, std::unordered_set<Node> > > d_tcr_tcGraph;
  /**
   * Maps a transitive closure term TC(r) to the explanations of the edges in
   * its TC graph. Each edge (a, b) is keyed by the pair tuple
   * RelsUtils::constructPair(TC(r), a, b) built from the endpoint
   * representatives, and maps to the membership assertion that justifies the
   * edge. doTCInference conjoins these explanations along a path to form the
   * reason for each inferred membership.
   */
  std::map<Node, std::map<Node, Node> > d_tcr_tcGraph_exps;

 private:
  /** Send infer
   *
   * Called when we have inferred fact from explanation reason, where the
   * latter should be a conjunction of facts that hold in the current context.
   *
   * This method adds the node (=> reason exp) to the pending vector d_pending.
   */
  void sendInfer(Node fact, InferenceId id, Node reason);
  /**
   * This method flushes the inferences in the pending vector d_pending to
   * theory of sets, which may process them as lemmas or as facts to assert to
   * the equality engine.
   */
  void doPendingInfers();
  /** Process inference
   *
   * A wrapper around d_im.assertInference that ensures that we do not send
   * inferences with explanations that are not entailed.
   */
  void processInference(Node conc, InferenceId id, Node exp);

  /** Methods used in full effort */
  void check();
  /**
   * Clear the per-check caches populated by collectRelsInfo. Called once per
   * full-effort check, from check(Theory::Effort), immediately before
   * collectRelsInfo; the caches stay live for the transitive-closure steps that
   * run later in the same check.
   */
  void clearCaches();
  void collectRelsInfo();
  void applyTransposeRule(std::vector<Node> tp_terms);
  void applyTransposeRule(Node rel, Node rel_rep, Node exp);
  /**
   * Minimality of the witness s = [s1, ..., s_cnt] of length l: its elements
   * are distinct except s1 = s_l, and it has no chord. Example: for the
   * witness s1 -> s2 -> s3 -> s4 = s1 of R1 U R2, (s1, s3) is in neither
   * TC(R1) nor TC(R2). With --rels-acyclic-backward-chords, backward edges
   * that close a shorter cycle are excluded too, e.g. (s3, s2) when l >= 4.
   * exp is the (rel.cyclic R) atom.
   */
  void applyContrMinimalRule(const std::vector<Node>& rels,
                             const std::vector<Node>& s,
                             Node l,
                             Node exp);
  /**
   * Acyclic-down rule: (a, b) in TC(R) /\ (not (rel.cyclic R)) => a != b.
   * mem is the representative of the tuple, rel the closure term TC(R) and
   * exp the membership literal.
   */
  void applyAcyclicDownRule(Node mem, Node rel, Node exp);
  /**
   * Create the cycle witness of an asserted (rel.cyclic R):
   * - R not a union: (s, s) in TC(R) for a fresh s, e.g. (rel.cyclic po)
   *   gives (s, s) in TC(po);
   * - R = R1 U ... U Rk: a fresh s1 and length l with 1 < l, unrolled by
   *   doCycleInference, e.g. (rel.cyclic (rf U po)) gives the cycle
   *   s1 -> s2 -> ... -> s_l = s1 whose edges are in TC(rf) or TC(po).
   * If an atom with the same operands, nested differently, already has the
   * witness (A U (B U C) and (A U B) U C), this atom implies that atom.
   */
  void applyInstCycleRule(Node atom);
  /** The atom (rel.cyclic R) whose witness has the operands rels. */
  Node cyclicAtom(const std::vector<Node>& rels) const;
  /** Build the (rewritten) union of the given relations. */
  Node mkRelUnion(const std::vector<Node>& rels);
  /**
   * Split on whether the witness closes at its last element s_cnt:
   *   (rel.cyclic R) /\ cnt <= l => cnt < l \/ (l = cnt /\ s_cnt = s1)
   */
  void applySplitCycleLenRule(const std::vector<Node>& rels,
                              const std::vector<Node>& s,
                              Node l);
  /**
   * Add the element s_{cnt+1} to the witness of (rel.cyclic (R1 U ... U Rk)):
   *   (rel.cyclic R) /\ cnt < l =>
   *     (s_cnt, s_{cnt+1}) in TC(R1) \/ ... \/ (s_cnt, s_{cnt+1}) in TC(Rk)
   * and two consecutive edges are not in the same TC(Ri) (they would compose
   * into one, giving a shorter cycle). Returns the extended witness.
   */
  std::vector<Node> applyUnrollCycle(const std::vector<Node>& rels,
                                     const std::vector<Node>& s,
                                     Node l);
  void applyProductRule(Node rel, Node rel_rep, Node exp);
  void applyJoinRule(Node rel, Node rel_rep, Node exp);
  /**
   * @param n is a ((_ table.join m1 n1 ... mk nk) A B) where A, B are tables
   * @param nRep a representative of n
   * @param exp a membership constraint of the form (set.member e n)
   *        where e is an element of the form (tuple a1 ... am b1 ... bn)
   * This function sends a fact that represents the following
   * (=>
   *   (set.member e n)
   *   (and
   *     (= a_{m1} b_{n1}) ... (= a_{mk} b_{nk})
   *     (set.member (tuple a1 ... am) A)
   *     (set.member (tuple b1 ... bn) B)))
   */
  void applyTableJoinRule(Node n, Node nRep, Node exp);
  void applyJoinImageRule(Node mem_rep, Node rel_rep, Node exp);
  void applyIdenRule(Node mem_rep, Node rel_rep, Node exp);
  /**
   * Rules for the asserted (rel.is-functional R), applied to the asserted
   * members of the relations in the class of R (--rels-functional-mode):
   *   uf (default):  (x, y) in R => y = f_R(x)   for a fresh function f_R
   *   pairs:         (x1, y1) in R /\ (x2, y2) in R => (x1 = x2 => y1 = y2)
   * Example: with (a, b) and (a, c) in R, uf gives b = f_R(a) and
   * c = f_R(a), hence b = c. uf is linear in the number of members, pairs
   * quadratic; pairs is used when the logic has no uninterpreted functions.
   */
  void applyFunctionalRules();
  /**
   * (not (rel.is-functional R)) => (k1, k2) in R /\ (k1, k3) in R /\ k2 != k3
   * for fresh k1, k2, k3, sent once per atom.
   */
  void applyNotFunctionalRule(Node atom);
  /**
   * Process a membership in a transitive closure term.
   *
   * @param mem a tuple (a, b) asserted to be a member of rel_rep
   * @param rel a term TC(r) = (rel.tclosure r) occurring in the equivalence
   *        class of rel_rep
   * @param rel_rep the representative of rel
   * @param exp the explanation of the membership, of the form
   *        (set.member mem s) where s is equal to rel
   *
   * If the membership is already derivable from the members of r (see
   * isTCReachable), this method does nothing. Otherwise it records the edge
   * (a, b) and its explanation in d_tcr_tcGraph / d_tcr_tcGraph_exps, and
   * sends the lemma that unfolds the closure one step
   * (InferenceId::SETS_RELS_TCLOSURE_DOWN):
   *   (set.member (a, b) TC(r)) =>
   *     (set.member (a, b) r)
   *     or ((set.member (a, z1) r) and (set.member (z2, b) r)
   *         and (z1 = z2 or (set.member (z1, z2) TC(r))))
   * where z1, z2 are skolems for the intermediate nodes on the path
   * from a to b.
   */
  void applyTCRule(Node mem, Node rel, Node rel_rep, Node exp);
  /**
   * The TCLOSURE_DOWN split of applyTCRule for the membership exp of (a, b) in
   * tc_rel = TC(R), also sent at last call with --rels-tc-down-lazy.
   */
  void sendTCDownSplit(Node tc_rel, Node exp);
  /**
   * Closure induction (--rels-tc-subset): TC(R) is the least transitive
   * relation containing R, so (a, b) in TC(R), R subset S and S transitive
   * give (a, b) in S. For the membership exp of (a, b) in tc_rel = TC(R),
   * the lemma (a, b) in S is sent for every such S in the current context:
   *  1. S = TC(X) with R syntactically included in TC(X),
   *     e.g. R = TC(po) ∩ loc and S = TC(po);
   *  2. S with R subset S asserted (as (set.union R S) = S) and S transitive
   *     (isTransitiveClass), e.g. R subset (rel.product A B): (a, b) in A x B;
   *  3. S = R if R is transitive, e.g. (rel.join R R) subset R asserted;
   *  4. S = R if R = A x B or R subset A x B with A ∩ B = empty: no two edges
   *     of R compose, so TC(R) = R, e.g. fr from reads to writes;
   *  5. S = X for R = X ∩ Y or R = X \ Y with X transitive.
   * No fresh element is introduced, so where it applies this replaces an
   * unbounded sequence of TCLOSURE_DOWN splits.
   */
  void applyTCSubsetRules(Node tc_rel, Node exp);
  /**
   * Whether the class of p (representative pRep) is known to be transitive:
   * it contains a product A x B, a closure or an identity; or a join J;J^T
   * with (rel.is-functional J) asserted (J;J^T;J;J^T is a subset of J;J^T,
   * since J^T;J relates only equal elements); or (rel.join p p) subset p is
   * asserted. The literals that justify this are appended to reason.
   */
  bool isTransitiveClass(Node pRep, Node p, std::vector<Node>& reason);
  /** Whether applyTCRule is called from the last-call check (lazy split). */
  bool d_tcLastCall = false;
  /**
   * Self-loop witnesses: for an asserted (rel.cyclic R), R not a union, maps
   * [R] to the fresh s with (s, s) in TC(R).
   */
  std::map<std::vector<Node>, Node> d_selfLoops;
  /**
   * Maps the operands of the relation of an asserted (rel.cyclic R) to the
   * atom, e.g.
   *   [rf, po, co] -> (rel.cyclic (set.union rf (set.union po co)))
   *   [po]         -> (rel.cyclic po)
   * The atom is the reason of every lemma about the witness of these
   * operands. An atom whose relation has the same operands, nested
   * differently, is reduced to the first one (applyInstCycleRule).
   */
  std::map<std::vector<Node>, Node> d_cycleAtoms;
  /** PROTOTYPE: the decision strategies on the witness lengths */
  std::vector<std::unique_ptr<DecisionStrategy> > d_cycleLenStrategies;
  /** PROTOTYPE: the pairs (X;Y, X) whose subset atom was registered */
  std::set<std::pair<Node, Node> > d_subsetSplitSent;
  /**
   * Grounding conflict for a membership (a, b) in TC(R), stated by exp, that
   * the known members m1, ..., mn of R do not explain:
   *   (a, b) in TC(R) /\ R = {m1, ..., mn} /\ distinct(a, b, elements of mi)
   *     => false
   * e.g. (a, c) in TC(R) /\ R = {(a, b)} /\ distinct(a, b, c) => false.
   * The disequalities keep the lemma valid in branches where elements are
   * merged later (with b = c above, the membership holds). The premise
   * also contains the equalities of the elements to their representatives.
   * Introduces no fresh element.
   */
  void applyTCGroundingConflict(Node mem_rep, Node tc_rel, Node exp);
  /**
   * Grounding conflict for a membership (x, z) in (rel.join A B), stated by
   * exp, that the known members of A and B do not explain:
   *   (x, z) in A;B /\ A = {known} /\ B = {known} /\ distinct(elements)
   *     => false
   * e.g. (a, c) in A;B /\ A = {(a, b)} /\ B = {(d, c)}
   *      /\ distinct(a, b, c, d) => false
   * (with b = d the membership holds).
   * Introduces no fresh element.
   */
  void applyJoinGroundingConflict(Node mem_rep, Node join_rel, Node exp);
  /**
   * Add the edge (fst_rep, snd_rep), justified by exp, to the TC graph of
   * tc_rel. Edges are only added, never removed. If the edge is already
   * present, it keeps the explanation it was first added with, unless
   * overwriteExp is true, in which case its explanation is replaced by exp.
   * applyTCRule passes overwriteExp = true so that doTCInference chains the
   * asserted TC membership rather than the (withdrawable) base-relation
   * membership that seeded the same edge. This is the only way d_tcr_tcGraph
   * and d_tcr_tcGraph_exps are written.
   */
  void addTCEdge(Node tc_rel,
                 Node fst_rep,
                 Node snd_rep,
                 Node exp,
                 bool overwriteExp = false);
  /**
   * Seed the TC graph of tc_rel = (rel.tclosure r) with the currently asserted
   * members of r, with all nodes and edges expressed in terms of
   * representatives. The edges are added to d_tcr_tcGraph / d_tcr_tcGraph_exps
   * (keyed by tc_rel) via addTCEdge and to d_rRep_tcGraph (keyed by r's
   * representative); nothing is overwritten, so this can be called at any point
   * of a check without discarding the edges applyTCRule contributed. It is
   * called once per TC term per check, via ensureTCGraphBuilt.
   */
  void buildTCGraphForRel(Node tc_rel);
  /**
   * Ensure buildTCGraphForRel has been called for tc_rel in the current check
   * (tracked via d_rel_nodes, which clearCaches resets).
   */
  void ensureTCGraphBuilt(Node tc_rel);
  /**
   * Unroll every witness in d_cycle_sequences by one element and apply the
   * length split, minimality and anchor rules to it; re-apply the anchor
   * rules to the self-loop witnesses (acyclicity constraints may have been
   * asserted since).
   */
  void doCycleInference();
  /** PROTOTYPE: continue a witness from its longest prefix (keep-prefix) */
  void restoreCyclePrefix(const std::vector<Node>& rels,
                          std::vector<Node>& s,
                          Node l);
  /**
   * Anchor rules: a cycle of R whose edges all lie in TC(S) would be a cycle
   * of S, so for the witness s of an asserted (rel.cyclic R) (acyc_exp) and
   * every asserted (not (rel.cyclic S)), some edge of R is outside TC(S):
   *   inclusion:  t in R /\ t not in TC(S)  for a fresh pair t;
   *   branch:     l = N => (s1, s2) not in TC(S) \/ ... \/ (s_{N-1}, s_N)
   *               not in TC(S)
   * The fresh edge is restricted to the operands of R that are not
   * syntactically in TC(S): for (rel.cyclic (rf U po)) and
   * (not (rel.cyclic po)), inclusion gives t in rf /\ t not in TC(po). If
   * every operand is in TC(S), e.g. (rel.cyclic (set.inter po loc)) and
   * (not (rel.cyclic po)), the constraints conflict directly.
   * --rels-acyclic-anchor selects the rules.
   *
   * The branch lemma needs every edge of the witness, so it is only sent when
   * concreteLen >= 2 is given: the length N of the witness in the candidate
   * model (s may be longer; its first N elements are used), with lenEq the
   * literal l = N. Full-effort callers pass concreteLen = -1.
   */
  void applyAcyclicAnchorRules(const std::vector<Node>& rels,
                               const std::vector<Node>& s,
                               Node acyc_exp,
                               int64_t concreteLen = -1,
                               Node lenEq = Node::null());
  /**
   * Append the operands of the nested unions of r to parts, e.g.
   * A U (B U C) gives [A, B, C]; r itself if it is not a union.
   */
  void collectUnionOperands(Node r, std::vector<Node>& parts);
  /**
   * Whether x is a subset of TC(s) in every interpretation, by its shape:
   * e.g. s, TC(s), s ∩ Y, s \ Y, s;s and s;(rel.iden A) are.
   */
  bool isSyntacticallyInTC(Node x, Node s);
  /**
   * Called at the end of a full-effort check. For each transitive closure
   * term TC(r) with a graph in d_tcr_tcGraph, computes the transitive
   * closure of that graph and infers all implied memberships
   * (InferenceId::SETS_RELS_TCLOSURE_UP) via the overload below.
   */
  void doTCInference();
  /**
   * Infer all memberships implied by the TC graph rel_tc_graph of the
   * transitive closure term tc_rel: for each edge, start a depth-first
   * traversal (the recursive overload below) that derives a membership in
   * tc_rel for every node reachable from the edge's source.
   * rel_tc_graph_exps maps each edge of the graph to its explanation, as in
   * d_tcr_tcGraph_exps.
   */
  void doTCInference(std::map<Node, std::unordered_set<Node> > rel_tc_graph,
                     std::map<Node, Node> rel_tc_graph_exps,
                     Node tc_rel);
  /**
   * Recursive step of the traversal above, having reached cur_node_rep from
   * start_node_rep. reasons holds the explanations of the edges along the
   * current path; this method sends the inference that the pair (start of
   * path, end of path) is a member of tc_rel, whose reason is the
   * conjunction of reasons together with the equalities connecting adjacent
   * path edges and connecting each explanation's relation term to tc_rel's
   * base relation. It then recurses into the successors of cur_node_rep that
   * are not in seen, the set of already-traversed nodes used to terminate on
   * cycles.
   */
  void doTCInference(Node tc_rel,
                     std::vector<Node> reasons,
                     std::map<Node, std::unordered_set<Node> >& tc_graph,
                     std::map<Node, Node>& rel_tc_graph_exps,
                     Node start_node_rep,
                     Node cur_node_rep,
                     std::unordered_set<Node>& seen);

  void composeMembersForRels(Node);
  /**
   * @param n is ((_ rel.join m1 n1 ... mk nk) A B) where A, B are relations
   * This functions looks for current members of A, B.
   * For each pair e1 = (tuple a1 ... am) in A, e2 = (tuple b1 ... bn) in B
   * this function sends the following fact
   *  (=>
   *    (and
   *      (set.member e1 A)
   *      (set.member e2 B)
   *      (= a_{m1} b_{n1}) ... (= a_{mk} b_{nk}))
   *    (set.member (tuple a1 ... am b1 ... bn) n))
   */
  void applyTableJoinUp(Node);
  void computeMembersForBinOpRel(Node);
  void computeMembersForIdenTerm(Node);
  void computeMembersForUnaryOpRel(Node);
  void computeMembersForJoinImageTerm(Node);

  /**
   * Is the membership of pair mem_rep in tc_rel = (rel.tclosure r) already
   * derivable from the asserted members of r? Returns true if mem_rep is a
   * known member of r's representative, or if the second element of mem_rep
   * is reachable from its first element in the TC graph stored in
   * d_rRep_tcGraph for r. Used by applyTCRule to avoid sending redundant
   * lemmas.
   */
  bool isTCReachable(Node mem_rep, Node tc_rel);
  /**
   * Recursive helper for the above: depth-first search in tc_graph, setting
   * isReachable to true if dest can be reached from start. hasSeen is the
   * set of already-visited nodes, used to terminate on cycles.
   */
  void isTCReachable(Node start,
                     Node dest,
                     std::unordered_set<Node>& hasSeen,
                     std::map<Node, std::unordered_set<Node> >& tc_graph,
                     bool& isReachable);
  /**
   * True if mem_rep is justified by currently-known members of join_rel[0] and
   * join_rel[1].
   */
  bool isJoinReachable(Node mem_rep, Node join_rel);

  /** Helper functions */
  bool hasTerm(Node a);
  void makeSharedTerm(Node a);
  void reduceTupleVar(Node);
  bool hasMember(Node, Node);
  void computeTupleReps(Node);
  bool areEqual(Node a, Node b);
  Node getRepresentative(Node t);
  inline void addToMembershipDB(Node, Node, Node);
  inline Node constructPair(Node tc_rep, Node a, Node b);
  bool safelyAddToMap(std::map<Node, std::vector<Node> >&, Node, Node);
  bool isRel(Node n)
  {
    return n.getType().isSet() && n.getType().getSetElementType().isTuple();
  }
};

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* SRC_THEORY_SETS_THEORY_SETS_RELS_H_ */
