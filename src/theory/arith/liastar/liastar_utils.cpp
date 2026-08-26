/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for the lia* (LIA star) arithmetic extension.
 *
 * This file is a toolbox of stateless helpers used by `LiaStarExtension`. It
 * has three responsibilities:
 *
 * 1. Predicate normalization. A STAR_CONTAINS literal carries a lambda whose
 *    body `p` is an arbitrary QF_LIA predicate. Before it can be handed to
 *    Normaliz it must be turned into a disjunction of conjunctions of linear
 *    (in)equalities, with no if-then-elses, no negations, and no
 *    disequalities. The pipeline is:
 *      removeItes      : push integer/boolean if-then-elses into the boolean
 *                        structure (case split, no new variables);
 *      removeNot       : push negations to the leaves (NNF) and rewrite each
 *                        negated comparison into a positive one, turning a
 *                        disequality `(not (= a b))` into `(or (> a b) (< a b))`;
 *      distribute      : distribute AND over OR to reach DNF, optionally pruning
 *                        unsatisfiable conjuncts with a subsolver.
 *    `removeItesAndNots` runs the first two; `toDNF` runs all three.
 *
 * 2. Translation to Normaliz input. `getMatrix`/`getMatrices` render a
 *    conjunction (one cone) / a DNF (a list of cones) into Normaliz "symbolic"
 *    constraint strings such as "x[1] + 2 x[2] >= 3;", and `buildCone` feeds
 *    those strings to libnormaliz and computes the cone's Hilbert basis and
 *    module generators. `getGeneratorBody` then turns one module generator into
 *    its arithmetic encoding (shared by the membership and the star encodings).
 *
 * 3. Subsolver model extraction. In the lazy strategy a satisfying model of the
 *    predicate is read back from an incremental subsolver and `getDisjunct`
 *    distils it into a single convex cell (one conjunction of atoms) that
 *    becomes the next cone to add.
 *
 * See `liastar_extension.cpp` for the overall decision procedure.
 */

#ifdef CVC5_USE_NORMALIZ

#include "liastar_utils.h"

#include "expr/algorithm/flatten.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "libnormaliz/input.h"
#include "libnormaliz/libnormaliz.h"
#include "options/arith_options.h"
#include "smt/solver_engine.h"
#include "theory/arith/linear/normal_form.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/uf/function_const.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

using namespace libnormaliz;

using libnormaliz::operator<<;

void LiaStarUtils::traceDistinctQuery(const std::string& label, Node a, Node b)
{
  // `!TraceIsOn(...)` does not compile in non-tracing builds, so guard
  // positively.
  if (TraceIsOn("liastar-ext-smt"))
  {
    Trace("liastar-ext-smt") << "(push 1)" << std::endl;
    Trace("liastar-ext-smt") << "(echo \"" << label << "\")" << std::endl;
    Trace("liastar-ext-smt") << "(assert " << std::endl
                             << "  (distinct" << std::endl
                             << "    ";
    Trace("liastar-ext-smt") << a << std::endl << "    ";
    Trace("liastar-ext-smt") << b << std::endl
                             << "  )" << std::endl
                             << ")" << std::endl;
    Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
    Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
  }
}

std::pair<Node, Node> LiaStarUtils::getVectorPredicate(Node n, NodeManager* nm)
{
  // `n` is (int.star-contains (lambda ((x_1 Int) ... (x_n Int)) p) y_1 ... y_n).
  // The "vector predicate" is `p` with each bound variable x_i replaced by the
  // corresponding vector element y_i, i.e. the statement that the vector itself
  // satisfies `p` (and hence is a single-summand member of the star set). We
  // also return the non-negativity constraints on the vector, which are a
  // necessary condition for membership in the star set (the set lives in the
  // non-negative orthant).
  Assert(n.getKind() == Kind::STAR_CONTAINS);
  // The predicate argument is normally a LAMBDA, but two rewrites can hide it:
  // a *constant* lambda (e.g. `lambda x. x = 31`, the function true at a
  // single point) is turned by the UF rewriter into a FUNCTION_ARRAY_CONST
  // with no children, and STAR_CONTAINS is not a closure kind, so lambda
  // lifting may purify the argument into a skolem. Undo both before indexing
  // into it.
  Node lambda =
      uf::FunctionConst::toLambda(SkolemManager::getOriginalForm(n[0]));
  std::vector<Node> vars(lambda[0].begin(), lambda[0].end());
  std::vector<Node> vecElements(n.begin() + 1, n.end());

  Node substitute = lambda[1].substitute(
      vars.begin(), vars.end(), vecElements.begin(), vecElements.end());

  Trace("liastar-ext-debug") << "n: " << n << std::endl;
  Trace("liastar-ext-debug") << "predicate : " << lambda[1] << std::endl;
  Node nonnegativeConstraints = nm->mkConst<bool>(true);
  for (const auto& v : vecElements)
  {
    Node nonnegative = nm->mkNode(Kind::GEQ, v, nm->mkConstInt(Rational(0)));
    nonnegativeConstraints = nonnegativeConstraints.andNode(nonnegative);
  }
  Trace("liastar-ext-debug") << "substitute: " << substitute << std::endl;
  return std::make_pair(substitute, nonnegativeConstraints);
}

Node LiaStarUtils::removeItesAndNots(Node n, Env* e)
{
  // Eliminate if-then-elses, then push negations to the leaves (and rewrite
  // negated comparisons into positive ones). The result is a negation-free,
  // ite-free formula over positive linear (in)equalities.
  Node noItes = removeItes(n, e);
  Trace("liastar-ext-debug") << "noItes: " << noItes << std::endl;
  Node nnf = removeNot(noItes, e);
  Trace("liastar-ext-debug") << "nnf: " << nnf << std::endl;
  // emit queries validating both transformations on the liastar-ext-smt trace
  traceDistinctQuery("noItes", n, noItes);
  traceDistinctQuery("nnf", noItes, nnf);
  return nnf;
}

Node LiaStarUtils::toDNF(Node n, Env* e)
{
  // Normalize (no ites/negations) and then distribute AND over OR to reach
  // disjunctive normal form. `recursiveFlatten` collapses nested AND/OR so each
  // disjunct is a flat conjunction (a single cone).
  Node nnf = removeItesAndNots(n, e);
  Node dnf = distribute(nnf, e);
  Trace("liastar-ext-debug") << "dnf: " << dnf << std::endl;
  dnf = recursiveFlatten(e->getNodeManager(), dnf);
  // emit a query validating the distribution on the liastar-ext-smt trace
  traceDistinctQuery("dnf", nnf, dnf);
  return dnf;
}

Node LiaStarUtils::recursiveFlatten(NodeManager* nm, Node n)
{
  // Collapse nested associative operators, e.g. (or a (or b c)) -> (or a b c)
  // and likewise for the conjuncts one level down, so a DNF is exactly two
  // levels deep: a flat OR of flat ANDs.
  Trace("liastar-ext-dnf") << "recursiveFlatten::n: " << n << std::endl;
  if (n.getNumChildren() == 0)
  {
    return n;
  }
  Node flat = expr::algorithm::flatten(nm, n);
  std::vector<Node> children;
  for (const auto& child : flat)
  {
    children.push_back(expr::algorithm::flatten(nm, child));
  }
  return nm->mkNode(flat.getKind(), children);
}

Node LiaStarUtils::distribute(Node n, Env* e)
{
  // Recursively rewrite `n` into DNF by distributing AND over OR. Atoms and
  // boolean constants are returned unchanged; an OR distributes into its
  // children; an AND computes the cartesian product of its children's
  // disjuncts. Conjuncts found to be unsatisfiable (via `areAssertionsUnsat`)
  // are dropped, which keeps the number of cones down by avoiding empty ones.
  Assert(n.getType().isBoolean())
      << "Expected " << n << " to be boolean" << std::endl;
  Trace("liastar-ext-dnf") << "distribute::n: " << n << std::endl;
  NodeManager* nm = e->getNodeManager();
  Node falseConst = nm->mkConst<bool>(false);
  Node trueConst = nm->mkConst<bool>(true);

  Kind k = n.getKind();
  switch (k)
  {
    case Kind::VARIABLE:
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_BOOLEAN:
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL:
    {
      // already a literal
      return n;
    }
    case Kind::AND:
    {
      // First put each conjunct into DNF.
      std::vector<Node> conjunctions;
      for (Node child : n)
      {
        Node childDnf = distribute(child, e);
        childDnf = expr::algorithm::flatten(nm, childDnf);
        conjunctions.push_back(childDnf);
      }

      if (conjunctions.size() == 1)
      {
        return conjunctions[0];
      }
      // Distribute AND over the OR-children by building the cartesian product
      // of their disjuncts. `disjunctions` holds the conjunctions accumulated so
      // far. For example, distributing
      //     (and (or a b) c (or d e))
      // grows the accumulator as:
      //     {}
      //     {a}, {b}              (after the first conjunct (or a b))
      //     {a,c}, {b,c}          (after the conjunct c)
      //     {a,c,d}, {b,c,d}, {a,c,e}, {b,c,e}   (after (or d e))
      // Partial conjunctions found unsatisfiable are pruned eagerly so the
      // product does not blow up with dead branches.
      std::vector<std::vector<Node>> disjunctions;
      disjunctions.push_back({});
      for (const Node& conjunct : conjunctions)
      {
        Kind conjunctKind = conjunct.getKind();
        if (conjunctKind == Kind::OR)
        {
          std::vector<std::vector<Node>> tmp;
          for (const Node& disjunct : conjunct)
          {
            auto copy = disjunctions;
            for (std::vector<Node>& v : copy)
            {
              v.push_back(disjunct);
              Result r = areAssertionsUnsat(v, e);
              if (r.getStatus() == Result::Status::UNSAT)
              {
                // discard unsatisfiable conjunctions
                continue;
              }
              else
              {
                tmp.push_back(v);
              }
            }
          }
          disjunctions = std::move(tmp);
        }
        else
        {
          // a plain conjunct is appended to every accumulated conjunction
          for (size_t i = 0; i < disjunctions.size(); i++)
          {
            disjunctions[i].push_back(conjunct);
          }
        }
      }
      // Reassemble the surviving (satisfiable) conjunctions into a disjunction.
      std::vector<Node> final_disjuncts;
      for (std::vector<Node>& v : disjunctions)
      {
        Result r = areAssertionsUnsat(v, e);
        if (r.getStatus() == Result::Status::UNSAT)
        {
          continue;
        }
        if (v.size() == 1)
        {
          final_disjuncts.push_back(v[0]);
        }
        else
        {
          final_disjuncts.push_back(nm->mkNode(Kind::AND, v));
        }
      }
      if (final_disjuncts.size() == 0)
      {
        return nm->mkConst<bool>(false);
      }
      if (final_disjuncts.size() == 1)
      {
        return final_disjuncts[0];
      }
      return nm->mkNode(Kind::OR, final_disjuncts);
    }
    case Kind::OR:
    {
      // OR is already a disjunction; just put each child into DNF.
      std::vector<Node> disjuncts;
      for (size_t i = 0; i < n.getNumChildren(); i++)
      {
        Node childDnf = distribute(n[i], e);
        childDnf = expr::algorithm::flatten(nm, childDnf);
        disjuncts.push_back(childDnf);
      }
      return nm->mkNode(Kind::OR, disjuncts);
    }

    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

Node LiaStarUtils::removeItes(Node n, Env* e)
{
  // Eliminate if-then-elses without introducing new variables, by case
  // splitting. A boolean ITE becomes a disjunction of its two guarded branches;
  // integer ITEs nested inside a comparison are lifted out by `removeIntegerItes`
  // and the resulting (condition, value) pairs are combined into a disjunction.
  NodeManager* nm = e->getNodeManager();
  Node falseConst = nm->mkConst<bool>(false);
  Node trueConst = nm->mkConst<bool>(true);
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::VARIABLE:
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_BOOLEAN: return n;
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL:
    {
      // Lift integer ITEs out of both sides. Each side becomes a list of
      // (condition, ite-free term) pairs; the comparison holds when some pair
      // from the left and some pair from the right are both selected.
      std::vector<std::pair<Node, Node>> left = removeIntegerItes(n[0], e);
      std::vector<std::pair<Node, Node>> right = removeIntegerItes(n[1], e);
      if (left.size() == 1 && right.size() == 1)
      {
        // no integer ites were present
        return n;
      }

      std::vector<Node> disjunctions;
      for (const auto& l : left)
      {
        for (const auto& r : right)
        {
          Node result = nm->mkNode(k, l.second, r.second);
          Node combined = result;
          if (r.first != trueConst)
          {
            combined = combined.andNode(r.first);
          }
          else if (l.first != trueConst)
          {
            combined = combined.andNode(l.first);
          }
          disjunctions.push_back(combined);
        }
      }
      return nm->mkNode(Kind::OR, disjunctions);
    }
    case Kind::ITE:
    {
      // a boolean ite: (ite c t e) <-> (or (and c t) (and (not c) e))
      Node l = removeItes(n[0].andNode(n[1]), e);
      Node r = removeItes(n[0].notNode().andNode(n[2]), e);
      return l.orNode(r);
    }
    case Kind::AND:
    {
      std::vector<Node> conjuncts;
      for (Node child : n)
      {
        conjuncts.push_back(removeItes(child, e));
      }
      return nm->mkNode(Kind::AND, conjuncts);
    }
    case Kind::OR:
    {
      std::vector<Node> disjuncts;
      for (Node child : n)
      {
        disjuncts.push_back(removeItes(child, e));
      }
      return nm->mkNode(Kind::OR, disjuncts);
    }
    case Kind::NOT:
    {
      return removeItes(n[0], e).notNode();
    }
    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

Node LiaStarUtils::removeNot(Node n, Env* e)
{
  // Convert to negation normal form and then drive every remaining negation
  // into the comparison it negates, so the formula has no NOT nodes and no
  // disequalities (which are not convex and so cannot be a single cone).
  NodeManager* nm = e->getNodeManager();
  Node nnf = booleans::TheoryBoolRewriter::computeNnfNorm(nm, n);
  Kind k = nnf.getKind();
  switch (k)
  {
    case Kind::VARIABLE:
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_BOOLEAN:
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL: return nnf;
    case Kind::AND:
    {
      std::vector<Node> conjuncts;
      for (Node child : nnf)
      {
        conjuncts.push_back(removeNot(child, e));
      }
      return nm->mkNode(Kind::AND, conjuncts);
    }
    case Kind::OR:
    {
      std::vector<Node> disjuncts;
      for (Node child : nnf)
      {
        disjuncts.push_back(removeNot(child, e));
      }
      return nm->mkNode(Kind::OR, disjuncts);
    }
    case Kind::NOT:
    {
      // computeNnfNorm leaves a NOT only directly above an atom; rewrite the
      // negated comparison into the equivalent positive one.
      Kind kind = nnf[0].getKind();
      switch (kind)
      {
        case Kind::LT:
        {
          //(not (< a b)) is rewritten as (>= a b)
          return nm->mkNode(Kind::GEQ, nnf[0][0], nnf[0][1]);
        }
        case Kind::GT:
        {
          //(not (> a b)) is rewritten as (<= a b)
          return nm->mkNode(Kind::LEQ, nnf[0][0], nnf[0][1]);
        }
        case Kind::LEQ:
        {
          //(not (<= a b)) is rewritten as (> a b)
          return nm->mkNode(Kind::GT, nnf[0][0], nnf[0][1]);
        }
        case Kind::GEQ:
        {
          //(not (>= a b)) is rewritten as (< a b)
          return nm->mkNode(Kind::LT, nnf[0][0], nnf[0][1]);
        }
        case Kind::EQUAL:
        {
          // (not (= a b)) is the union of two half-spaces, so it is rewritten
          // as the disjunction (or (> a b) (< a b)).
          Node a = nnf[0][0];
          Node b = nnf[0][1];
          Node gt = nm->mkNode(Kind::GT, a, b);
          Node lt = nm->mkNode(Kind::LT, a, b);
          return gt.orNode(lt);
        }
        default:
          InternalError() << "Unexpected negated kind. Node " << n
                          << " has kind: " << n.getKind() << std::endl;
      }
      break;
    }
    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

std::vector<std::pair<Node, Node>> LiaStarUtils::removeIntegerItes(Node n,
                                                                   Env* e)
{
  // Lift integer if-then-elses out of an integer term into a list of guarded
  // alternatives. Each returned pair is (condition, ite-free term): the term is
  // the value of `n` when the condition holds, and the conditions are mutually
  // exclusive and exhaustive. For example
  //   (+ (ite c1 a b) (ite c2 c d))
  // returns the four pairs
  //   <(and c1 c2),           (+ a c)>
  //   <(and c1 (not c2)),     (+ a d)>
  //   <(and (not c1) c2),     (+ b c)>
  //   <(and (not c1) (not c2)),(+ b d)>
  Assert(n.getType().isInteger());
  NodeManager* nm = e->getNodeManager();
  Node trueConst = nm->mkConst<bool>(true);
  auto rw = e->getRewriter();
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::VARIABLE:
    case Kind::DUMMY_SKOLEM:
    case Kind::BOUND_VARIABLE:
    case Kind::NEG:
    case Kind::CONST_INTEGER:
      // a leaf term with no ite and the trivial (true) condition
      return {{trueConst, n}};
    case Kind::ADD:
    case Kind::SUB:
    case Kind::MULT:
    {
      // Combine the guarded alternatives of both operands pairwise: the
      // condition is the conjunction of the two operand conditions and the
      // value is the operator applied to the two operand values.
      std::vector<std::pair<Node, Node>> left = removeIntegerItes(n[0], e);
      std::vector<std::pair<Node, Node>> right = removeIntegerItes(n[1], e);
      std::vector<std::pair<Node, Node>> combined;
      for (const auto& l : left)
      {
        for (const auto& r : right)
        {
          Node condition = rw->rewrite(l.first.andNode(r.first));
          Node result = rw->rewrite(nm->mkNode(k, l.second, r.second));
          combined.push_back({condition, result});
        }
      }
      return combined;
    }
    case Kind::ITE:
    {
      // (ite c t e): guard the then-alternatives with c and the
      // else-alternatives with (not c).
      std::vector<std::pair<Node, Node>> iteResult;
      Node condition = removeItes(n[0], e);
      std::vector<std::pair<Node, Node>> thenPart = removeIntegerItes(n[1], e);
      for (const auto& pair : thenPart)
      {
        Node newCondition;
        if (pair.first == trueConst)
        {
          newCondition = condition;
        }
        else
        {
          newCondition = pair.first.andNode(condition);
        }
        iteResult.push_back({newCondition, pair.second});
      }

      // todo: restore this line Node notCondition =
      // rw->rewrite(condition.notNode());
      Node notCondition = condition.notNode();
      std::vector<std::pair<Node, Node>> elsePart = removeIntegerItes(n[2], e);
      for (const auto& pair : elsePart)
      {
        Node newCondition;
        if (pair.first == trueConst)
        {
          newCondition = notCondition;
        }
        else
        {
          newCondition = pair.first.andNode(notCondition);
        }
        iteResult.push_back({newCondition, pair.second});
      }
      return iteResult;
    }

    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

Result LiaStarUtils::areAssertionsUnsat(const std::vector<Node>& assertions,
                                        Env* e)
{
  // Decide whether a conjunction of literals is unsatisfiable, used by
  // `distribute` to prune dead branches of the DNF. Returns an unknown Result
  // when the sub-solver is disabled, so the caller keeps the conjunct.
  if (!e->getOptions().arith.arithLiaStarSubSolver)
  {
    return Result();
  }
  NodeManager* nm = e->getNodeManager();
  Node assertion;
  if (assertions.size() == 1)
  {
    assertion = assertions[0];
  }
  else
  {
    assertion = nm->mkNode(Kind::AND, assertions);
  }
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(assertion, fvs);
  std::vector<Node> freeVariables(fvs.begin(), fvs.end());
  if (fvs.size() > 0 && e->getOptions().arith.arithLiaStarNormalizAsSubSolver)
  {
    // Use Normaliz itself as the satisfiability oracle (the conjunction is a
    // single cone; an empty cone means unsat).
    Node variables = nm->mkNode(Kind::BOUND_VAR_LIST, freeVariables);
    assertion = expr::algorithm::flatten(nm, assertion);
    return normalizCheckSat(
        variables,
        assertion,
        e->getOptions().arith.arithLiaStarAssumeNonnegative);
  }
  else
  {
    // Use a regular cvc5 subsolver.
    return cvc5CheckSat(freeVariables, assertion, e);
  }
}

Node LiaStarUtils::getDisjunct(Node assertion,
                               const std::vector<Node>& from,
                               const std::vector<Node>& to,
                               Env* e,
                               SolverEngine* smte,
                               SolverEngine* probe,
                               const std::vector<Node>& bias)
{
  NodeManager* nm = e->getNodeManager();
  // The subsolver `smte` already has `assertion` (and the negations of the
  // previously discovered cone-disjuncts) asserted; we only check it and read
  // the model. `assertion` is passed here only to enumerate the atoms whose
  // truth value the disjunct fixes. When a `bias` is given (componentwise
  // bounds steering the model toward useful summands of the candidate
  // vector), it is checked first as assumptions; an unsatisfiable biased
  // query falls back to the unbiased one, so completeness (the unbiased
  // unsat answer below) is unaffected.
  Result result;
  if (!bias.empty())
  {
    result = smte->checkSat(bias);
    if (result.getStatus() == Result::Status::UNSAT)
    {
      result = smte->checkSat();
    }
  }
  else
  {
    result = smte->checkSat();
  }
  if (result.getStatus() == Result::Status::UNSAT)
  {
    // No region of the predicate is left uncovered: the cone encoding is exact.
    return nm->mkConst<>(false);
  }
  // Build one disjunct of the satisfying region by fixing every atom of the
  // formula to its truth value in the model. The result is a conjunction of
  // literals that implies the formula. We deliberately do not read the
  // arithmetic theory's facts: the linear solver eliminates variables using
  // equalities, so those equalities would be missing from the facts and the
  // resulting cone would be too coarse.
  std::vector<Node> atoms;
  std::unordered_set<Node> visited;
  collectAtoms(assertion, atoms, visited);
  std::vector<bool> values;
  for (const Node& atom : atoms)
  {
    values.push_back(smte->getValue(atom).getConst<bool>());
  }
  // Optionally generalize the cell: drop the atoms the formula's truth does
  // not depend on, so the cell (and hence its cone) covers more of the
  // predicate per refinement round.
  std::vector<bool> keep(atoms.size(), true);
  if (e->getOptions().arith.arithLiaStarGeneralize)
  {
    keep = generalizeCell(assertion, atoms, values);
  }
  std::vector<Node> literals;
  for (size_t i = 0; i < atoms.size(); i++)
  {
    if (!keep[i])
    {
      continue;
    }
    const Node& atom = atoms[i];
    Node literal;
    if (values[i])
    {
      // the atom is true in the model: keep it as is
      literal = atom;
    }
    else if (atom.getKind() == Kind::EQUAL && atom[0].getType().isInteger())
    {
      // A disequality is not convex (it is the union of two half-spaces), so it
      // cannot be a single cone. Pick the strict inequality on the side that
      // the model satisfies.
      Rational lhs = smte->getValue(atom[0]).getConst<Rational>();
      Rational rhs = smte->getValue(atom[1]).getConst<Rational>();
      Kind k = lhs > rhs ? Kind::GT : Kind::LT;
      literal = nm->mkNode(k, atom[0], atom[1]);
    }
    else
    {
      // the atom is false in the model: negate it
      literal = atom.notNode();
    }
    literals.push_back(literal);
  }
  // Optionally generalize the cell semantically: keep only a subset of the
  // literals that still implies the formula arithmetically, using `probe`
  // (the negated formula, in the same skolem space as the literals here) as
  // the entailment oracle.
  if (probe != nullptr)
  {
    semanticGeneralize(probe, literals);
  }
  if (literals.empty())
  {
    return nm->mkConst<>(true);
  }
  Node disjunct =
      literals.size() == 1 ? literals[0] : nm->mkNode(Kind::AND, literals);
  if (!from.empty())
  {
    // substitute the fresh constants back to the lambda's bound variables.
    disjunct =
        disjunct.substitute(to.begin(), to.end(), from.begin(), from.end());
  }
  return disjunct;
}

namespace {

/** Truth values of the three-valued evaluation used by `generalizeCell`. */
enum ThreeValued : uint8_t
{
  TV_FALSE = 0,
  TV_TRUE = 1,
  TV_UNKNOWN = 2,
};

/**
 * Evaluate the boolean skeleton of `n` under a partial assignment of its
 * atoms (atoms missing from `assignment` are unknown). Mirrors the traversal
 * of `LiaStarUtils::collectAtoms`: AND/OR/NOT are evaluated structurally,
 * boolean constants by value, everything else is an atom. `cache` memoizes
 * results for the current assignment (it must not be reused across
 * assignments).
 */
ThreeValued evalThreeValued(
    TNode n,
    const std::unordered_map<Node, ThreeValued>& assignment,
    std::unordered_map<Node, ThreeValued>& cache)
{
  if (n.getKind() == Kind::CONST_BOOLEAN)
  {
    return n.getConst<bool>() ? TV_TRUE : TV_FALSE;
  }
  auto it = cache.find(n);
  if (it != cache.end())
  {
    return it->second;
  }
  ThreeValued result;
  switch (n.getKind())
  {
    case Kind::NOT:
    {
      ThreeValued child = evalThreeValued(n[0], assignment, cache);
      result = child == TV_UNKNOWN ? TV_UNKNOWN
                                   : (child == TV_TRUE ? TV_FALSE : TV_TRUE);
      break;
    }
    case Kind::AND:
    case Kind::OR:
    {
      // AND: false dominates, then unknown, else true. OR is the dual.
      ThreeValued dominant = n.getKind() == Kind::AND ? TV_FALSE : TV_TRUE;
      ThreeValued identity = n.getKind() == Kind::AND ? TV_TRUE : TV_FALSE;
      result = identity;
      for (const Node& child : n)
      {
        ThreeValued value = evalThreeValued(child, assignment, cache);
        if (value == dominant)
        {
          result = dominant;
          break;
        }
        if (value == TV_UNKNOWN)
        {
          result = TV_UNKNOWN;
        }
      }
      break;
    }
    default:
    {
      auto a = assignment.find(n);
      result = a == assignment.end() ? TV_UNKNOWN : a->second;
      break;
    }
  }
  cache[n] = result;
  return result;
}

}  // namespace

void LiaStarUtils::semanticGeneralize(SolverEngine* probe,
                                      std::vector<Node>& literals)
{
  // The probe has the predicate's negation asserted, so a subset L of the
  // cell's literals implies the predicate iff checkSat(L) is unsat. The full
  // cell implies the predicate by construction, so the first check is unsat
  // and its assumption core already identifies a sufficient subset;
  // everything outside the core drops at once. Any other answer (sat or
  // unknown on a stale or resource-limited probe) conservatively keeps the
  // literals.
  if (literals.empty())
  {
    return;
  }
  Result result = probe->checkSat(literals);
  if (result.getStatus() != Result::Status::UNSAT)
  {
    return;
  }
  std::vector<Node> core = probe->getUnsatAssumptions();
  std::unordered_set<Node> coreSet(core.begin(), core.end());
  std::vector<Node> kept;
  for (const Node& literal : literals)
  {
    if (coreSet.count(literal) > 0)
    {
      kept.push_back(literal);
    }
  }
  // The core is not necessarily minimal: greedily try to drop each remaining
  // literal, equalities first -- dropping a model-true equality fattens the
  // cell from a hyperplane slice to a full-dimensional region, which merges
  // the most cells.
  std::stable_partition(kept.begin(), kept.end(), [](const Node& literal) {
    return literal.getKind() == Kind::EQUAL;
  });
  for (size_t i = 0; i < kept.size();)
  {
    std::vector<Node> candidate;
    candidate.reserve(kept.size() - 1);
    for (size_t j = 0; j < kept.size(); j++)
    {
      if (j != i)
      {
        candidate.push_back(kept[j]);
      }
    }
    Result r = candidate.empty() ? probe->checkSat() : probe->checkSat(candidate);
    if (r.getStatus() == Result::Status::UNSAT)
    {
      kept.erase(kept.begin() + i);
    }
    else
    {
      i++;
    }
  }
  literals = kept;
}

std::vector<bool> LiaStarUtils::generalizeCell(Node formula,
                                               const std::vector<Node>& atoms,
                                               const std::vector<bool>& values)
{
  // Greedily mark atoms as "don't care" while the formula still evaluates to
  // true under the partial assignment: the conjunction of the literals of
  // the remaining atoms then still (propositionally) implies the formula.
  std::unordered_map<Node, ThreeValued> assignment;
  for (size_t i = 0; i < atoms.size(); i++)
  {
    assignment[atoms[i]] = values[i] ? TV_TRUE : TV_FALSE;
  }
  std::vector<bool> keep(atoms.size(), true);
  {
    // Sanity: the model must satisfy the formula; if it does not (e.g. a
    // stale candidate model), generalizing would be unsound, so keep all.
    std::unordered_map<Node, ThreeValued> cache;
    if (evalThreeValued(formula, assignment, cache) != TV_TRUE)
    {
      return keep;
    }
  }
  for (size_t i = 0; i < atoms.size(); i++)
  {
    ThreeValued saved = assignment[atoms[i]];
    assignment[atoms[i]] = TV_UNKNOWN;
    std::unordered_map<Node, ThreeValued> cache;
    if (evalThreeValued(formula, assignment, cache) == TV_TRUE)
    {
      keep[i] = false;
    }
    else
    {
      assignment[atoms[i]] = saved;
    }
  }
  return keep;
}

void LiaStarUtils::collectAtoms(Node n,
                                std::vector<Node>& atoms,
                                std::unordered_set<Node>& visited)
{
  // Walk the boolean skeleton of `n` and collect its atomic predicates (the
  // boolean leaves) in deterministic order, deduplicating via `visited`.
  if (!visited.insert(n).second)
  {
    return;
  }
  switch (n.getKind())
  {
    case Kind::CONST_BOOLEAN: return;
    case Kind::NOT:
    case Kind::AND:
    case Kind::OR:
    case Kind::IMPLIES:
    case Kind::XOR:
    case Kind::ITE:
    {
      for (const Node& child : n)
      {
        if (child.getType().isBoolean())
        {
          collectAtoms(child, atoms, visited);
        }
      }
      return;
    }
    default:
    {
      // an atomic predicate (comparison or boolean equality)
      atoms.push_back(n);
      return;
    }
  }
}

Result LiaStarUtils::cvc5CheckSat(const std::vector<Node>& freeVariables,
                                  Node assertion,
                                  Env* e)
{
  // Check the satisfiability of `assertion` with a fresh cvc5 subsolver. The
  // variables are constrained to be non-negative only under
  // arithLiaStarAssumeNonnegative; by default the star-contains lambda body
  // (part of `assertion`) carries the user's constraints, and adding
  // non-negativity here would make this oracle report UNSAT for conjunctions
  // that are satisfiable over Z^n, pruning live DNF branches. Genuine bound
  // variables are existentially quantified; free constants are left in place
  // (checking a formula with free constants is the same as checking its
  // existential closure).
  Options subOptions;
  SubsolverSetupInfo ssi(*e, subOptions);

  Result result;
  if (freeVariables.size() == 0)
  {
    result = checkWithSubsolver(assertion, ssi);
  }
  else
  {
    NodeManager* nm = e->getNodeManager();
    Node zero = nm->mkConstInt(Rational(0));
    const bool assumeNonnegative =
        e->getOptions().arith.arithLiaStarAssumeNonnegative;
    std::vector<Node> boundVariables;
    for (Node var : freeVariables)
    {
      if (assumeNonnegative)
      {
        assertion = assertion.andNode(nm->mkNode(Kind::GEQ, var, zero));
      }
      if (var.getKind() == Kind::BOUND_VARIABLE)
      {
        boundVariables.push_back(var);
      }
    }
    Node query = assertion;
    if (!boundVariables.empty())
    {
      Node varList = nm->mkNode(Kind::BOUND_VAR_LIST, boundVariables);
      query = nm->mkNode(Kind::EXISTS, varList, assertion);
    }
    result = checkWithSubsolver(query, ssi);
  }
  Trace("liastar-ext-cvc5CheckSat")
      << "Conjunction: " << assertion << " is " << result << std::endl;
  return result;
}

Cone<Integer> LiaStarUtils::buildCone(
    size_t dimension,
    const std::vector<std::string>& constraints,
    bool assumeNonnegative,
    LiaStarStatistics* stats)
{
  if (stats)
  {
    stats->d_dimensionMax.maxAssign(dimension);
  }
  // The single point of contact with libnormaliz. Render the constraint rows
  // into a Normaliz "symbolic constraints" input block over `dimension`-many
  // variables, asking for the Hilbert basis and the module generators. Then
  // construct the cone and compute those two properties.
  libnormaliz::OptionsHandler options;

  std::map<libnormaliz::PolyParam::Param, std::vector<std::string>>
      poly_param_input;
  std::map<libnormaliz::NumParam::Param, long> num_param_input;
  std::map<libnormaliz::BoolParam::Param, bool> bool_param_input;

  libnormaliz::renf_class_ptr number_field_ref;

  std::stringstream ss;
  ss << "amb_space " << dimension << std::endl;
  ss << "constraints " << constraints.size() << " symbolic" << std::endl;
  for (const auto& constraint : constraints)
  {
    ss << constraint << std::endl;
  }
  if (assumeNonnegative)
  {
    ss << "nonnegative" << std::endl;
  }
  else
  {
    // Normaliz's constraint-only input defaults to the non-negative orthant,
    // which would silently drop the summands with a negative coordinate. Since
    // int.star-contains constrains its summands only through the lambda under
    // the star, declare every coordinate sign-unrestricted instead.
    // `signs` takes entries in {-1, 0, 1}: 1 at position i means x_i >= 0, -1
    // means x_i <= 0, and 0 imposes no inequality.
    ss << "signs" << std::endl;
    for (size_t sj = 0; sj < dimension; sj++)
    {
      ss << (sj == 0 ? "" : " ") << "0";
    }
    ss << std::endl;
  }
  ss << "HilbertBasis" << std::endl;
  ss << "ModuleGenerators" << std::endl;
  Trace("liastar-ext") << "normaliz input:" << std::endl;
  Trace("liastar-ext") << ss.str() << std::endl;

  // here we use mpq_class instead of Integer (or mpz_class)
  // because libnormaliz.so only has implementation for
  // readNormalizInput<mpq_class>
  std::map<Type::InputType, libnormaliz::Matrix<mpq_class>> input;
  if (stats) stats->d_normalizInputTime.start();
  input = libnormaliz::readNormalizInput<mpq_class>(ss,
                                                    options,
                                                    num_param_input,
                                                    bool_param_input,
                                                    poly_param_input,
                                                    number_field_ref);
  if (stats) stats->d_normalizInputTime.stop();
  if (stats)
  {
    ++stats->d_normalizCalls;
    stats->d_normalizComputeTime.start();
  }
  Cone<Integer> cone(input);
  cone.setNonnegative(assumeNonnegative);
  // always use infinite precision for integers
  cone.deactivateChangeOfPrecision();
  cone.compute(ConeProperty::HilbertBasis);
  cone.compute(ConeProperty::ModuleGenerators);
  // completes the Hilbert basis for a non-pointed cone
  cone.compute(ConeProperty::MaximalSubspace);
  if (stats) stats->d_normalizComputeTime.stop();
  if (stats)
  {
    stats->d_hilbertBasisTotal += cone.getHilbertBasis().size();
    stats->d_hilbertBasisMax.maxAssign(cone.getHilbertBasis().size());
    stats->d_moduleGeneratorsTotal += cone.getModuleGenerators().size();
    stats->d_moduleGeneratorsMax.maxAssign(cone.getModuleGenerators().size());
  }
  return cone;
}

std::vector<std::vector<Integer>> LiaStarUtils::getHilbertBasisWithLineality(
    Cone<Integer>& cone, size_t& numPointed)
{
  std::vector<std::vector<Integer>> basis = cone.getHilbertBasis();
  numPointed = basis.size();
  for (const std::vector<Integer>& generator : cone.getMaximalSubspace())
  {
    basis.push_back(generator);
  }
  return basis;
}

bool LiaStarUtils::isEmptyCone(Cone<Integer>& cone)
{
  // AffineDim is only computed for inhomogeneous cones; -1 marks the
  // (inhomogeneous) constraint system as infeasible, i.e. the cone is empty.
  if (cone.isInhomogeneous())
  {
    return cone.getAffineDim() == -1;
  }
  return false;
}

Result LiaStarUtils::normalizCheckSat(Node variables,
                                     Node assertion,
                                     bool assumeNonnegative)
{
  // Use Normaliz as a satisfiability oracle for a single conjunction of linear
  // constraints: the conjunction is satisfiable iff the corresponding cone is
  // non-empty. Only the UNSAT verdict is meaningful here; otherwise an unknown
  // Result is returned. The domain is the non-negative orthant when
  // `assumeNonnegative` is set and all of Z^n otherwise.
  Trace("liastar-normalizCheckSat")
      << "---------------------------" << std::endl;
  Trace("liastar-normalizCheckSat")
      << "Cone for node: " << assertion << std::endl;

  const std::vector<std::pair<std::vector<std::string>, Node>>& matrices =
      getMatrices(variables, assertion);
  Cone<Integer> cone = buildCone(
      variables.getNumChildren(), matrices[0].first, assumeNonnegative);

  Result result;
  if (isEmptyCone(cone))
  {
    Trace("liastar-ext") << "empty cone" << std::endl;
    result = Result(Result::Status::UNSAT);
  }
  Trace("liastar-ext-normalizCheckSat")
      << "Constraints are " << result << std::endl;
  return result;
}

std::vector<std::pair<std::vector<std::string>, Node>>
LiaStarUtils::getMatrices(Node variables, Node n)
{
  // Render a DNF predicate into one Normaliz matrix per disjunct (cone). A
  // disjunction yields one matrix per child; any other shape (atom,
  // conjunction, boolean constant) is a single disjunct handled by `getMatrix`.
  Assert(n.getType().isBoolean()) << "n: " << n << std::endl;
  if (n.getKind() == Kind::OR)
  {
    std::vector<std::pair<std::vector<std::string>, Node>> pairs;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
      Trace("liastar-ext") << "Disjunction " << i << ": " << n[i] << std::endl;
      pairs.push_back(getMatrix(variables, n[i]));
    }
    return pairs;
  }
  return {getMatrix(variables, n)};
}

std::pair<std::vector<std::string>, Node> LiaStarUtils::getMatrix(
    Node variables, Node n)
{
  // Render a single cone (a conjunction of linear (in)equalities, or one
  // atom/boolean constant) into a list of Normaliz "symbolic" constraint
  // strings paired with the original node `n`. The boolean constants are
  // encoded as the trivially-true row "x[1] = x[1];" and the infeasible row
  // "1 = 0;".
  Assert(n.getType().isBoolean()) << "n: " << n << std::endl;
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::CONST_BOOLEAN:
    {
      bool value = n.getConst<bool>();
      std::string constraint = value ? "x[1] = x[1];" : "1 = 0;";
      std::vector<std::string> constraints{constraint};
      return {constraints, n};
    }
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL:
    {
      // a comparison "lhs <op> rhs;" with each side printed as a linear term
      linear::Polynomial l = linear::Polynomial::parsePolynomial(n[0]);
      linear::Polynomial r = linear::Polynomial::parsePolynomial(n[1]);
      std::string lTerm = getString(variables, l);
      std::string rTerm = getString(variables, r);
      std::string kString = k == Kind::LT    ? " < "
                            : k == Kind::GT  ? " > "
                            : k == Kind::LEQ ? " <= "
                            : k == Kind::GEQ ? " >= "
                                             : " = ";
      std::string constraint = lTerm + kString + rTerm + ";";
      std::vector<std::string> constraints{constraint};
      return {constraints, n};
    }
    case Kind::AND:
    {
      // one row per conjunct (each conjunct is a single-constraint atom)
      std::vector<std::string> constraints;
      for (size_t i = 0; i < n.getNumChildren(); i++)
      {
        std::pair<std::vector<std::string>, Node> m =
            getMatrix(variables, n[i]);
        constraints.push_back(m.first[0]);
      }
      return {constraints, n};
    }

    default:
    {
      InternalError() << "Unexpected kind. Node " << n
                      << " has kind: " << n.getKind() << std::endl;
    };
  }
}

std::string LiaStarUtils::getString(Node variables, linear::Polynomial& p)
{
  // Print a linear polynomial in Normaliz syntax, mapping the i-th bound
  // variable to the placeholder "x[i+1]" (Normaliz indexes from 1). For
  // example, with variables (a b), the polynomial 2a - b + 3 prints as
  // "2x[1] - x[2] + 3".
  Assert(variables.getKind() == Kind::BOUND_VAR_LIST)
      << "variables: " << variables << std::endl;

  size_t size = variables.getNumChildren();
  Assert(p.isIntegral()) << p.getNode() << " is expected to be linear"
                         << std::endl;
  std::stringstream ss;
  int index = 0;
  for (const linear::Monomial& monomial : p)
  {
    Trace("liastar-ext-debug")
        << "monomial: " << monomial.getNode() << std::endl;
    linear::Constant c = monomial.getConstant();
    Trace("liastar-ext-debug") << "c: " << c.getNode() << std::endl;
    Rational r = c.getValue().abs();

    // print the sign
    if (c.isNegative())
    {
      ss << " - ";
    }
    else if (index > 0)
    {
      ss << " + ";
    }
    index++;

    if (monomial.isConstant())
    {
      ss << r;
      continue;
    }
    // print the coefficient, omitting a unit coefficient
    if (r != Rational(1))
    {
      ss << r;
    }
    // find the variable's index among the bound variables
    for (size_t i = 0; i < size; i++)
    {
      linear::VarList varList = monomial.getVarList();
      for (const auto& var : varList)
      {
        if (var.getNode() == variables[i])
        {
          ss << "x[" << i + 1 << "]";
        }
      }
    }
  }
  Trace("liastar-ext-debug") << "polynomial  : " << p.getNode() << std::endl;
  Trace("liastar-ext-debug") << "string : " << ss.str() << std::endl;
  return ss.str();
}

void LiaStarUtils::getGeneratorBody(
    size_t dimension,
    const std::vector<Integer>& generator,
    Cone<Integer>& cone,
    bool star,
    bool useSkolems,
    NodeManager* nm,
    std::vector<Node>& vars,
    std::vector<Node>& constraints,
    std::vector<Node>& point,
    std::vector<std::vector<Node>>& rays)
{
  // Encode one module generator `g` of a cone whose recession cone is generated
  // by the cone's Hilbert basis `{h_1, ..., h_m}`. The integer points reachable
  // from this generator are `g + sum_j l_j * h_j`, where l_j is non-negative
  // for the pointed part and unrestricted in sign for a lineality direction
  // (which is available in both directions). There
  // are two flavours:
  //
  //   membership (star == false): the contribution of this generator is the
  //     point `g + sum_j l_j h_j`, with `g` a fixed offset (multiplier 1). Used
  //     to express that the vector is a single member of the set.
  //
  //   star (star == true): the generator may be used `mu >= 0` times, so its
  //     contribution is `mu * g + sum_j l_j h_j`, with the coupling
  //     `mu = 0 => l_j = 0` (a ray can only be taken if its generator is). This
  //     encodes membership in the additive closure (the star).
  //
  // The fresh multipliers (`mu` and the `l_j`) are skolem constants when
  // `useSkolems` (the constraints are asserted at the top level) or bound
  // variables otherwise (the caller existentially binds them).
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  std::vector<Integer> zeroVector(dimension, Integer(0));

  // The multiplier for the module generator. In the membership encoding the
  // generator is a fixed offset (multiplier 1). In the star encoding it is a
  // fresh variable counting how many times the generator is used, except for
  // the zero generator (the cone's homogeneous part) which is always present
  // once.
  Node mu = one;
  if (star && generator != zeroVector)
  {
    mu = useSkolems ? nm->mkDummySkolem("mu", nm->integerType())
                    : nm->mkBoundVar("mu", nm->integerType());
    vars.push_back(mu);
  }
  if (star)
  {
    // (>= mu 0)
    constraints.push_back(nm->mkNode(Kind::GEQ, mu, zero));
  }

  // point = mu * generator (in the membership encoding mu == 1, so the point is
  // just the generator)
  for (const auto& element : generator)
  {
    Node constant = nm->mkConstInt(Rational(element));
    Node monomial = star ? nm->mkNode(Kind::MULT, constant, mu) : constant;
    point.push_back(monomial);
  }

  // one ray l_j * h_j per Hilbert basis element h_j
  size_t numPointed = 0;
  const std::vector<std::vector<Integer>> hilbertBasis =
      getHilbertBasisWithLineality(cone, numPointed);
  for (size_t index = 0; index < hilbertBasis.size(); index++)
  {
    const std::vector<Integer>& basis = hilbertBasis[index];
    std::string name = "l" + std::to_string(index + 1);
    Node l = useSkolems ? nm->mkDummySkolem(name, nm->integerType())
                        : nm->mkBoundVar(name, nm->integerType());
    vars.push_back(l);
    if (index < numPointed)
    {
      // (>= l 0); a lineality direction is unrestricted in sign
      constraints.push_back(nm->mkNode(Kind::GEQ, l, zero));
    }
    if (star)
    {
      // (=> (= mu 0) (= l 0)): a ray may only be used if its generator is.
      constraints.push_back(nm->mkNode(Kind::EQUAL, mu, zero)
                                .impNode(nm->mkNode(Kind::EQUAL, l, zero)));
    }

    std::vector<Node> ray;
    for (const auto& element : basis)
    {
      Node constant = nm->mkConstInt(Rational(element));
      ray.push_back(nm->mkNode(Kind::MULT, constant, l));
    }
    rays.push_back(ray);
  }
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */
