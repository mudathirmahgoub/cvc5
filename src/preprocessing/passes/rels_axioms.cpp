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
 * The rels-axioms preprocessing pass.
 */

#include "preprocessing/passes/rels_axioms.h"

#include "expr/node_algorithm.h"
#include "options/sets_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

RelsAxioms::RelsAxioms(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "rels-axioms")
{
}

Node RelsAxioms::functionalityConstraint(Node q)
{
  if (q.getKind() != Kind::FORALL || q[0].getNumChildren() != 3)
  {
    return Node::null();
  }
  Node body = q[1];
  // literals of the clause: the body is either an OR (the rewritten form) or
  // an implication with a conjunction of two premises
  std::vector<Node> lits;
  if (body.getKind() == Kind::OR)
  {
    lits.insert(lits.end(), body.begin(), body.end());
  }
  else if (body.getKind() == Kind::IMPLIES)
  {
    Node ante = body[0];
    if (ante.getKind() == Kind::AND)
    {
      for (const Node& c : ante)
      {
        lits.push_back(c.negate());
      }
    }
    else
    {
      lits.push_back(ante.negate());
    }
    lits.push_back(body[1]);
  }
  else
  {
    return Node::null();
  }
  if (lits.size() != 3)
  {
    return Node::null();
  }
  Node eq;
  std::vector<Node> mems;
  for (const Node& l : lits)
  {
    if (l.getKind() == Kind::EQUAL && l[0].getKind() == Kind::BOUND_VARIABLE
        && l[1].getKind() == Kind::BOUND_VARIABLE)
    {
      eq = l;
    }
    else if (l.getKind() == Kind::NOT && l[0].getKind() == Kind::SET_MEMBER
             && l[0][0].getKind() == Kind::APPLY_CONSTRUCTOR
             && l[0][0].getNumChildren() == 2
             && l[0][0][0].getKind() == Kind::BOUND_VARIABLE
             && l[0][0][1].getKind() == Kind::BOUND_VARIABLE)
    {
      mems.push_back(l[0]);
    }
    else
    {
      return Node::null();
    }
  }
  if (eq.isNull() || mems.size() != 2 || mems[0][1] != mems[1][1]
      || expr::hasBoundVar(mems[0][1]))
  {
    return Node::null();
  }
  Node j = mems[0][1];
  Node x1 = mems[0][0][0], y1 = mems[0][0][1];
  Node x2 = mems[1][0][0], y2 = mems[1][0][1];
  auto samePair = [](Node a, Node b, Node c, Node d) {
    return (a == c && b == d) || (a == d && b == c);
  };
  NodeManager* nm = nodeManager();
  Node jt = nm->mkNode(Kind::RELATION_TRANSPOSE, j);
  Node join;
  TypeNode elemType;
  if (x1 == x2 && y1 != y2 && samePair(y1, y2, eq[0], eq[1]))
  {
    // functional: J^T ; J subset identity
    join = nm->mkNode(Kind::RELATION_JOIN, jt, j);
    elemType = y1.getType();
  }
  else if (y1 == y2 && x1 != x2 && samePair(x1, x2, eq[0], eq[1]))
  {
    // injective: J ; J^T subset identity
    join = nm->mkNode(Kind::RELATION_JOIN, j, jt);
    elemType = x1.getType();
  }
  else
  {
    return Node::null();
  }
  TypeNode tupleType = nm->mkTupleType({elemType});
  TypeNode setType = nm->mkSetType(tupleType);
  Node univ = nm->mkNullaryOperator(setType, Kind::SET_UNIVERSE);
  Node iden = nm->mkNode(Kind::RELATION_IDEN, univ);
  return nm->mkNode(Kind::SET_SUBSET, join, iden);
}

PreprocessingPassResult RelsAxioms::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // the identity over the universe needs the universe set
  if (!options().sets.setsExp)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }
  NodeManager* nm = nodeManager();
  std::vector<Node> added;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node q = (*assertionsToPreprocess)[i];
    Node c = functionalityConstraint(q);
    if (c.isNull() || std::find(added.begin(), added.end(), c) != added.end())
    {
      continue;
    }
    Trace("rels-axioms") << "rels-axioms: " << q << " gives " << c << std::endl;
    added.push_back(c);
    // Replace the axiom by its conjunction with the constraint, so that the
    // constraint depends on the axiom (unsat cores, proofs).
    assertionsToPreprocess->replace(i, nm->mkNode(Kind::AND, q, c));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
