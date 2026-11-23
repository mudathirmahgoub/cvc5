/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference information utility.
 */

#include "theory/bags/infer_info.h"

#include "theory/bags/inference_manager.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

InferInfo::InferInfo(InferenceManager* im, InferenceId id)
    : TheoryInference(id), d_im(im)
{
}

TrustNode InferInfo::processLemma(CVC5_UNUSED LemmaProperty& p)
{
  Node lemma = getLemma();
  Trace("bags::InferInfo::process") << (*this) << std::endl;
  // the inference manager registers the lemma with its proof constructor, if
  // proofs are enabled
  ProofGenerator* pg = d_im->notifyLemma(lemma, getId(), getPremise());
  return TrustNode::mkTrustLemma(lemma, pg);
}

Node InferInfo::getLemma() const
{
  if (d_premises.empty())
  {
    return d_conclusion;
  }
  NodeManager* nm = d_im->getNodeManager();
  return nm->mkNode(Kind::IMPLIES, getPremise(), d_conclusion);
}

Node InferInfo::getPremise() const
{
  return d_im->getNodeManager()->mkAnd(d_premises);
}

bool InferInfo::isTrivial() const
{
  Assert(!d_conclusion.isNull());
  return d_conclusion.isConst() && d_conclusion.getConst<bool>();
}

bool InferInfo::isConflict() const
{
  Assert(!d_conclusion.isNull());
  return d_conclusion.isConst() && !d_conclusion.getConst<bool>();
}

bool InferInfo::isFact() const
{
  Assert(!d_conclusion.isNull());
  TNode atom =
      d_conclusion.getKind() == Kind::NOT ? d_conclusion[0] : d_conclusion;
  return !atom.isConst() && atom.getKind() != Kind::OR;
}

std::ostream& operator<<(std::ostream& out, const InferInfo& ii)
{
  out << "(infer ;id " << std::endl << ii.getId() << std::endl;
  out << ";conclusion " << std::endl << ii.d_conclusion << std::endl;
  if (!ii.d_premises.empty())
  {
    out << " ;premise" << std::endl << ii.d_premises << std::endl;
  }
  out << ")";
  return out;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
