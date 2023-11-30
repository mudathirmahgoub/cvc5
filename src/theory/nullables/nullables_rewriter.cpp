/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Nullables theory rewriter.
 */

#include "theory/nullables/nullables_rewriter.h"

#include "theory/rewriter.h"
#include "util/rational.h"
#include "util/statistics_registry.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

NullablesRewriteResponse::NullablesRewriteResponse()
    : d_node(Node::null()), d_rewrite(Rewrite::NONE)
{
}

NullablesRewriteResponse::NullablesRewriteResponse(Node n, Rewrite rewrite)
    : d_node(n), d_rewrite(rewrite)
{
}

NullablesRewriteResponse::NullablesRewriteResponse(
    const NullablesRewriteResponse& r)
    : d_node(r.d_node), d_rewrite(r.d_rewrite)
{
}

NullablesRewriter::NullablesRewriter(Rewriter* r,
                                     HistogramStat<Rewrite>* statistics)
    : d_rewriter(r), d_statistics(statistics)
{
  d_nm = NodeManager::currentNM();
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one = d_nm->mkConstInt(Rational(1));
}

RewriteResponse NullablesRewriter::postRewrite(TNode n)
{
  NullablesRewriteResponse response;
  if (n.isConst())
  {
    // no need to rewrite n if it is already in a normal form
    response = NullablesRewriteResponse(n, Rewrite::NONE);
  }
  else if (n.getKind() == Kind::EQUAL)
  {
    response = postRewriteEqual(n);
  }
  else if (n.getKind() == Kind::NULLABLE_VAL)
  {
    response = postRewriteSelect(n);
  }
  else
  {
    response = NullablesRewriteResponse(n, Rewrite::NONE);
  }

  Trace("nullables-rewrite")
      << "postRewrite " << n << " to " << response.d_node << " by "
      << response.d_rewrite << "." << std::endl;

  if (d_statistics != nullptr)
  {
    (*d_statistics) << response.d_rewrite;
  }
  if (response.d_node != n)
  {
    return RewriteResponse(RewriteStatus::REWRITE_AGAIN_FULL, response.d_node);
  }
  return RewriteResponse(RewriteStatus::REWRITE_DONE, n);
}

NullablesRewriteResponse NullablesRewriter::postRewriteEqual(
    const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    Node ret = d_nm->mkConst(true);
    return NullablesRewriteResponse(ret, Rewrite::EQ_REFL);
  }

  if (n[0].isConst() && n[1].isConst())
  {
    Node ret = d_nm->mkConst(false);
    return NullablesRewriteResponse(ret, Rewrite::EQ_CONST_FALSE);
  }

  // standard ordering
  if (n[0] > n[1])
  {
    Node ret = d_nm->mkNode(Kind::EQUAL, n[1], n[0]);
    return NullablesRewriteResponse(ret, Rewrite::EQ_SYM);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

RewriteResponse NullablesRewriter::preRewrite(TNode n)
{
  NullablesRewriteResponse response;
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::EQUAL: response = preRewriteEqual(n); break;
    default: response = NullablesRewriteResponse(n, Rewrite::NONE);
  }

  Trace("nullables-rewrite")
      << "preRewrite " << n << " to " << response.d_node << " by "
      << response.d_rewrite << "." << std::endl;

  if (d_statistics != nullptr)
  {
    (*d_statistics) << response.d_rewrite;
  }
  if (response.d_node != n)
  {
    return RewriteResponse(RewriteStatus::REWRITE_AGAIN_FULL, response.d_node);
  }
  return RewriteResponse(RewriteStatus::REWRITE_DONE, n);
}

NullablesRewriteResponse NullablesRewriter::preRewriteEqual(
    const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    // (= A A) = true where A is a nullable
    return NullablesRewriteResponse(d_nm->mkConst(true),
                                    Rewrite::IDENTICAL_NODES);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

NullablesRewriteResponse NullablesRewriter::postRewriteSelect(
    const TNode& n) const
{
  Assert(n.getKind() == Kind::NULLABLE_VAL);
  if (n[0].getKind() == Kind::NULLABLE_SOME)
  {
    return NullablesRewriteResponse(n[0][0], Rewrite::IDENTICAL_NODES);
  }
  return NullablesRewriteResponse(n, Rewrite::NONE);
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal
