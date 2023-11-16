/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__NULLABLES__THEORY_NULLABLES_REWRITER_H
#define CVC5__THEORY__NULLABLES__THEORY_NULLABLES_REWRITER_H

#include "theory/nullables/rewrites.h"
#include "theory/theory_rewriter.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace nullables {

/** a class represents the result of rewriting nullable nodes */
struct NullablesRewriteResponse
{
  NullablesRewriteResponse();
  NullablesRewriteResponse(Node n, Rewrite rewrite);
  NullablesRewriteResponse(const NullablesRewriteResponse& r);
  /** the rewritten node */
  Node d_node;
  /** type of rewrite used by nullables */
  Rewrite d_rewrite;

}; /* struct NullablesRewriteResponse */

class NullablesRewriter : public TheoryRewriter
{
 public:
  NullablesRewriter(Rewriter* r, HistogramStat<Rewrite>* statistics = nullptr);

  /**
   * postRewrite nodes with kinds: . See the
   * rewrite rules for these kinds below.
   */
  RewriteResponse postRewrite(TNode n) override;
  /**
   * preRewrite nodes with kinds: EQUAL, NULLABLE_SUBNULLABLE, NULLABLE_MEMBER.
   * See the rewrite rules for these kinds below.
   */
  RewriteResponse preRewrite(TNode n) override;

 private:
  /**
   * rewrites for n include:
   * - (= A A) = true where A is a nullable
   */
  NullablesRewriteResponse preRewriteEqual(const TNode& n) const;

  /**
   * rewrites for n include:
   * - (nullable.count x nullable.empty) = 0
   * - (nullable.count x (nullable x c)) = (ite (>= c 1) c 0)
   * - otherwise = n
   */
  NullablesRewriteResponse rewriteNullableCount(const TNode& n) const;

 private:
  /** Reference to the rewriter statistics. */
  NodeManager* d_nm;
  Node d_zero;
  Node d_one;
  /**
   * Pointer to the rewriter. NOTE this is a cyclic dependency, and should
   * be removed.
   */
  Rewriter* d_rewriter;
  /** Reference to the rewriter statistics. */
  HistogramStat<Rewrite>* d_statistics;
}; /* class TheoryNullablesRewriter */

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES__THEORY_NULLABLES_REWRITER_H */
