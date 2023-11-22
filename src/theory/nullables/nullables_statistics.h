/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for the theory of nullables.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__NULLABLES_STATISTICS_H
#define CVC5__THEORY__NULLABLES_STATISTICS_H

#include "theory/nullables/rewrites.h"
#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace nullables {

/**
 * Statistics for the theory of nullables.
 */
class NullablesStatistics
{
 public:
  NullablesStatistics(StatisticsRegistry& sr);

  /** Counts the number of applications of each type of rewrite rule */
  HistogramStat<Rewrite> d_rewrites;
};

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__NULLABLES_STATISTICS_H */
