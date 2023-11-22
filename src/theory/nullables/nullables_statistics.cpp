/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds
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

#include "theory/nullables/nullables_statistics.h"

namespace cvc5::internal {
namespace theory {
namespace nullables {

NullablesStatistics::NullablesStatistics(StatisticsRegistry& sr)
    : d_rewrites(sr.registerHistogram<Rewrite>("theory::nullables::rewrites"))
{
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal
