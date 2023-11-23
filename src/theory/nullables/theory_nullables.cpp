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
 * Nullables theory.
 */

#include "theory/nullables/theory_nullables.h"

#include "expr/skolem_manager.h"
#include "proof/proof_checker.h"
#include "smt/logic_exception.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

TheoryNullables::TheoryNullables(Env& env,
                                 OutputChannel& out,
                                 Valuation valuation)
    : Theory(THEORY_NULLABLES, env, out, valuation)
{
}

TheoryNullables::~TheoryNullables() {}

std::string TheoryNullables::identify() const { return "THEORY_NULLABLES"; }

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal
