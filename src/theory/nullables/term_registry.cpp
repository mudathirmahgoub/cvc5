/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of nullables term registry object.
 */

#include "theory/nullables/term_registry.h"

#include "expr/emptyset.h"
#include "theory/nullables/inference_manager.h"
#include "theory/nullables/solver_state.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace nullables {

TermRegistry::TermRegistry(Env& env, SolverState& state, InferenceManager& im)
    : EnvObj(env),
      d_im(im),
      d_proxy(userContext()),
      d_proxy_to_term(userContext())
{
}

Node TermRegistry::getEmptyNullable(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator it = d_emptynullable.find(tn);
  if (it != d_emptynullable.end())
  {
    return it->second;
  }
  Node n = NodeManager::currentNM()->mkConst(EmptySet(tn));
  d_emptynullable[tn] = n;
  return n;
}

}  // namespace nullables
}  // namespace theory
}  // namespace cvc5::internal
