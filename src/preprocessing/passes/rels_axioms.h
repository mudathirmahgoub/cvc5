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
 * The rels-axioms preprocessing pass: recognizes quantified axioms that state
 * a property of a relation in first-order terms and adds the equivalent
 * relational constraint, which the relations solver can use inductively.
 *
 * Currently recognized (option --rels-functional-axioms):
 *   forall x y z. (x,y) in J /\ (x,z) in J => y = z   (J is functional)
 *     adds  (rel.join (rel.transpose J) J) subset (rel.iden universe)
 *   forall x y z. (y,x) in J /\ (z,x) in J => y = z   (J is injective)
 *     adds  (rel.join J (rel.transpose J)) subset (rel.iden universe)
 * The quantified axiom is kept; the added constraint is a consequence of it.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__RELS_AXIOMS_H
#define CVC5__PREPROCESSING__PASSES__RELS_AXIOMS_H

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class RelsAxioms : public PreprocessingPass
{
 public:
  RelsAxioms(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /**
   * If q is a functionality or injectivity axiom of a binary relation J (see
   * the file header), return the corresponding relational constraint;
   * otherwise return the null node.
   */
  Node functionalityConstraint(Node q);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
