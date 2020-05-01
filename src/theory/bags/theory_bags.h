/*********************                                                        */
/*! \file theory_bags.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Kshitij Bansal, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory.
 **
 ** Bags theory.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_BAGS_H
#define CVC4__THEORY__BAGS__THEORY_BAGS_H

#include <memory>

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace bags {

class TheoryBagsPrivate;
class TheoryBagsScrutinize;

class TheoryBags : public Theory
{
 public:
  /** Constructs a new instance of TheoryBags w.r.t. the provided contexts. */
  TheoryBags(context::Context* c,
             context::UserContext* u,
             OutputChannel& out,
             Valuation valuation,
             const LogicInfo& logicInfo);
  ~TheoryBags() override;

  TheoryRewriter* getTheoryRewriter() override;

  /** finish initialization */
  void finishInit() override;
  void addSharedTerm(TNode) override;
  void check(Effort) override;
  bool collectModelInfo(TheoryModel* m) override;

  Node explain(TNode) override;
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  Node getModelValue(TNode) override;
  std::string identify() const override { return "THEORY_BAGS"; }
  void preRegisterTerm(TNode node) override;
  Node expandDefinition(Node n) override;
  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions) override;
  void presolve() override;
  void propagate(Effort) override;
  void setMasterEqualityEngine(eq::EqualityEngine* eq) override;
  bool isEntailed(Node n, bool pol);

 private:
  friend class TheoryBagsPrivate;
  friend class TheoryBagsScrutinize;

  std::unique_ptr<TheoryBagsPrivate> d_internal;
}; /* class TheoryBags */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_H */
