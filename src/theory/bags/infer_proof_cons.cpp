/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference to proof conversion for bags.
 */

#include "theory/bags/infer_proof_cons.h"

#include "expr/skolem_manager.h"
#include "proof/proof_node_manager.h"
#include "proof/theory_proof_step_buffer.h"
#include "proof/trust_id.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

InferProofCons::InferProofCons(Env& env)
    : EnvObj(env), d_lemmaId(userContext()), d_lemmaExp(userContext())
{
  d_true = nodeManager()->mkConst(true);
}

void InferProofCons::notifyLemma(const Node& lem,
                                 InferenceId id,
                                 const Node& exp)
{
  Trace("bags-ipc-debug") << "BagsIpc::lemma " << lem << " " << id
                          << std::endl;
  Assert(exp == d_true || (lem.getKind() == Kind::IMPLIES && lem[0] == exp));
  d_lemmaId[lem] = id;
  d_lemmaExp[lem] = exp;
}

std::shared_ptr<ProofNode> InferProofCons::getProofFor(Node lem)
{
  NodeInferenceMap::iterator it = d_lemmaId.find(lem);
  Assert(it != d_lemmaId.end());
  InferenceId id = it->second;
  Node exp = d_lemmaExp[lem];

  CDProof cdp(d_env);
  std::vector<Node> assumps;
  Node conc = lem;
  if (exp != d_true)
  {
    // lem is (=> exp conc), which we prove by SCOPE over the premises
    Assert(lem.getKind() == Kind::IMPLIES);
    if (exp.getKind() == Kind::AND)
    {
      assumps.insert(assumps.end(), exp.begin(), exp.end());
    }
    else
    {
      assumps.push_back(exp);
    }
    conc = lem[1];
    cdp.addStep(lem, ProofRule::SCOPE, {conc}, assumps);
  }
  TheoryProofStepBuffer psb(cdp.getManager()->getChecker(), true);
  bool success = convert(psb, id, assumps, conc);
  if (success && !cdp.addSteps(psb))
  {
    // should not fail if success was computed correctly by convert
    DebugUnhandled();
    success = false;
  }
  if (!success)
  {
    Trace("bags-ipc") << "...trust " << id << std::endl;
    cdp.addTrustedStep(conc, TrustId::THEORY_INFERENCE_BAGS, assumps, {});
  }
  return cdp.getProofFor(lem);
}

bool InferProofCons::convert(TheoryProofStepBuffer& psb,
                             InferenceId id,
                             const std::vector<Node>& assumps,
                             const Node& conc)
{
  Trace("bags-ipc") << "InferProofCons::convert " << id << std::endl;
  Trace("bags-ipc") << "- assumptions: " << assumps << std::endl;
  Trace("bags-ipc") << "- conclusion:  " << conc << std::endl;
  bool success = false;
  switch (id)
  {
    case InferenceId::BAGS_NON_NEGATIVE_COUNT:
    {
      // (>= (bag.count e A) 0)
      if (assumps.empty() && conc.getKind() == Kind::GEQ
          && conc[0].getKind() == Kind::BAG_COUNT)
      {
        Node res = psb.tryStep(ProofRule::BAGS_COUNT_NON_NEG, {}, {conc[0]});
        success = CDProof::isSame(res, conc);
      }
    }
    break;
    case InferenceId::BAGS_EMPTY:
    case InferenceId::BAGS_BAG_MAKE:
    case InferenceId::BAGS_UNION_DISJOINT:
    case InferenceId::BAGS_UNION_MAX:
    case InferenceId::BAGS_INTERSECTION_MIN:
    case InferenceId::BAGS_DIFFERENCE_SUBTRACT:
    case InferenceId::BAGS_DIFFERENCE_REMOVE:
    case InferenceId::BAGS_SETOF:
    {
      // The conclusion is (= (bag.count e k) r) where k is the purification
      // skolem of a bag term t. We prove (= (bag.count e t) r) by
      // BAGS_COUNT_DEF, and then replace t by k.
      if (!assumps.empty() || conc.getKind() != Kind::EQUAL
          || conc[0].getKind() != Kind::BAG_COUNT)
      {
        break;
      }
      Node count = getUnpurifiedCount(conc[0]);
      Node res = psb.tryStep(ProofRule::BAGS_COUNT_DEF, {}, {count});
      if (res.isNull())
      {
        break;
      }
      success = transformToSkolemForm(psb, res, conc);
    }
    break;
    case InferenceId::BAGS_FILTER_UP:
    {
      // (=> (>= (bag.count e A) 1)
      //     (or (and (P e) (= (bag.count e k) (bag.count e A)))
      //         (and (not (P e)) (= (bag.count e k) 0))))
      // where k is the purification skolem of (bag.filter P A). The premise
      // is not needed.
      if (conc.getKind() != Kind::OR || conc[0].getKind() != Kind::AND
          || conc[0].getNumChildren() != 2
          || conc[0][1].getKind() != Kind::EQUAL
          || conc[0][1][0].getKind() != Kind::BAG_COUNT)
      {
        break;
      }
      Node count = getUnpurifiedCount(conc[0][1][0]);
      Node res = psb.tryStep(ProofRule::BAGS_FILTER_UP, {}, {count});
      if (!res.isNull())
      {
        success = transformToSkolemForm(psb, res, conc);
      }
    }
    break;
    case InferenceId::BAGS_FILTER_DOWN:
    {
      // (=> (>= (bag.count e k) 1)
      //     (and (P e) (= (bag.count e k) (bag.count e A))))
      // where k is the purification skolem of (bag.filter P A).
      if (assumps.size() != 1 || assumps[0].getKind() != Kind::GEQ
          || assumps[0][0].getKind() != Kind::BAG_COUNT)
      {
        break;
      }
      Node count = getUnpurifiedCount(assumps[0][0]);
      Node mem = nodeManager()->mkNode(Kind::GEQ, count, assumps[0][1]);
      if (!transformToSkolemForm(psb, assumps[0], mem))
      {
        break;
      }
      Node res = psb.tryStep(ProofRule::BAGS_FILTER_DOWN, {mem}, {});
      if (!res.isNull())
      {
        success = transformToSkolemForm(psb, res, conc);
      }
    }
    break;
    case InferenceId::BAGS_MAP_UP1:
    {
      // (<= (bag.count x A) (bag.count (f x) k))
      // where k is the purification skolem of (bag.map f A).
      if (!assumps.empty() || conc.getKind() != Kind::LEQ
          || conc[1].getKind() != Kind::BAG_COUNT
          || conc[0].getKind() != Kind::BAG_COUNT)
      {
        break;
      }
      Node t = SkolemManager::getUnpurifiedForm(conc[1][1]);
      if (t.getKind() != Kind::BAG_MAP)
      {
        break;
      }
      Node res = psb.tryStep(ProofRule::BAGS_MAP_UP, {}, {t, conc[0][0]});
      if (!res.isNull())
      {
        success = transformToSkolemForm(psb, res, conc);
      }
    }
    break;
    case InferenceId::BAGS_BAG_MAKE_SPLIT:
    {
      // (or (and (not (>= c 1)) (= t bag.empty))
      //     (and (>= c 1) (not (= t bag.empty))))
      // where t is (bag x c)
      if (assumps.empty() && conc.getKind() == Kind::OR
          && conc.getNumChildren() == 2 && conc[0].getKind() == Kind::AND
          && conc[0].getNumChildren() == 2
          && conc[0][1].getKind() == Kind::EQUAL)
      {
        Node t = conc[0][1][0];
        Node res = psb.tryStep(ProofRule::BAGS_MAKE_SPLIT, {}, {t});
        success = CDProof::isSame(res, conc);
      }
    }
    break;
    case InferenceId::BAGS_DISEQUALITY:
    {
      // (not (= A B)) => (not (= (bag.count k A) (bag.count k B)))
      if (assumps.size() == 1)
      {
        Node res = psb.tryStep(ProofRule::BAGS_EXT, {assumps[0]}, {});
        success = CDProof::isSame(res, conc);
      }
    }
    break;
    case InferenceId::BAGS_SKOLEM:
    {
      // (= t k) where k is the purification skolem of t, which holds by
      // replacing k by t.
      if (assumps.empty())
      {
        success = psb.applyPredIntro(conc, {});
      }
    }
    break;
    case InferenceId::BAGS_CG_SPLIT:
    {
      // (or (= x y) (not (= x y)))
      if (assumps.empty() && conc.getKind() == Kind::OR
          && conc.getNumChildren() == 2)
      {
        Node res = psb.tryStep(ProofRule::SPLIT, {}, {conc[0]});
        success = CDProof::isSame(res, conc);
      }
    }
    break;
    default: Trace("bags-ipc") << "Unhandled " << id << std::endl; break;
  }
  // all of the handled inferences above are expected to succeed
  Assert(!success || psb.getNumSteps() > 0);
  Trace("bags-ipc") << "...success = " << success << std::endl;
  return success;
}

Node InferProofCons::getUnpurifiedCount(const Node& count)
{
  Assert(count.getKind() == Kind::BAG_COUNT);
  Node t = SkolemManager::getUnpurifiedForm(count[1]);
  return nodeManager()->mkNode(Kind::BAG_COUNT, count[0], t);
}

bool InferProofCons::transformToSkolemForm(TheoryProofStepBuffer& psb,
                                           const Node& src,
                                           const Node& conc)
{
  if (CDProof::isSame(src, conc))
  {
    return true;
  }
  // The two formulas have the same original form, so we do not need to rewrite
  // them, which we indicate with MethodId::RW_IDENTITY.NTITY.
  return psb.applyPredTransform(src,
                                conc,
                                {},
                                MethodId::SB_DEFAULT,
                                MethodId::SBA_SEQUENTIAL,
                                MethodId::RW_IDENTITY);
}

std::string InferProofCons::identify() const { return "bags::InferProofCons"; }

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
