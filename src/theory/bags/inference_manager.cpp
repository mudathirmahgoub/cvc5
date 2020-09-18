/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the inference manager for the theory of bags
 **/

#include "theory/bags/inference_manager.h"

#include "options/sets_options.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

InferenceManager::InferenceManager(Theory& t,
                                   SolverState& s,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(t, s, pnm), d_state(s)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool InferenceManager::assertFactRec(Node fact, Node exp, int inferType)
{
  Assert(false)<<"Not implemented yet"<<std::endl;
}
void InferenceManager::assertInference(Node fact,
                                       Node exp,
                                       const char* c,
                                       int inferType)
{
  if (assertFactRec(fact, exp, inferType))
  {
    Trace("bags-lemma") << "Bags::Lemma : " << fact << " from " << exp << " by "
                        << c << std::endl;
    Trace("bags-assertion")
        << "(assert (=> " << exp << " " << fact << ")) ; by " << c << std::endl;
  }
}

void InferenceManager::assertInference(Node fact,
                                       std::vector<Node>& exp,
                                       const char* c,
                                       int inferType)
{
  Node exp_n = exp.empty() ? d_true
                           : (exp.size() == 1
                                  ? exp[0]
                                  : NodeManager::currentNM()->mkNode(AND, exp));
  assertInference(fact, exp_n, c, inferType);
}

void InferenceManager::assertInference(std::vector<Node>& conc,
                                       Node exp,
                                       const char* c,
                                       int inferType)
{
  if (!conc.empty())
  {
    Node fact = conc.size() == 1 ? conc[0]
                                 : NodeManager::currentNM()->mkNode(AND, conc);
    assertInference(fact, exp, c, inferType);
  }
}
void InferenceManager::assertInference(std::vector<Node>& conc,
                                       std::vector<Node>& exp,
                                       const char* c,
                                       int inferType)
{
  Node exp_n = exp.empty() ? d_true
                           : (exp.size() == 1
                                  ? exp[0]
                                  : NodeManager::currentNM()->mkNode(AND, exp));
  assertInference(conc, exp_n, c, inferType);
}

void InferenceManager::split(Node n, int reqPol)
{
  n = Rewriter::rewrite(n);
  Node lem = NodeManager::currentNM()->mkNode(OR, n, n.negate());
  // send the lemma
  lemma(lem);
  Trace("bags-lemma") << "Bags::Lemma split : " << lem << std::endl;
  if (reqPol != 0)
  {
    Trace("bags-lemma") << "Bags::Require phase " << n << " " << (reqPol > 0)
                        << std::endl;
    requirePhase(n, reqPol > 0);
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
