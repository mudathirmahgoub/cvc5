/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for the liastar extension.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__LIASTAR__LIASTAR_STATS_H
#define CVC5__THEORY__ARITH__LIASTAR__LIASTAR_STATS_H

#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

/**
 * Statistics for the liastar extension. All statistics are registered under
 * the prefix theory::arith::liastar:: and are printed when cvc5 is run with
 * --stats-internal.
 *
 * Note that timers may overlap: e.g. d_toDnfTime includes d_removeItesTime,
 * d_removeNotTime and d_distributeTime, and d_distributeTime includes the
 * subsolver time spent pruning unsat disjuncts (d_subSolverTime).
 */
class LiaStarStatistics
{
 public:
  LiaStarStatistics(StatisticsRegistry& sr);

  //------------------------- timers
  /** Total time spent in LiaStarExtension::checkFullEffort. */
  TimerStat d_checkFullEffortTime;
  /** Time spent evaluating star literals in the candidate model. */
  TimerStat d_modelValueTime;
  /**
   * Total time spent converting predicates to DNF, i.e. in
   * LiaStarUtils::toDNF. This includes ITE removal, NNF conversion,
   * distribution and any subsolver calls made while pruning disjuncts.
   */
  TimerStat d_toDnfTime;
  /** Time spent removing ITE expressions (LiaStarUtils::removeItes). */
  TimerStat d_removeItesTime;
  /** Time spent converting to NNF (LiaStarUtils::removeNot). */
  TimerStat d_removeNotTime;
  /**
   * Time spent distributing conjunctions over disjunctions
   * (LiaStarUtils::distribute). Includes subsolver time for pruning unsat
   * disjuncts when arith-lia-star-sub-solver is enabled.
   */
  TimerStat d_distributeTime;
  /**
   * Time spent converting DNF disjuncts to integer constraint matrices
   * (LiaStarUtils::getMatrices, LinearConstraints).
   */
  TimerStat d_getMatricesTime;
  /**
   * Time spent computing module generators and Hilbert bases
   * (IntegerPolyhedron). This is the total across the main reduction and
   * hilbert-basis-as-subsolver calls.
   */
  TimerStat d_hilbertBasisTime;
  /** Total time spent in LiaStarExtension::getCones. */
  TimerStat d_getConesTime;
  /** Total time spent in LiaStarExtension::getLia. */
  TimerStat d_getLiaTime;
  /**
   * Total time spent in subsolver calls checking satisfiability of
   * disjuncts (LiaStarUtils::areAssertionsUnsat).
   */
  TimerStat d_subSolverTime;
  /** Time spent in cvc5 subsolver calls (LiaStarUtils::cvc5CheckSat). */
  TimerStat d_cvc5SubSolverTime;
  /**
   * Time spent in hilbert-basis-as-subsolver calls
   * (LiaStarUtils::hilbertBasisCheckSat).
   */
  TimerStat d_hilbertBasisSubSolverTime;

  //------------------------- counters
  /** Number of calls to LiaStarExtension::checkFullEffort. */
  IntStat d_checkRuns;
  /**
   * Total number of star-contains literals collected over all checks. A
   * literal is counted once per check run, even if the run returns early
   * before examining it.
   */
  IntStat d_starContainsLiterals;
  /** Number of times a star literal was evaluated in the candidate model. */
  IntStat d_modelValueChecks;
  /**
   * Number of times model evaluation was enough to satisfy a star literal,
   * i.e. the check finished without sending a reduction lemma.
   */
  IntStat d_modelValueSolved;
  /** Number of star literals reduced with a star reduction lemma. */
  IntStat d_starTermsReduced;
  /**
   * Number of ITE eliminations performed during ITE removal. An ITE nested
   * in a condition is duplicated into both branches and hence may be
   * eliminated (and counted) more than once.
   */
  IntStat d_itesRemoved;
  /** Number of predicates converted to DNF. */
  IntStat d_dnfCalls;
  /**
   * Total number of disjuncts over all DNF conversions, as converted by
   * getMatrices. A predicate that is a constant (e.g. false after all
   * disjuncts were pruned) counts as one disjunct.
   */
  IntStat d_dnfDisjuncts;
  /** Maximum number of disjuncts in a single DNF conversion. */
  IntStat d_dnfDisjunctsMax;
  /**
   * Number of disjuncts discarded as unsat by the subsolver during DNF
   * conversion (includes partial conjunctions pruned early).
   */
  IntStat d_disjunctsPrunedUnsat;
  /** Number of subsolver calls (LiaStarUtils::areAssertionsUnsat). */
  IntStat d_subSolverCalls;
  /** Number of subsolver calls that returned sat. */
  IntStat d_subSolverSat;
  /** Number of subsolver calls that returned unsat. */
  IntStat d_subSolverUnsat;
  /** Number of subsolver calls that returned unknown or none. */
  IntStat d_subSolverUnknown;
  /**
   * Number of module generator and Hilbert basis computations
   * (IntegerPolyhedron), in the main reduction and the subsolver.
   */
  IntStat d_hilbertBasisCalls;
  /**
   * Total number of sums of candidates formed by the dual algorithm
   * (DualHilbertBasis) over all Hilbert basis computations, a measure of
   * their work.
   */
  IntStat d_hilbertBasisSums;
  /**
   * Number of disjuncts without integer solutions (unsat disjuncts) in the
   * main star reduction (getCones). Disjuncts checked by the
   * hilbert-basis-as-subsolver are not included; those are counted by
   * d_subSolverUnsat.
   */
  IntStat d_conesEmpty;
  /**
   * Number of disjuncts with integer solutions (sat disjuncts) in the main
   * star reduction (getCones). Disjuncts checked by the
   * hilbert-basis-as-subsolver are not included.
   */
  IntStat d_conesNonempty;
  /**
   * Total number of Hilbert basis vectors over all nonempty cones in the
   * main star reduction (getCones), including the basis vectors of the
   * maximal subspace (IntegerPolyhedron::getRecessionMonoidGenerators).
   */
  IntStat d_hilbertBasisTotal;
  /** Maximum number of Hilbert basis vectors in a single cone. */
  IntStat d_hilbertBasisMax;
  /**
   * Total number of module generators over all nonempty cones in the main
   * star reduction (getCones). A cone (a disjunct without constants) has the
   * single module generator 0.
   */
  IntStat d_moduleGeneratorsTotal;
  /** Maximum number of module generators in a single cone. */
  IntStat d_moduleGeneratorsMax;
  /** Maximum dimension of star vectors. */
  IntStat d_dimensionMax;
};

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR__LIASTAR_STATS_H */
