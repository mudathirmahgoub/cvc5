export const meta = {
  name: 'review-mainsolver-enum',
  description: 'Adversarially review the main-solver LIA* enumeration implementation',
  phases: [
    { title: 'Review', detail: 'three lenses: soundness, termination/progress, mechanics' },
    { title: 'Verify', detail: 'adversarial verification of findings' },
  ],
}

const FINDINGS_SCHEMA = {
  type: 'object',
  properties: {
    findings: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          title: { type: 'string' },
          detail: { type: 'string' },
          severity: { type: 'string', enum: ['critical', 'major', 'minor'] },
        },
        required: ['title', 'detail', 'severity'],
      },
    },
  },
  required: ['findings'],
}

const VERDICT_SCHEMA = {
  type: 'object',
  properties: { isReal: { type: 'boolean' }, reasoning: { type: 'string' } },
  required: ['isReal', 'reasoning'],
}

const CTX = `Repo: /home/mudathir/all/cvc5/mudathir (cvc5, branch lazy). Uncommitted changes: run
"git diff" there. New feature: option arith-liastar-main-solver moves the lazy LIA* cell
enumeration from a per-lambda subsolver into the MAIN solver. Design (see MainEnum in
src/theory/arith/liastar/liastar_extension.h and mainSolverCheckStar/advanceStage/
emitDriverLemma/getModelDisjunct/getMainEnum/addEnumLemma in liastar_extension.cpp):
- lambda bound vars -> fresh integer skolems y; base(y) = predicate (ites/nots removed) + y>=0.
- Stage guards: h_0 => base(y); per discovered cone-disjunct D_k a fresh h_k with
  h_k => h_{k-1} and h_k => not(D_k(y)); en.guard is the current h_k; each h is
  ensureLiteral'd and preferPhase'd true. h_0 additionally gets a split lemma.
- Driver lemma per (literal, stage): literal => (p[v] or star_k or h_k), unguarded,
  where star_k = d_lastStarLia[literal] (under-approximation built by processDisjunct)
  and p[v] is the vector predicate. Claimed satisfiability-preserving.
- Each full-effort round: catch up stages for cones discovered via other literals; if
  guard fixed false at level 0 (Valuation::isFixed) -> emit exact equivalence
  (processDisjunct complete=true); if guard true in SAT assignment -> read the cell from
  arithModel via getModelDisjunct (substitute+rewrite each atom of base; equality atoms
  false in model become strict inequalities; skolems missing from arithModel fall back to
  TheoryArith::getCandidateModelValue), dedupe against d_lazyCones, advanceStage, then
  processDisjunct(false) emits the guarded equivalence g_k => (literal = star_k) and
  deactivates the previous g; then emitDriverLemma for the new stage.
- Tests: all 9 regress1/arith/liastar tests pass in this mode (Debug), and in the other
  three modes (accumulate/push-pop/eager); unit test passes.
Focus ONLY on problems introduced by the new main-solver mode (not pre-existing issues in
the subsolver paths). Report findings with concrete code references.`

const LENSES = [
  {
    key: 'soundness',
    prompt: `${CTX}
Lens: logical soundness. Questions to attack:
1. Is the driver lemma literal => (p[v] or star_k or h_k) really satisfiability-preserving in
   ALL cases -- including stale drivers from earlier stages (each stage's driver stays asserted
   forever, with its own h_j whose constraint set is frozen at stage j)? Construct a
   countermodel if possible.
2. Is the completeness conclusion from Valuation::isFixed(guard)=false sound? isFixed means
   implied by input assertions -- but the implication chain includes liastar's own lemmas
   (drivers, guarded equivalences, star constraints). Could not(h_k) be fixed for a reason
   OTHER than base-and-negated-disjuncts being unsat (e.g. via the driver and a fixed
   not(literal)), making the exact equivalence emission wrong?
3. getModelDisjunct: the disjunct fixes every atom of base; equality-false becomes GT/LT.
   Any way it returns a conjunction NOT implying base (so the cone overcovers) or one not
   containing the model point?
4. Interaction of d_lastStarLia / d_lastGuard between modes or multiple literals sharing a
   lambda: cross-contamination?`,
  },
  {
    key: 'termination-progress',
    prompt: `${CTX}
Lens: termination and progress. Questions to attack:
1. Can the procedure livelock: rounds where guard is false-but-not-fixed and the driver for the
   current stage was already emitted -- emitDriverLemma returns without queueing anything and
   doPendingLemmas sends nothing. Is there a scenario where the solver then answers sat with an
   unjustified positively-asserted literal, or loops forever without progress?
2. Duplicate-cell handling: when the model re-exhibits a known cell, the round emits at most a
   driver. Can this repeat indefinitely (same cell each round)? Note the stage that negates the
   cell was opened in the round that first harvested it -- is en.negated maintained consistently
   with d_lazyCones in ALL paths (addCone drops empty cones!)?
3. advanceStage in the catch-up loop vs processDisjunct ordering: en.negated = pairs.size() is
   executed twice in the harvest path (before/after processDisjunct). Off-by-one risks?
4. incremental mode (push/pop of the main solver between check-sats): lemmas/d_mainEnums/
   d_lastDriver are non-context state; what breaks (e.g. simple.smt2 has two check-sats)?`,
  },
  {
    key: 'mechanics',
    prompt: `${CTX}
Lens: cvc5 mechanics. Questions to attack:
1. ensureLiteral + preferPhase during a full-effort check: legal at that point? (compare the
   existing liastarGuard pattern). Any issue calling them per stage (many stages)?
2. addEnumLemma skips lemmas that rewrite to constants -- could skipping h_k => not(D_k) (if it
   ever rewrites to true) silently break the stage invariant?
3. getModelDisjunct's use of arithModel keys: substitution with non-leaf keys (the arith model
   map can contain non-variable terms); is substitute() over atom nodes safe/correct here?
4. TheoryArith::getCandidateModelValue fallback: legal for skolems unknown to the linear solver?
5. Lemma flushing: every path in mainSolverCheckStar ends in doPendingLemmas or processDisjunct
   (which calls it) -- verify, including the early-return paths in checkFullEffort around the
   model-value shortcut.
6. The unused 'seeded' warning, unused includes, style of the new code vs file conventions.`,
  },
]

const results = await pipeline(
  LENSES,
  l => agent(l.prompt, { label: `review:${l.key}`, phase: 'Review', schema: FINDINGS_SCHEMA }),
  (review, lens) => parallel((review?.findings ?? []).map(f => () =>
    agent(`${CTX}
A reviewer (lens ${lens.key}) claims:
Title: ${f.title}
Detail: ${f.detail}
Adversarially verify against the actual code (git diff + files). Is this a REAL problem
introduced by the new main-solver mode? Default isReal=false unless the reasoning reproduces
concretely from the code.`,
      { label: `verify:${f.title.slice(0, 30)}`, phase: 'Verify', schema: VERDICT_SCHEMA })
      .then(v => ({ ...f, lens: lens.key, verdict: v }))
  ))
)

const all = results.filter(Boolean).flat().filter(Boolean)
return {
  confirmed: all.filter(f => f.verdict?.isReal),
  rejected: all.filter(f => !f.verdict?.isReal).map(f => f.title),
}