export const meta = {
  name: 'review-liastar-pushpop',
  description: 'Review the subsolver push/pop refactor diff across three lenses, then adversarially verify findings',
  phases: [
    { title: 'Review', detail: 'three independent lenses on the diff' },
    { title: 'Verify', detail: 'adversarial check of each finding' },
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
          file: { type: 'string' },
          detail: { type: 'string' },
          severity: { type: 'string', enum: ['critical', 'major', 'minor'] },
        },
        required: ['title', 'file', 'detail', 'severity'],
      },
    },
  },
  required: ['findings'],
}

const VERDICT_SCHEMA = {
  type: 'object',
  properties: {
    isReal: { type: 'boolean' },
    reasoning: { type: 'string' },
  },
  required: ['isReal', 'reasoning'],
}

const CONTEXT = `Repo: /home/mudathir/all/cvc5/mudathir (cvc5 SMT solver, branch "lazy").
The working tree has an uncommitted change: run "git diff" in that directory to see it.
The change refactors LiaStarExtension's lazy refinement loop: previously each refinement
round called sub.engine->assertFormula(notD_i) for each newly discovered cone-disjunct,
accumulating assertions forever in the incremental subsolver. Now the code keeps one
cumulative disjunction sub.covered of all discovered disjuncts (in skolem space) and each
round (only when new disjuncts arrived) does: if (sub.pushed) engine->pop(); engine->push();
engine->assertFormula(sub.covered.notNode()); sub.pushed = true.
The base predicate is asserted once at user level 0 in getSubsolver() before any push.
Rationale: each round's refined formula not(D_1 or ... or D_k) implies the previous round's,
so popping the old one loses nothing, and the subsolver holds exactly 2 live assertions,
keeping per-assertion caches bounded.
Key files: src/theory/arith/liastar/liastar_extension.{h,cpp} (see lazyCheckStar, getSubsolver,
lazyHilbert), src/theory/arith/liastar/liastar_utils.cpp (getDisjunct does checkSat+getValue),
src/smt/solver_engine.{h,cpp} (push/pop semantics).`

const LENSES = [
  {
    key: 'solver-api-semantics',
    prompt: `${CONTEXT}

Lens: cvc5 SolverEngine API semantics. Read the diff and the surrounding code, and read
src/smt/solver_engine.cpp push()/pop()/assertFormula()/checkSat() implementations. Look for:
- Is pop() legal/safe in this call sequence (pop after a checkSat, push before assert)?
- Does pop() require incremental mode and is it guaranteed on? Can pop() throw here?
- Are Nodes held across pop (sub.covered, sub.base, sub.to skolems) safe, or is anything
  user-context-dependent invalidated?
- Does asserting at level 0 before the first push really survive later pops?
- Any issue with getValue/model reads relative to the push/pop timing in getDisjunct?
Report only real problems with the new code (not pre-existing issues), as findings.`,
  },
  {
    key: 'logic-correctness',
    prompt: `${CONTEXT}

Lens: logical correctness of the refinement. Read the diff and lazyCheckStar/lazyHilbert/
getDisjunct/addCone/getStarConstraints carefully. Look for:
- Is the cumulative sub.covered exactly equivalent to the conjunction of the previously
  asserted negated disjuncts? (substitution to skolem space, empty-from case, OR nesting)
- Off-by-one or staleness in sub.negated vs d_lazyCones (note addCone drops empty cones --
  does that desync anything? could the same disjunct be rediscovered forever?)
- The skip case: when no new disjuncts arrived since last round, the code does not
  pop/push/re-assert. Is the subsolver state then still what lazyHilbert expects?
- Multiple STAR_CONTAINS literals sharing one lambda; multiple check-sat commands
  (incremental main solver); interaction with d_processedStarTerms.
Report only real problems introduced by the new code, as findings.`,
  },
  {
    key: 'edge-cases-lifecycle',
    prompt: `${CONTEXT}

Lens: lifecycle and edge cases. Read the diff and the whole liastar_extension.{h,cpp}. Look for:
- First round (no disjuncts yet): checkSat on base alone -- consistent with old behavior?
- Round where getDisjunct returns false (complete): literal marked processed; any dangling
  pushed frame problem at destruction (~LiaStarExtension, SolverEngine destructor with
  unpopped user levels)?
- Exceptions: if assertFormula or push throws mid-sequence, is state (sub.pushed flag)
  consistent?
- Could sub.covered grow as a deeply left-nested OR and hit any recursion limit in
  substitution/rewriting/preprocessing?
- Proof mode (d_proofGen) and the trace channels: anything in the new path that breaks them?
Report only real problems introduced by the new code, as findings.`,
  },
]

const results = await pipeline(
  LENSES,
  l => agent(l.prompt, { label: `review:${l.key}`, phase: 'Review', schema: FINDINGS_SCHEMA }),
  (review, lens) => parallel((review?.findings ?? []).map(f => () =>
    agent(`${CONTEXT}

A code reviewer (lens: ${lens.key}) claims the following problem in the uncommitted diff:
Title: ${f.title}
File: ${f.file}
Detail: ${f.detail}

Adversarially verify this against the actual code. Read the relevant files. Decide whether this
is a REAL problem introduced by the new code (not pre-existing, not hypothetical-but-impossible).
Default to isReal=false if you cannot reproduce the reasoning concretely from the code.`,
      { label: `verify:${f.title.slice(0, 30)}`, phase: 'Verify', schema: VERDICT_SCHEMA })
      .then(v => ({ ...f, lens: lens.key, verdict: v }))
  ))
)

const all = results.filter(Boolean).flat().filter(Boolean)
const confirmed = all.filter(f => f.verdict?.isReal)
const rejected = all.filter(f => !f.verdict?.isReal).map(f => f.title)
log(`${all.length} raw findings, ${confirmed.length} confirmed`)
return { confirmed, rejected }