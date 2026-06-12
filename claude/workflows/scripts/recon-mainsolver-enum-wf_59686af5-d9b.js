export const meta = {
  name: 'recon-mainsolver-enum',
  description: 'Gather cvc5 API facts needed to move LIA* lazy cell enumeration into the main solver',
  phases: [{ title: 'Recon', detail: 'parallel readers over valuation, inference manager, inference ids, proof gen, model construction' }],
}

const FACTS = {
  type: 'object',
  properties: {
    facts: { type: 'array', items: { type: 'string' } },
    signatures: { type: 'array', items: { type: 'string' } },
    caveats: { type: 'array', items: { type: 'string' } },
  },
  required: ['facts', 'signatures', 'caveats'],
}

const CTX = `Repo: /home/mudathir/all/cvc5/mudathir (cvc5 SMT solver, branch lazy).
Goal: in src/theory/arith/liastar/liastar_extension.cpp, replace the per-lambda incremental
subsolver with enumeration in the MAIN solver: fresh integer skolems y for the lambda's bound
variables, a boolean guard skolem h (decision variable, phase-preferred true), lemmas
h => base(y) and h => not(D_i(y)) sent via TheoryArith's InferenceManager, the next cell read
from the main solver's candidate arithmetic model, and completeness detected when h is forced
false at decision level 0. Answer the specific questions for your assigned area with exact
signatures and file:line references. Return raw facts, not prose essays.`

const TASKS = [
  {
    key: 'valuation',
    prompt: `${CTX}
Area: src/theory/valuation.h (+ .cpp). Questions:
1. Exact signatures of: ensureLiteral, isSatLiteral, hasSatValue, isDecision, getDecisionLevel,
   and ANY method that tells whether a literal is FIXED/entailed at decision level 0 (isFixed?).
   For getDecisionLevel: what does it return for unassigned literals / non-SAT literals? Safe call order?
2. Is there a getModelValue / getCandidateModelValue on Valuation usable at LAST_CALL effort from a
   theory extension? Signature and constraints.
3. How does the existing liastar code use Valuation (search liastar_extension.cpp for getValuation)?`,
  },
  {
    key: 'inference-manager',
    prompt: `${CTX}
Area: src/theory/arith/inference_manager.h, src/theory/theory_inference_manager.h,
src/theory/inference_manager_buffered.h, src/theory/output_channel.h. Questions:
1. Signatures of preferPhase and requirePhase (if it exists) reachable from arith's InferenceManager.
2. addPendingLemma signature(s): what happens when the ProofGenerator* is nullptr while the env is
   proof-producing — is that legal (trusted THEORY_LEMMA) or an assertion failure? Cite code.
3. Lemma caching: if the same lemma node is added twice (addPendingLemma + doPendingLemmas), is the
   duplicate dropped? Where (hasCachedLemma / d_lemmasSent)? Does hasSentLemma() reflect only newly
   sent ones this round?
4. Anything about LemmaProperty (e.g. PREPROCESS, SEND_ATOMS) the liastar code should consider when
   sending lemmas containing brand-new skolems/atoms.`,
  },
  {
    key: 'inference-ids',
    prompt: `${CTX}
Area: src/theory/inference_id.h and inference_id.cpp. Questions:
1. List the existing ARITH_LIA_STAR_* enum values with exact lines in both files.
2. Show exactly what must be added to introduce a new id ARITH_LIA_STAR_ENUM (enum entry placement
   and the switch/case or name table entry in the .cpp).`,
  },
  {
    key: 'proof-generator',
    prompt: `${CTX}
Area: src/theory/arith/liastar/liastar_proof_generator.{h,cpp}. Questions:
1. List all register* methods with signatures and which proof rule each produces.
2. What happens if a lemma is sent with this generator but was never registered (getProofFor behavior)?
3. Is there a generic trust/assume fallback suitable for new lemma kinds (h => base(y), h => not(D(y))),
   or is passing nullptr as the generator the safer route when proofs are enabled?`,
  },
  {
    key: 'arith-model',
    prompt: `${CTX}
Area: how the arithModel passed to LiaStarExtension::checkFullEffort is built. Trace the caller chain:
src/theory/arith/theory_arith.cpp (search for checkFullEffort / liastar), nonlinear_extension.cpp if
relevant, and where the model map comes from (linear solver collectModelValues?). Questions:
1. Does the map contain values for ALL arithmetic variables known to the linear solver, including fresh
   skolems that appear only in theory lemmas (not in user assertions)? Under what conditions can a
   variable be MISSING from that map (eliminated by substitution, not in termSet, etc.)?
2. Are the mapped values always constants (Rational)?
3. How does the existing model-value shortcut in checkFullEffort substitute and rewrite to evaluate
   formulas under this model -- can the same substitute+rewrite evaluate an arbitrary QF_LIA atom over
   the skolems to a boolean constant reliably?`,
  },
]

const results = await parallel(TASKS.map(t => () =>
  agent(t.prompt, { label: `recon:${t.key}`, phase: 'Recon', schema: FACTS })
    .then(r => ({ key: t.key, ...r }))))
return results.filter(Boolean)