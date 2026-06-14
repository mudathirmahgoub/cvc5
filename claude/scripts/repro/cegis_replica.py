#!/usr/bin/env python3
"""Offline replica of the in-solver cut-synthesis (CEGIS) loop.

This is the diagnostic tool that cracked the last benchmark. When the
in-solver `synthesizeCuts` was failing on the MAPA instance fol_0000107, I
re-implemented the *exact* loop here -- driving a plain cvc5 from Python with
get-value -- so every target / candidate / counterexample was visible. The
replica converged (8 cuts, ~33 candidate-validate iterations) while the
in-solver version did not, which localized the bug: the in-solver code was
seeding the candidate search with the discovered cells' Hilbert-basis RAY
directions as if they were sample points. A ray of a cell whose indicator bit
is pinned (u13=1) has a 0 in that coordinate, so it slips past the
"restricted coordinates are zero" filter while pointing *outside* the
restriction -- and constraining the candidate to be >=0 on it excludes the
one valid conditional cut. This replica uses only genuine predicate POINTS as
samples (module generators + CEGIS counterexamples), which is the fix.

Run:  cegis_replica.py            # reproduces the fol_0000107 refutation
Prints one line per synthesized cut and finally "REFUTED after k cuts".
"""
import subprocess, re, sys

CVC5 = "/home/mudathir/all/cvc5/mudathir/build-prod/bin/cvc5"
BENCH = "/home/mudathir/fmcad26/sls-reachability/card/cvc5_mapa/fol_0000107.smt2"

# the 21 lambda coordinates of this instance, in argument order
VARS = ['u!9','u!10','u!11','u!13','u!14','u!16','u!17','u!19','u!20','u!22',
        'u!23','u!25','u!26','u!27','UNIVERALSET!1!8','f!0!7','a_fy!5!21',
        'a_fx!6!24','b_ga!3!15','a_fz!4!18','b_gb!2!12']
# coordinates the input pins to 0 (comparison indicator bits) -> conditional cut
ZERO = {'u!9','u!13','u!16','u!19','u!22','u!25','u!27'}
# the input's side constraints (the "A formulas"), in v-space
FACTS = """(declare-const t Int)(declare-const n Int)
(assert (= |u!9| 0))(assert (= |u!10| n))(assert (> n 0))(assert (> n (* 3 t)))
(assert (<= |u!11| t))(assert (= |u!13| 0))(assert (>= (* 2 |u!14|) (+ n (* 3 t) 1)))
(assert (= |u!16| 0))(assert (>= (* 2 |u!17|) (+ n (* 3 t) 1)))(assert (= |u!19| 0))
(assert (>= |u!20| (- n t)))(assert (= |u!22| 0))(assert (>= |u!23| (- n t)))
(assert (= |u!25| 0))(assert (>= |u!26| (- n t)))(assert (= |u!27| 0))
""" + '\n'.join(f'(assert (>= |{v}| 0))' for v in VARS)

def predicate_body():
    """Extract the lambda body (the predicate) from the benchmark."""
    src = open(BENCH).read()
    start = src.index('(assert \n  (int.star-contains')
    b = src.index('(and', start); d, i = 0, src.index('(and', start)
    while True:
        if src[i] == '(': d += 1
        elif src[i] == ')': d -= 1
        if d == 0: break
        i += 1
    return src[b:i+1]

BODY = predicate_body()
DECLS = '\n'.join(f'(declare-const |{v}| Int)' for v in VARS)

def run(text):
    open('/tmp/q.smt2', 'w').write(text)
    return subprocess.run([CVC5, '-q', '--produce-models', '/tmp/q.smt2'],
                          capture_output=True, text=True, timeout=120).stdout.strip()

def lit(x): return str(x) if x >= 0 else f'(- {-x})'

def get_values(text, names):
    out = run(text + '\n(get-value (' + ' '.join(names) + '))').splitlines()
    if not out or out[0] != 'sat':
        return (out[0] if out else 'error'), []
    nums = [int(v.replace('(- ', '-').rstrip(')')) if v.startswith('(') else int(v)
            for v in re.findall(r'(\(- \d+\)|\d+)\)', ' '.join(out[1:]))]
    return 'sat', nums

def main():
    samples, cuts = [], []
    for rnd in range(40):
        # TARGET: a vector the input still allows, given the cuts so far
        st, tv = get_values(f'(set-logic QF_LIA)\n{DECLS}\n{FACTS}\n' +
                            '\n'.join(cuts) + '\n(check-sat)', [f'|{v}|' for v in VARS])
        if st == 'unsat':
            print(f'REFUTED after {len(cuts)} cuts'); return 0
        if st != 'sat' or len(tv) != 21:
            print('target query problem:', st); return 1
        # CANDIDATE + VALIDATE: CEGIS for one valid separating cut, escalating budget
        found, total = None, 0
        for K in (4, 9, 16, 30):
            for _ in range(60):
                total += 1
                cdecl = '\n'.join(f'(declare-const c{i} Int)(declare-const a{i} Int)'
                                  f'(assert (>= a{i} c{i}))(assert (>= a{i} (- c{i})))'
                                  for i in range(21))
                l1 = f'(assert (<= (+ {" ".join(f"a{i}" for i in range(21))}) {K}))'
                cons = ['(assert (>= (+ ' + ' '.join(f'(* c{i} {lit(p[i])})' for i in range(21)) + ') 0))'
                        for p in samples]                                # samples are POINTS only (the fix)
                tgt = '(assert (<= (+ ' + ' '.join(f'(* c{i} {lit(tv[i])})' for i in range(21)) + ') (- 1)))'
                st2, cv = get_values(f'(set-logic QF_LIA)\n{cdecl}\n{l1}\n' +
                                     '\n'.join(cons) + f'\n{tgt}\n(check-sat)', [f'c{i}' for i in range(21)])
                if st2 != 'sat':
                    break                                                # no candidate at this budget -> escalate K
                lhs = '(+ ' + ' '.join(f'(* {lit(cv[i])} |{VARS[i]}|)' for i in range(21)) + ')'
                restrict = '\n'.join(f'(assert (= |{v}| 0))' for v in ZERO)
                vq = f'(set-logic QF_LIA)\n{DECLS}\n(assert {BODY})\n{restrict}\n(assert (<= {lhs} (- 1)))\n(check-sat)'
                vst, pt = get_values(vq, [f'|{v}|' for v in VARS])
                if vst == 'unsat':                                       # valid on the restricted predicate
                    found = (cv, lhs); break
                samples.append(pt)                                       # counterexample -> new sample
            if found: break
        if not found:
            print(f'round {rnd}: synthesis FAILED (samples={len(samples)})'); return 1
        cv, lhs = found; cuts.append(f'(assert (>= {lhs} 0))')
        nz = [(VARS[i], cv[i]) for i in range(21) if cv[i]]
        print(f'round {rnd}: cut after {total} CEGIS iters: {nz}', flush=True)
    return 1

if __name__ == '__main__':
    sys.exit(main())
