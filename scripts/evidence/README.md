# Evidence for every rule of the calculus (temporary)

Which rule each solved benchmark needs, in which configuration, with a real lemma of the rule
from that benchmark. Delete this directory before merging into cvc5 main.

| file | what it does |
|---|---|
| `rule-ids.patch` | applied to this branch: finer inference ids (one per rule: Alternate, Alt-Close, Chord, Distinct, Backward, Inclusion, Branch, Register, Same-Operands, the five kinds of closure induction, the last-call completion, the lazy TC-Down) and the debug option `--rels-evidence-disable=IDS`, which drops the lemmas of the given rules |
| `measure.py` | from a virtual portfolio's `runs.json`, reruns every solved (benchmark, configuration) pair with `--stats-internal -o lemmas` (usage: lemmas per rule, an example per rule), then reruns it once per rule that fired, and once per group of rules that can replace one another, with that rule disabled (ablation); time limit max(60 s, 5 x the original time), `--check-models` on satisfiable benchmarks |
| `examples.py` | picks for every rule a representative lemma from a benchmark where the rule is needed |
| `make_tables.py` | the slides' tables (`scripts/slides/figures/evidence-*.tex`) and `REPORT.md` |

The results are in `scripts/slides/data/evidence/` (`usage.json`, `ablation.json`,
`examples.json`, `REPORT.md`): the 42 solved pairs of the portfolio run `final-300s`,
763 ablation runs.

```sh
git apply scripts/evidence/rule-ids.patch && (cd build && make)      # a separate build
python3 scripts/evidence/measure.py build/bin/cvc5 results/final-300s/virtual/runs.json out 4
python3 scripts/evidence/examples.py build/bin/cvc5 out
python3 scripts/evidence/make_tables.py out scripts/slides/figures
```
