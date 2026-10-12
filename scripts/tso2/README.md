# tso-2-th and tso-2-th-just-rf (temporary)

Work on the two benchmarks that rachelcleaveland/relational-solver-benchmarks added in
`ad1980d` (2 threads, X86-TSO). Delete this directory before merging into cvc5 main.

| file | content |
|---|---|
| `PROOF.md` | hand proof that both benchmarks are unsat |
| `CVC5-NOTES.md` | why cvc5 times out on them, the prototype options of this branch, all measurements |
| `split/` | the benchmarks split by violated condition, minimal versions, explicit cycles |
| `pretty.py` | prints the definitions and templates of a benchmark in relational notation |
| `minimize.py` | keeps only given templates (e.g. the ones the proof uses) and replaces the goal |
| `run15.py` | runs every file of `benchmarks-ltts` with one configuration |
| `DECOMPOSITION.md` | tso-2-th is unsat by bounded cvc5 queries: the lemma, the queries, the results |
| `decompose.py` | writes and runs those queries for any relation and bound |

## The configuration that solves tso-2-th-just-rf

```sh
cvc5 --rels-acyclic-anchor=inclusion --inst-when=full-delay --rels-acyclic-backward-chords \
     --prenex-quant=none --rels-tc-subset --rels-tc-down-lazy \
     --rels-cycle-keep-prefix --rels-cycle-len-decide --rels-cycle-unroll-guard \
     --rels-cycle-flatten-keep-tc --rels-product-lazy --rels-product-lazy-compose \
     --rels-tc-up-skip-known --rels-tc-subset-split \
     benchmarks-ltts/tso-2-th-just-rf.smt2      # unsat, about 3 s
```

The first line is `nofmf-unsat-rules` of the portfolio; the other options are the prototype
options of this branch and of rachelcleaveland/cvc5#11, all off by default. On the 15 files of
`benchmarks-ltts` this configuration solves 10 of the 12 unsat files (`tso-2-th-just-rf` in 3 s,
`plsc-2-th` in 11 s instead of 53-79 s); it does not solve `sc-2-th` (the hammer configuration
does, in 4 s), `tso-2-th`, or the satisfiable `no-ltts` files (finite model finding does).

## Reproducing the split files

```sh
python3 scripts/tso2/pretty.py benchmarks-ltts/tso-2-th.smt2            # definitions and templates
python3 scripts/tso2/minimize.py benchmarks-ltts/tso-2-th.smt2 "(rel.cyclic ghb)" out.smt2 \
    "$(python3 -c 'print("|".join(...))')"                              # see CVC5-NOTES.md
python3 scripts/tso2/run15.py build/bin/cvc5 300 5 "<options>"           # from the benchmark repo root
```
