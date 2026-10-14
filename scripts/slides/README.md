# Slides for the PR (temporary)

`relations-pr.tex` presents the changes of this branch against cvc5 main: the predicates
`rel.cyclic` and `rel.is-functional`, their rewrite rules, the calculus of inference rules in
the relations solver, the strategy (where each rule runs in the DPLL(T) loop), and the
results on the litmus-template benchmarks. Like the rest of `scripts/`, delete this directory
before merging into cvc5 main.

| file | content |
|---|---|
| `relations-pr.tex`, `relations-pr.pdf` | the deck and its build |
| `make_figures.py` | turns `scripts/portfolio.py` results into the tables and plots in `figures/` |
| `data/final-300s/{virtual,real}/runs.json` | the run the results slides show (release build 45502e064c, 300 s; local paths removed) |
| `figures/` | the fragments the deck `\input`s |

Rebuild (pdflatex, with the TeX Live packages beamer, pgfplots, mathpartir):

```sh
cd scripts/slides
python3 make_figures.py data/final-300s figures
pdflatex relations-pr.tex && pdflatex relations-pr.tex
```

For new results, run `scripts/portfolio.py ... --mode both --results DIR` and pass `DIR` to
`make_figures.py`.
