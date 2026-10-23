# Results for the branch sets-to-bags-liastar

This branch only holds the data and figures of the experiments described in the pull request that merges [`sets-to-bags-liastar`](https://github.com/mudathirmahgoub/cvc5/tree/sets-to-bags-liastar) into `main`. It has no history in common with cvc5.

- `final/`: the final experiment on the 240 BAPA benchmarks of the LIA* paper artifact (sls-reachability), with cvc5 at commit `9fd0ccffd` and sls-reachability.
  - `results.csv`: answers and times per benchmark.
  - `summary.csv`: the table.
  - `cactus.png`, `cactus.pdf`: the cactus plots.
  - `run_experiments.py`, `report.py`: the scripts. They expect to be in `results/<name>/` of an sls-reachability checkout, whose `benchmarks/bapa` they read.
- `exp1-stock-bags/results.csv`: the first run, with a debug build of `sets-to-bags` and the stock bags solver. It has answers only.
- `exp2-all-configurations/results.csv`: the second run, with cvc5 at commit `a28b35f20`. It includes the hand-written bag versions of the benchmarks. Its times include about 0.04 s of Python startup per run.
- `examples/`: small hand-written examples, and their answers with the final binary in `results.tsv`.
