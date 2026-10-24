# Results for the branch sets-to-bags-liastar

This branch only holds the data and figures of the experiment described in the pull request that merges [`sets-to-bags-liastar`](https://github.com/mudathirmahgoub/cvc5/tree/sets-to-bags-liastar) into `main`. It has no history in common with cvc5.

`final/` has the experiment on the 240 BAPA benchmarks of the LIA* paper artifact ([sls-reachability](https://github.com/mudathirmahgoub/sls-reachability)), with cvc5 at commit `63a1dc4e4` and a 50 s limit:

- `results.csv`: answers and times per benchmark and configuration.
- `summary.csv`: the table.
- `cactus.png`, `cactus.pdf`: the cactus plots.
- `run_experiments.py`, `report.py`: the scripts. They expect to be in `results/<name>/` of an sls-reachability checkout, whose `benchmarks/bapa` they read. Run `run_experiments.py /path/to/cvc5 --timeout 50` with a Python that has z3, then `report.py --timeout 50`.
