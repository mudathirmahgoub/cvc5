# Results for the branch sets-to-bags-liastar

This branch only holds the data and figures of the experiment described in the pull request that merges [`sets-to-bags-liastar`](https://github.com/mudathirmahgoub/cvc5/tree/sets-to-bags-liastar) into `main`. It has no history in common with cvc5.

`final/` has the experiment on the 240 BAPA benchmarks of the LIA* paper artifact ([sls-reachability](https://github.com/mudathirmahgoub/sls-reachability)), with cvc5 at commit `e9fd1ca81` and a 50 s limit. These 240 files are the only inputs. They are read as problems over sets (BAPA) and as problems over bags (MAPA), the latter by sls-reachability with `--mapa` and by cvc5 with `--sets-to-bags=relaxed`. The two readings are reported separately. The tables and figures name the configurations cvc5 (sets), cvc5 (bags), cvc5 (LIA\*) and SLS (sls-reachability), and the tables give their options:

- `summary-sets.csv`, `cactus-sets.png`, `cactus-sets.pdf`: the set reading.
- `summary-bags.csv`, `cactus-bags.png`, `cactus-bags.pdf`: the bag reading.
- `results.csv`: answers and times per benchmark and configuration, for both readings.
- `run_experiments.py`, `report.py`: the scripts. They expect to be in `results/<name>/` of an sls-reachability checkout, whose `benchmarks/bapa` they read. Run `run_experiments.py /path/to/cvc5 --timeout 50` with a Python that has z3, then `report.py --timeout 50`.
