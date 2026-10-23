- **The inlined laws' model results, run again (model).** This train rewrites the laws of
  `tests/model/search.py` and `tests/model/hyperbolic.py` within a narrower allow-list,
  which changes the model's harness, and `tests/model/results_check.py` (CI's `model`
  job, since [#378](https://github.com/jackChallis/stoicheia/pull/378)) refuses results
  that name an older harness than the one committed. So once the preparation's results
  were written again, on the coordinator's orders of 23 October, this train merged them
  and ran `python3 -I tests/model/run.py --full --write` on its own harness, at commit
  `a4031521074f`. Every check of that run passed. Each count it wrote is the count the
  preparation's harness gave, number for number; only the commit that
  [MODEL.md](../../tests/model/MODEL.md) and the results name is new, which is evidence
  that the inlined laws decide each configuration as the laws they replace did. No check,
  law, test or expected value changes.

  The files approved here are the ten outputs of that run at `a4031521074f`:
  - for angles, `tests/model/results/angle_check.txt`;
  - for every small grid, `tests/model/results/exhaustive.txt`;
  - for the lattice, `tests/model/results/grid_check.txt`;
  - for the plane of constant negative curvature, `tests/model/results/hyperbolic.txt`;
  - for the fifteen weakened rules, `tests/model/results/mutations.txt`;
  - for seed one, `tests/model/results/search-seed1.txt`;
  - for seed two, `tests/model/results/search-seed2.txt`;
  - for seed three, `tests/model/results/search-seed3.txt`;
  - for the patterns built by design, `tests/model/results/structured.txt`;
  - for the totals, `tests/model/results/summary.txt`.
