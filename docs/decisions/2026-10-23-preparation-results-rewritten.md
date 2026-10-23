- **The preparation's model results, written again on its own harness (model).** Since
  [#378](https://github.com/jackChallis/stoicheia/pull/378), CI's `model` job runs
  `tests/model/results_check.py`, which refuses committed results unless they name the
  harness as it hashes now. The preparation for the second axiom retirement changes three
  of the harness's files (`tests/model/derived.py`, `tests/model/exhaustive.py` and
  `tests/model/structured.py`), and its results were not written again after it merged
  #378, so the check refused its pull request,
  [#265](https://github.com/jackChallis/stoicheia/pull/265). On the coordinator's orders
  of 23 October, `python3 -I tests/model/run.py --full --write` ran at the preparation's
  merge of main, commit `1634107840b7`, and all its checks passed: the plane gave no
  counterexample, the 15 mutations were all caught, and in the hyperbolic plane
  `Postulate5` alone failed, as it must. [MODEL.md](../../tests/model/MODEL.md) carries
  the counts as the run wrote them. The exhaustive and structured runs now count the 31
  laws this preparation keeps as derived properties under their `derived.` names, and the
  search and hyperbolic counts are as before. No check, law, test or expected value
  changes.

  This entry approves each result file that run wrote again, one by one:
  - the angle check's output, `tests/model/results/angle_check.txt`;
  - the exhaustive harness's output, `tests/model/results/exhaustive.txt`;
  - the lattice check's output, `tests/model/results/grid_check.txt`;
  - what the hyperbolic plane printed, `tests/model/results/hyperbolic.txt`;
  - the weakened statements' report, `tests/model/results/mutations.txt`;
  - the random search with its first seed, `tests/model/results/search-seed1.txt`;
  - the random search with its second seed, `tests/model/results/search-seed2.txt`;
  - the random search with its third seed, `tests/model/results/search-seed3.txt`;
  - the hypotheses built on purpose, `tests/model/results/structured.txt`;
  - and the totals of every run, `tests/model/results/summary.txt`.
