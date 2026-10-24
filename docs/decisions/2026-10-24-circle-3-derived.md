- **Circle 3 kept as a derived property of the numerical model, before its retirement
  (model, [#294](https://github.com/jackChallis/stoicheia/issues/294)).** The next train of
  #294 proves Circle 3 (`Tacit.outside_of_between`) after III.2 and takes it out of
  `Certificate/axioms.lock`, and its law then leaves `tests/model/laws.toml`,
  `tests/model/search.py` and `tests/model/hyperbolic.py`, as the 39 retired rules' laws
  left before it. The exhaustive and structured harnesses ran Circle 3 by its law's name,
  so they would stop at its removal. Here, as the second retirement's preparation did for
  31 rules, `tests/model/derived.py` keeps Circle 3's predicate, the guard and conclusion
  of its law in `search.py` unchanged, as the derived property `derived.outside_of_between`,
  and the two harnesses run it under that name, with the configurations they gave the law.
  The law itself stays, in `search.py`, `hyperbolic.py` and `laws.toml`, while Circle 3 is
  an axiom, and `run.py` still finds its hypotheses met. This lands first, in a check
  change of its own, so that the retirement changes only the values pinned to the lock.

  `python3 -I tests/model/run.py --full --write` ran at commit `bfa20bf2a4e9`, the
  harness as this change leaves it, and every check passed: the plane gave no
  counterexample, all 15 mutations were caught, and in the hyperbolic plane `Postulate5`
  alone failed, as it must. Circle 3's 281,664 exhaustive and 47,802 structured
  configurations move from the axiom totals to the derived properties', so the plane's
  axiom total falls from 4,427,399 to 4,097,933 and the derived properties' rises from
  9,525,564 to 9,855,030; its search and hyperbolic counts are as before.
  [MODEL.md](../../tests/model/MODEL.md) carries the counts as the run wrote them, and
  says that 40 predicates are kept as derived properties. No law, axiom, test or expected
  value changes, and no check is loosened. It belongs to #294, within #152.

  This entry approves the change to `tests/model/derived.py`, which gains the predicate
  `derived.outside_of_between`, the guard and conclusion of Circle 3's law.

  This entry approves the change to `tests/model/exhaustive.py`, which runs Circle 3's
  configurations under the name `derived.outside_of_between`.

  This entry approves the change to `tests/model/structured.py`, which runs Circle 3's
  configurations under the name `derived.outside_of_between`, in the same place.

  This entry approves the change to `tests/model/MODEL.md`, which counts 40 derived
  properties and gives the counts of this run.

  This entry approves, one by one, each result file the run wrote again:
  - `tests/model/results/angle_check.txt`, the angle check's output;
  - `tests/model/results/exhaustive.txt`, the exhaustive harness's output;
  - `tests/model/results/grid_check.txt`, the lattice check's output;
  - `tests/model/results/hyperbolic.txt`, the hyperbolic plane's output;
  - `tests/model/results/mutations.txt`, the weakened statements' report;
  - `tests/model/results/search-seed1.txt`, the random search's first seed;
  - `tests/model/results/search-seed2.txt`, the random search's second seed;
  - `tests/model/results/search-seed3.txt`, the random search's third seed;
  - `tests/model/results/structured.txt`, the structured harness's output;
  - and `tests/model/results/summary.txt`, the totals of every run.
