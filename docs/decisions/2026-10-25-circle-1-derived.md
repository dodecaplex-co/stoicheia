- **Circle 1 kept as a derived property of the numerical model, ahead of its retirement
  (model, [#477](https://github.com/jackChallis/stoicheia/issues/477)).** On 25 October
  2026, at about 22:45 Pacific, the owner gave the coordinator's three recommendations a
  single answer: "yes to all three." The coordinator recorded on #477 what that approves,
  with #473: the new axiom `Tacit.radius_ne_zero`, and the plan this change serves, that
  Circle 1 (`Tacit.between_of_inside_chord`) become a theorem in `Prop02.lean` after
  III.2, keeping its name and type, with preparation trains first so that no check fails
  on main at any commit. When it is proved, its law leaves `tests/model/laws.toml`,
  `tests/model/search.py` and `tests/model/hyperbolic.py`, as Circle 3's did on 24
  October. But the exhaustive and structured harnesses ran Circle 1 by its law's name, and
  would have stopped at that removal. Here, as Circle 3's preparation did
  ([its entry](2026-10-24-circle-3-derived.md)), Circle 1's predicate becomes a derived
  property first, and the two harnesses run it under the derived name, on the
  configurations they already gave it. The law stays in all three files while Circle 1 is
  an axiom. Nothing in the Lean, the lock or any expected value moves.

  The predicate is word for word the guard and conclusion of Circle 1's law in
  `search.py`: for a point `A` inside the circle and two different points `B` and `C` of
  the circle, all three on one straight line, `A` lies between `B` and `C`.

  The model's run, `python3 -I tests/model/run.py --full --write`, was made at commit
  `242da9a7f107`, where this change sits on the radius rule's train, and it passed every
  check: no counterexample turned up in the plane, each of the 15 mutations was caught,
  and the hyperbolic plane refuted `Postulate5` alone, rightly. Against that train's run at
  `3a2ba2364a3a`, the one difference is where Circle 1's grid and built configurations are
  counted: its 3,228 exhaustive and 37,732 structured ones now count as a derived
  property's, so the plane's total for the axioms is 4,063,054 where it was 4,104,014,
  and the total for the derived properties 9,895,990 where it was 9,855,030. Its search
  and hyperbolic counts do not change. In the table of axioms Circle 1's row now shows a
  dot for the exhaustive and the structured harness, which run it only under its derived
  name, in the derived properties' table.

  Approved, for `tests/model/derived.py`: one new predicate, `derived.between_of_inside_chord`,
  listed among the derived properties, and a clause of the module's opening note saying
  why it is there.

  Approved, for `tests/model/exhaustive.py`: the run of Circle 1's grid configurations
  renamed to `derived.between_of_inside_chord`, and nothing else.

  Approved, for `tests/model/structured.py`: the run of Circle 1's built chords renamed
  to `derived.between_of_inside_chord`, its configurations as before.

  Approved, for `tests/model/MODEL.md`: 41 derived properties counted in five places,
  Circle 1's predicate named among them, the law counts of the two harnesses lowered by
  one each, and the numbers the run wrote.

  The run rewrites ten output files, and a sentence of its own approves each. The angle
  check's report, `tests/model/results/angle_check.txt`, is approved. The grid
  enumeration's report, `tests/model/results/exhaustive.txt`, is approved. The second
  grid check's report, `tests/model/results/grid_check.txt`, is approved. The hyperbolic
  plane's report, `tests/model/results/hyperbolic.txt`, is approved. The mutations'
  report, `tests/model/results/mutations.txt`, is approved. The random search's report
  for seed 1, `tests/model/results/search-seed1.txt`, is approved. The report for seed 2,
  `tests/model/results/search-seed2.txt`, is approved. The report for seed 3,
  `tests/model/results/search-seed3.txt`, is approved. The structured harness's report,
  `tests/model/results/structured.txt`, is approved. The table of
  every run, `tests/model/results/summary.txt`, is approved.
