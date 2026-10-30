- **Metric 9's law re-keyed in the model's harnesses before Common Notion 4 for figures
  replaces it (model, [#517](https://github.com/dodecaplex-co/stoicheia/issues/517)).** On
  28 October 2026 the owner chose, of the options put to them, "Euclid's C.N. 4"; issue
  #517, on resting I.4's area clause on Common Notion 4 in place of Metric 9, is the
  coordinator's record of that choice. Under it Metric 9, `Tacit.area_congruent`, is to
  leave the axioms, with Common Notion 4 for figures in its place, in a content train that
  follows this one; and when Metric 9 goes, its law goes from `tests/model/laws.toml`,
  `tests/model/search.py` and `tests/model/hyperbolic.py` with it. The exhaustive and the
  structured harnesses, though, call that law by its name on configurations of their own,
  and would stop at its removal. So this change comes first, in a train of its own, as the
  model's page asks under "Changing the axioms" of any program that names the law of an
  axiom about to be removed. The pre-flight's rule for a check change, `keep_apart`, lets
  the content change, of the checks' inputs, only values pinned to the edition, among them
  the lock and its hash, a law that moves with its axiom, the model's page and its results;
  the four programs touched here are check code, which is never pinned, so their re-key
  must land on main while Metric 9 is still an axiom, true and passing there, and must need
  nothing more when it leaves.

  The new predicate, `derived.area_congruent`, is Metric 9's law in `search.py`, guard and
  conclusion, without a change. It takes six points; seven times in ten it puts for `E` and
  `F` the images of `B` and `C` under a lattice motion carrying `A` to `D` (a reflection or
  none, then up to three quarter turns); and when the triangles `ABC` and `DEF` then agree
  in their three sides and their three angles, it asks that they agree in area. The law
  itself stays in all three files for as long as Metric 9 is an axiom, so the random search
  and the hyperbolic run still test it under its own name. Nothing in the Lean, the lock or
  any expected value moves, and no check is loosened.

  `python3 -I tests/model/run.py --full`, on the harness as this change leaves it, passed
  every check: nothing in the plane broke an axiom's law or a derived property, the 15
  weakened statements were each caught, and in the hyperbolic plane `Postulate5` alone
  failed, 1,189 times, as it must. Set beside the
  results of the run at `8ce3f1ae4285`, its counts differ in one respect, where Metric 9's
  grid and built configurations are counted: its 375,479 exhaustive and 94,050 structured
  ones now count as a derived property's. The plane's total for the axioms therefore falls
  from 4,063,299 to 3,593,770, the exhaustive harness's part of it from 2,243,944 to
  1,868,465 and the structured harness's from 595,529 to 501,479, while the total for the
  derived properties rises from 9,895,990 to 10,365,519. Metric 9's 54,696 configurations
  in the search, over the three seeds, and its 10,711 in the hyperbolic plane do not
  change. In the table of axioms its exhaustive and structured cells become dots, and the
  table of derived properties gains its row. The results and the counts on the model's page
  are those `python3 -I tests/model/run.py --full --write` writes at the commit that holds
  this harness, as WORKFLOW's section 8 requires of a change to a harness file.

  In `tests/model/derived.py` the predicate `derived.area_congruent`, its line among the
  derived properties, and a clause of the module's docstring saying why it is kept there
  are approved.
  In `tests/model/exhaustive.py` the call that runs every six-point configuration of the
  small grid, `gen_cong`, now made as `derived.area_congruent`, and the comment above it
  saying so, are approved.
  In `tests/model/structured.py` the call that runs the built congruent copies, `g_cong`,
  under the name `derived.area_congruent`, its generator untouched, is approved.
  In `tests/model/run.py` the one label changed, the seed the full plan gives the exhaustive
  harness now described as for `derived.area_congruent`'s isometries, is approved.
  In `tests/model/MODEL.md` the 42 predicates kept as derived properties, counted in five
  places, Metric 9 named among them as still an axiom, with a sentence on the dots its row
  shows, the law counts of the exhaustive and structured harnesses each lowered by one, and
  the counts the run writes, all its count markers standing, are approved.

  Each results file the run rewrites has a sentence of its own here.
  This entry approves `tests/model/results/angle_check.txt`, the second, separately written
  check of the angles and areas.
  This entry approves `tests/model/results/exhaustive.txt`, in which Metric 9's grid now
  reports under `derived.area_congruent`.
  This entry approves `tests/model/results/grid_check.txt`, the exact incidence and order
  check on its own grid.
  This entry approves `tests/model/results/hyperbolic.txt`, where Metric 9 is still run by
  its law in the Beltrami-Klein reading.
  This entry approves `tests/model/results/mutations.txt`, with its fifteen statements
  weakened on purpose.
  This entry approves `tests/model/results/search-seed1.txt`, random sampling from its first
  seed.
  This entry approves `tests/model/results/search-seed2.txt`, random sampling from its
  second seed.
  This entry approves `tests/model/results/search-seed3.txt`, random sampling from its third
  seed.
  This entry approves `tests/model/results/structured.txt`, where the built congruent copies
  now count under `derived.area_congruent`.
  This entry approves `tests/model/results/summary.txt`, the plain-text table that `--write`
  draws from all of those.
