- **The hyperbolic harness loses its dead `chord` generator (model,
  [#561](https://github.com/dodecaplex-co/stoicheia/issues/561)).** Card #561, the
  coordinator's record of the loose ends Circle 1's retirement left (#477), asks for the
  kind `'chord'` of `gs_cm` in the hyperbolic harness to go. It drew one circle, two points
  on it and a point of the straight line through them, most often between them, for the
  law of `between_of_inside_chord`; that law left the hyperbolic harness when Circle 1
  became a theorem, and since then no law has called
  `gs_cm('chord')`, so the branch generated nothing any run reads. Deleting it changes no
  law, no generator a law calls, and no configuration: every count in the results is the
  same as before. What changes is the header of each report (the commit and date of the
  run and the harness's hash), and in the exhaustive report the time each law took. The
  runs were written by `python3 -I tests/model/run.py --full --write` at the harness's
  commit, as WORKFLOW's section 8 asks of a change to a harness file.

  For `tests/model/hyperbolic.py`, the deletion of the fifteen lines of the `'chord'` branch
  in `gs_cm`, with its comment, is approved, and nothing else in that file changes.
  In `tests/model/MODEL.md`, only the commit and date that its counts paragraph names move,
  to the harness commit the run read; its count markers stand, and this is approved.
  The independent angle check's output, `tests/model/results/angle_check.txt`, rewritten by that
  run with no line changed below its header, is approved.
  Every configuration on the small grids, `tests/model/results/exhaustive.txt`, comes back
  with unchanged counts and new timings under the new header, and is approved so.
  The grid check of the plane, `tests/model/results/grid_check.txt`, is approved with its
  header alone changed.
  The hyperbolic plane's report, `tests/model/results/hyperbolic.txt`, from the harness this
  entry changes, still has Postulate 5 failing 1,189 times and every other axiom holding,
  and it is approved.
  The mutation report, `tests/model/results/mutations.txt`, still catches all fifteen
  weakened statements; approved.
  The random search under seed 1, `tests/model/results/search-seed1.txt`, is approved with
  its counts as they were.
  Under seed 2, `tests/model/results/search-seed2.txt` holds the same counts, and is approved.
  Under seed 3, `tests/model/results/search-seed3.txt` does as well, and is approved.
  The structured search's report, `tests/model/results/structured.txt`, unchanged but for
  the header naming the run, is approved.
  The summary of every run, `tests/model/results/summary.txt`, which `--write` makes from
  the reports above, is approved as written.
