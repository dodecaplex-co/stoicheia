- **The kinds of `gs_cm` that no law draws from removed, the last trace of Circle 3's
  law among them (tooling, [#436](https://github.com/jackChallis/stoicheia/issues/436),
  item 1).** The retirement of
  Circle 3 ([its entry](2026-10-24-circle-3-retired.md)) took `Tacit.outside_of_between`'s
  law out of `tests/model/hyperbolic.py`, but kept the kind `'out'` of the generator maker
  `gs_cm`, which only that law drew from: the retirement could change a harness only in the
  laws that moved with their axioms. The coordinator's orders of 24 October assign the
  follow-up to this card. So the branch `if kind == 'out':` of `gs_cm` goes, with the
  comment above it that named Circle 3's law. Its review found two more kinds that no law
  draws from: `'nss'`, unused since the first retirement wave took out the law of
  `not_same_side_of_circles_meet`, and `'oio'`, unused since the second took out that of
  `circles_meet_of_on_inside_outside`; they go too, as the preparation for Circle 3's
  retirement removed kinds that nothing drew from any more
  ([its entry](2026-10-24-circle-3-law-inlined.md)). `gs_cm` keeps `'side'`, for
  `circles_meet_same_side`, and `'five'`, for `circles_meet`, the only kinds a law calls
  for, and no law changes. Each removed branch was tested before it drew a random number,
  and neither kept kind reached the two inner ones' draws, so `'side'` and `'five'` draw
  exactly as before. (`tests/model/structured.py` has its own `g_cm`, with kinds of the
  same names, which this change leaves alone.)

  At commit `442989248536`, this change's code, `python3 -I tests/model/run.py --full
  --write` passed every check. Each results file differs from main's in its header (the
  commit, the harness's hash, the date) and in timings alone; every count is the same.
  The allow-list for law code in `scripts/safe_push.py` names `gs_cm` as a generator maker
  and no kind of it, so it is unchanged.

  This entry approves the change to `tests/model/hyperbolic.py`: the unused kinds `'out'`,
  `'nss'` and `'oio'` of `gs_cm`, and the comment on the first, are removed, and nothing
  else.

  This entry approves the change to `tests/model/MODEL.md`, a counts line naming commit
  `442989248536` and 25 October.

  This entry approves `tests/model/results/angle_check.txt`, written again at
  `442989248536`.

  This entry approves `tests/model/results/exhaustive.txt`, with only its header and its
  times new.

  This entry approves `tests/model/results/grid_check.txt`, the same lattice counts under a
  new header.

  This entry approves `tests/model/results/hyperbolic.txt`, the output of the harness that
  lost the kinds, with every count kept.

  This entry approves `tests/model/results/mutations.txt`, its weakened rules caught as
  before.

  This entry approves `tests/model/results/search-seed1.txt`, the search from seed 1 after
  this change.

  This entry approves `tests/model/results/search-seed2.txt`, the search from seed 2 after
  this change.

  This entry approves `tests/model/results/search-seed3.txt`, the search from seed 3 after
  this change.

  This entry approves `tests/model/results/structured.txt`, its designed patterns
  counted as before.

  This entry approves `tests/model/results/summary.txt`, with the totals it held.
