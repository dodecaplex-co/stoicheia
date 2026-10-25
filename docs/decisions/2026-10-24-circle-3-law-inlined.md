- **Circle 3's law, rewritten within a narrower allow-list, before its retirement
  (tooling, [#294](https://github.com/jackChallis/stoicheia/issues/294)).** When #294's
  retirement takes Circle 3 (`Tacit.outside_of_between`) out of the lock, its law leaves
  both model harnesses, and three entries of `LAW_GLOBALS`, the allow-list for law code,
  would then serve no law: `in_or_on` among the calls of `tests/model/search.py` and of
  `tests/model/hyperbolic.py`, and `gs_convex` among the latter's generator makers. The
  test that each entry is needed would fail on all three, on main, between the
  retirement's landing and the narrowing's, and no pull request may change a check
  together with what that check judges. Wave two met the same problem, and on 21 October
  2026 the owner chose, from the three options put to them then, "A prep PR first, no
  exception" ([#119](https://github.com/jackChallis/stoicheia/issues/119) is the
  coordinator's record); the coordinator's orders of 24 October take that course for
  Circle 3. So this train, landing before the retirement, has Circle 3's law work out
  in its own body what those names gave it, and narrows the list by exactly the three.

  In `search.py` the law tests `inside(A, al) or on_circle(A, al)` where it called
  `in_or_on`, which was that expression. In `hyperbolic.py` it tests
  `ch2(A, centre(al)) <= al[2]` where it called `in_or_on`, which was that comparison,
  and it samples with `gs_cm('out')`, a new kind of the generator maker the two
  circle-meeting laws already use, into which the draws of `gs_convex('out')` move
  unchanged, as #119's preparation moved two samplers into `gs_convex`. Since wave two,
  Circle 3's law was the one user of `gs_convex`, so the whole function goes, with its
  kinds that nothing drew from any more; each harness's `in_or_on`, which nothing else
  there called, goes too. The copy of Circle 3's predicate in `tests/model/derived.py` is
  unchanged. No other law changes, and the law decides as before on every configuration,
  drawing the same random numbers in the same order.

  At commit `c29cf9bd9fed`, this change's code, `python3 -I tests/model/run.py --full
  --write` passed every check. Below each file's header, which names the commit, the
  harness's hash and the time taken, every line it wrote is the line the harness before
  this change wrote, save for the exhaustive harness's timings; so the rewritten law and
  sampler give the model byte-identical output. The allow-list's test
  passes here, and again with the retirement's harnesses in place.

  This entry approves the change to `tests/model/search.py`, where Circle 3's law no
  longer calls `in_or_on` and that helper is removed.

  This entry approves the change to `tests/model/hyperbolic.py`, where Circle 3's law
  calls neither `in_or_on` nor `gs_convex`, and `gs_cm` gains the kind `'out'`.

  This entry approves the change to `scripts/safe_push.py`, whose `LAW_GLOBALS` loses
  `in_or_on` twice and `gs_convex` once, and nothing else.

  This entry approves the change to `scripts/test_safe_push.py`, whose case of a
  generator maker called with no argument now names `gs_cm()` in place of `gs_convex()`.

  This entry approves the change to `tests/model/MODEL.md`, whose counts now name the
  commit of this run.

  This entry approves `tests/model/results/angle_check.txt` as rewritten by this run.

  This entry approves `tests/model/results/exhaustive.txt`, whose timings alone differ.

  This entry approves `tests/model/results/grid_check.txt`, the lattice's report from
  this run.

  This entry approves `tests/model/results/hyperbolic.txt`, where the inlined law and
  sampler ran.

  This entry approves `tests/model/results/mutations.txt`, the fifteen weakened rules
  reported anew.

  This entry approves `tests/model/results/search-seed1.txt`, seed 1 of the search
  that ran the inlined law.

  This entry approves `tests/model/results/search-seed2.txt`, the second seed's search.

  This entry approves `tests/model/results/search-seed3.txt`, where the third seed drew.

  This entry approves `tests/model/results/structured.txt`, the patterns built by design,
  run again.

  This entry approves `tests/model/results/summary.txt`, whose totals are unchanged.
