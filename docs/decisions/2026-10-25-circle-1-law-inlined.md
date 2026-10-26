- **Circle 1's law draws from `gs_cm`, and the allow-list for law code narrows by
  `gs_chord`, before Circle 1's retirement (tooling,
  [#477](https://github.com/jackChallis/stoicheia/issues/477)).** On 25 October 2026 the
  owner's answer "yes to all three." approved, among the coordinator's recommendations,
  retiring Circle 1 (`Tacit.between_of_inside_chord`) into a theorem after III.2, once
  trains that prepare for it have landed, so that no commit on main fails a check; #477 is
  the coordinator's record. At that retirement Circle 1's law leaves both model harnesses.
  In `tests/model/hyperbolic.py` the law was the only user of the generator `gs_chord`,
  whose name `scripts/safe_push.py` lists in `LAW_GLOBALS`, and the test that every
  name there is needed by some law would then fail on main until a second change took
  it out, a check change that may not travel with the lock change it would follow.
  Circle 3's retirement met the same problem
  ([its preparation](2026-10-24-circle-3-law-inlined.md)), and this does as it did.

  The law now samples with `gs_cm('chord')`, a new kind of the generator maker that the
  two circle-meeting laws already use, and the body of `gs_chord` moves into that kind
  as it was, drawing the same random numbers in the same order; `gs_chord`, which
  nothing else used, goes, and `LAW_GLOBALS` loses its name and nothing else. Circle 1's
  law in `tests/model/search.py` calls only helpers other laws also call, so nothing
  there moves. When the law leaves at the retirement, the kind is left unused inside a
  maker other laws still need, and no name in the allow-list goes unused.

  `python3 -I tests/model/run.py --full --write` ran at commit `c6515f8dacfc`, this
  change on Circle 1's derived preparation, and passed every check.
  Every file it wrote holds, below the lines of its header that name the commit, the
  harness's hash and the date, and apart from the time each run took, exactly what the
  run at `242da9a7f107`, before this change, wrote: the law met the same configurations
  and drew the same random numbers. The allow-list's test passes, and with Circle 1's
  law cut from both harnesses it passes still, which is what the retirement needs.

  Approved, for `tests/model/hyperbolic.py`: Circle 1's law drawing from
  `gs_cm('chord')`, the kind added to `gs_cm` with `gs_chord`'s draws unchanged, and
  `gs_chord` removed.

  Approved, for `scripts/safe_push.py`: the name `gs_chord` taken out of the generators
  `LAW_GLOBALS` allows `hyperbolic.py`'s laws, with no other change to the file.

  Approved, for `tests/model/MODEL.md`: the counts the run wrote between its markers.

  The run rewrites ten output files, and each has an approval of its own. The angles and
  areas check, `tests/model/results/angle_check.txt`: approved. The grid enumeration,
  `tests/model/results/exhaustive.txt`: approved. The independent grid check,
  `tests/model/results/grid_check.txt`: approved. The hyperbolic run, where the law drew
  from its new kind, `tests/model/results/hyperbolic.txt`: approved. The weakened
  statements, `tests/model/results/mutations.txt`: approved. The search's first seed,
  `tests/model/results/search-seed1.txt`: approved. Its second,
  `tests/model/results/search-seed2.txt`: approved. Its third,
  `tests/model/results/search-seed3.txt`: approved. The structured run,
  `tests/model/results/structured.txt`: approved. The summary of all of them,
  `tests/model/results/summary.txt`: approved.
