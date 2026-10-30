<!-- entry: id=shard-headroom cards=798 line="The cadence's safe_push tests run in twelve shards, each with 90 minutes, dealt by times measured afresh." -->
- **The cadence's safe_push tests run in twelve shards, each with 90 minutes, dealt by
  times measured afresh (tooling,
  [#798](https://github.com/dodecaplex-co/stoicheia/issues/798)).** The coordinator's
  orders of 30 October 2026, 07:15 Pacific time, assign card #798 to ship TT; this entry
  claims no decision of the owner's.

  The workflow `.github/workflows/safe-push-tests.yml` runs `scripts/test_safe_push.py` on
  main every six hours, in shards side by side, each shard's job limited to 60 minutes
  until now. In the run of 30 October 12:48 UTC (41058182573) shards 1, 2 and 6 of eight
  were cancelled at that limit, and shard 7 failed in its first two seconds, GitHub unable
  to resolve `actions/setup-python@v5` for it; a red cadence run holds the release. The
  slowest shard of each run had climbed from 40 minutes on 29 October 18:04 UTC
  (40927368447) to 48 at 03:45 and 05:42 on 30 October and past 60 at 12:48, while the
  fastest that ran its tests stayed between 19 and 34 (the jobs' own start and end times,
  `gh run view --json jobs`, for the six cadence runs from 40927368447 to 41058182573).

  Three causes were measured from the shards' logs of the runs of 29 October 22:43 UTC
  (40967994404), 30 October 10:51 (41043816571) and 12:48. First, the times the shards are
  dealt by, `scripts/test_safe_push_times.json`, were those of run 40162492847, of 25
  October UTC: 83 of the suite's 552 tests had no time there and each weighed the median,
  3.1 seconds, though in the run of 10:51 they took 80 minutes between them. Second, the
  469 tests the file did time took 224 minutes in the run of 10:51 against the file's 155,
  and with the 83 the whole suite came to 303 minutes, against 155 five days before. Dealt
  by that file, the run of 10:51's own times give its eight shards 23.6 to 45.6 minutes,
  as its shards took. Third, a shard's time varies with the runner it lands on: a fit of a
  time to each test and a factor to each shard's job, over the three runs, has the slowest
  runner taking about 2.7 times as long as the fastest, and up to about twice as long as
  another shard's of the same run. Six of the seven shards of the run of 12:48 that ran
  drew slower runners than the run of 10:51's on average, and the seventh one about as
  fast.

  So the times file is written again, by `python3 scripts/test_safe_push.py
  --times-from-log`, from the log of the green run of 10:51 (41043816571, at commit
  08ba00f13), which timed every one of the 552 tests unittest's loader lists on main
  today; no test now weighs the median. The suite runs in twelve shards rather than eight.
  Dealt by those times, each of the twelve comes to 25.3 minutes, and the heaviest test
  takes 9.8; since each test's time carries the speed of the runner it was measured on, on
  runners as fast as the run of 10:51's on average the twelve come to 24 to 29 minutes.
  Each shard's job may now take 90 minutes: half again the 60 at which the shards of 12:48
  were cancelled; the heaviest of the twelve would take about 50 minutes on the slowest
  runner measured, and about 74 with the suite grown by half, still inside 90. Every test
  still runs in exactly one shard, every shard still writes the list of the tests it ran
  and keeps its log to unittest's summary, and the proof still reads N from the matrix, so
  nothing of the verdict or the report changes. No shard takes longer for this: each one's
  share is smaller.

  This entry approves the change to `.github/workflows/safe-push-tests.yml`: the
  `safe-push-shards` job's matrix holds 1 to 12, its `timeout-minutes` is 90, and its
  comments say why, with the runs the numbers come from.

  This entry approves the new `scripts/test_safe_push_times.json`, written whole by
  `--times-from-log` from the log of run 41043816571, whose note names that run and its
  commit.

  This entry approves the change to `scripts/test_safe_push.py`: the workflow contract of
  `safe-push-tests.yml` holds the new matrix and limit, the test of the shard job expects
  the limit of 90, the stand-in for gh gives a green run a job for each of the twelve
  shards, and the docstring's example names a shard of twelve.

  This entry approves the change to `scripts/safe_push.py`, whose module docstring,
  comment on `SUITE_JOBS` and `suite_gate`'s docstring no longer count the shards, so that
  they stay true whatever the matrix holds; none of its code changes.

  This entry approves the change to `.github/workflows/ci.yml`, whose comment on a release
  pull request's run no longer counts the shards; none of its jobs changes.

  What this does not settle: a shard's runner can still make it run up to about twice as
  long as another shard of the same run, which no dealing by times can foresee, so the
  slowest shard of a run will often be more than a quarter above the median shard, even
  with the twelve even by their times; the suite's whole time, which went from 155 minutes
  to 303 between 25 and 30 October, may outgrow the limit again, which holds it to about
  1.8 times today's on the slowest runner measured; and each test added after today weighs
  the median until the times are measured again, as these were.
