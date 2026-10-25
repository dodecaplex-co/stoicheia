- **The shards are dealt by the times of a cadence run, read from its own shard steps
  ([#425](https://github.com/jackChallis/stoicheia/issues/425)).** The cadence's shards,
  from [#233](https://github.com/jackChallis/stoicheia/issues/233) (landed as #419, [its
  entry](2026-10-24-safe-push-shards.md)), are dealt by the seconds in
  `scripts/test_safe_push_times.json`, which until now held the times of the CI run of #239
  on 21 October: 288 tests, so that of the 469 the loader lists on main at 80813728, 181
  weighed the median, 2.7 seconds. By that file this branch's 474 tests came to 5.8
  minutes a shard, while the shards of run 40135685522, the first sharded run on main, at
  8839a510, took 14 to 34 minutes, and the longest shard sets a run's length. Card #425
  asks that the times be read from the cadence's own shard steps, and that the review
  suggestions TS listed in #419 be taken up.

  The reader. `--times-from-log` read only a step whose group line opened with
  `python3 scripts/test_safe_push.py`; the cadence's shard step has a script of two lines,
  so its group line is `Run set -o pipefail`, as the entry of #233 noted, and no cadence
  run could be read. Now a step counts when a line of its script runs that command: the
  group line, which holds the script's first line, or a line GitHub echoes in cyan before
  the step's `##[endgroup]`, as in the log of run 40135685522. The old step of one line
  still counts. A line that only echoes the command, a line of an action's `with`, and a
  line of a step's output do not; the proof's step, which runs the script with no test's
  line, is passed over, as before.

  The completeness rule. By the coordinator's ruling of 24 October 18:58, option (A), the
  timing tool's rule that the logs time every test the loader lists, and no other, is
  relaxed, because under it a branch that adds a test could never be timed from an older
  run. A test the loader lists with no line in the logs is left out of the file, and so
  weighs their median, as `--shard` already weighs a test the file does not name; a test
  the logs time that the loader no longer lists is left out; and the command names each
  of both on stderr, with their counts. Still refused, each with a planted test: a run
  whose count of tests' lines differs from unittest's "Ran N", a test that ran twice, a run
  with no line from setUpModule, a run cut short, logs that hold no run, and, new, logs
  none of whose tests the loader lists. The coverage proof, `--cover`, and the dealing are
  unchanged, and no expected value or test of theirs changed.

  The file's note now names its source: the run, by the name of the log, `run-ID.log`, as
  `gh run view ID --log > run-ID.log` saves it (the log names its run too, in
  upload-artifact's URLs, but the note takes it from the name); the commit actions/checkout says it checked out; and how many of the tests the loader
  listed when the file was written weigh the median, and how many timed tests were left
  out. Only a log's own name reaches the note, never its folder.

  The refresh. The file is written again from run 40162492847, a green cadence run on main
  at 80813728, this branch's base, the newest green run when this train reached the step.
  It times 469 tests, and setUpModule at 0.8 seconds; of this branch's 474 tests, the five
  that this train adds weigh their median, 3.1 seconds, and none is left out. Dealt by it,
  each of the eight shards comes to 19.5 minutes, and the eight together to 155.8 minutes,
  against 155.7 for that run's eight shard steps by the log's stamps, which took 14.1 to
  34.0 minutes each.
  Whether later runs' shards come out as even is for those runs to show: GitHub's runners
  differ in speed, as the 137 minutes of the slow run cited in the entry of #233 show. The
  note dates the run by GitHub's stamps, in UTC: 25 October.

  The review's other points. The comments that counted the cadence's jobs as three now
  name what the workflow runs: the eight shards, the verdict job `safe-push-tests`,
  `negative-tests`, `formal-model-kernel` and `report`, in `scripts/safe_push.py`'s
  comment on `SUITE_JOBS` and its docstrings, `.github/workflows/ci.yml`, the report job's
  comment and the issue's closing sentence in `.github/workflows/safe-push-tests.yml`, and
  the tests; `SUITE_JOBS` and the release's gate are unchanged. The report names the shards
  whose kept logs show them red: one whose log ends in a summary that is not OK, one whose
  log stops before unittest's summary, and one that kept no log, of the N the logs' own
  first `Shard K of N:` line gives. It still runs no code of the repository, keeps its one
  permission, `issues: write`, and reads no API but the issues'; so it says too that the
  run's page gives each shard's result, since a shard can be red for a step its log does
  not show, and a shard of a rerun that kept no log may leave an earlier attempt's. Reading
  each shard's result from the jobs API is left out: the job's token is granted
  `issues: write` alone, and whether it may read a run's jobs without `actions: read` was
  not tried. The run model's `resolved()` now refuses any `${{` it does not read, such as
  a function's call, where it passed it through. The report's fixture now gives each
  shard's log the count of tests it holds, where it said "Ran 125 tests" of every one. The
  test file's docstring says that the proof shows every test ran once, and passed or was
  skipped. The subtests of the release's gate test,
  `test_release_needs_a_green_safe_push_tests_run_at_its_head`, each start from what the
  pre-flight left, origin's main and branch and the stand-in's state alike, so that a case
  that merged by mistake changes no other case's outcome.

  Left out, as the card's orders say: the pinned install of the verdict job, which is
  #409's, and `--cover`. WORKFLOW, section 8, said the times were read from the run of
  #239; it now says how they are read.

  The tests. In `Shards`: the times read from the cadence's shard step, in lines shaped
  like the log of run 40135685522, with the run and the commit in the note, beside three
  steps that must not be read; a listed test with no line weighing the median, named on
  stderr with the count; a logged test the loader no longer lists left out, and named;
  the refusals above, the command writing nothing when it refuses; and `resolved()`'s
  refusal. In `CadenceReport`, the shards red by their logs named, and none named when no
  log shows one red; in `CadenceRun`'s planted reds, the failing test's shard named.
  Each new or changed test of the reader and of `resolved()` was seen to fail in a scratch
  copy with its guard taken out, sixteen guards in all, and to pass with it. No check or
  test is weakened, but for the two refusals the ruling turns into allowances.

  This entry approves, in `.github/workflows/safe-push-tests.yml`, the report naming the
  shards red by their logs, and the comments and the issue's text that count its jobs.

  This entry approves, in `.github/workflows/ci.yml`, the comment of the `risk` job that
  counts the jobs of the safe-push-tests workflow.

  This entry approves, in `scripts/safe_push.py`, the comment and docstrings that count
  the cadence's jobs; its code is unchanged.

  This entry approves, in `scripts/test_safe_push.py`, the reader of the shard step, the
  relaxed completeness rule and its stderr, the note's source, `resolved()`'s refusal, the
  independent subtests of the gate test, and the new and changed tests above.

  This entry approves `scripts/test_safe_push_times.json` as written again from run
  40162492847.
