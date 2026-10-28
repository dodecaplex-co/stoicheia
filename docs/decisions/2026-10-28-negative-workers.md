- **The negative tests in parallel worktrees (checks,
  [#607](https://github.com/dodecaplex-co/stoicheia/issues/607)).** On 28 October 2026 the
  owner said, of the pre-flight's speed: "running on my own hardware is ideal if possible.
  Then the speedup on the free 4 core. then explore 8 core / 16 core"; card #607 is the
  coordinator's record of it. The negative tests were the largest part of every heavy
  landing: 1,085 of the 1,899 seconds of one two-pass pre-flight on the Mac that morning,
  and 940 of 1,599 on GitHub's free four-core runner, each on one core.

  `negative_tests.py --workers N`, or `STOICHEIA_NEGATIVE_WORKERS` when the option is
  absent, runs the chosen plants in N workers at once. Each worker is a Git worktree of its
  own, given the tree's state and a clone of its build, and runs its share with the Git
  bracket, guards and closing check that a run narrowed by `--plant` has. The parent reads
  every worker's report and prints one, in the stable order, the same as one worker's apart
  from the times; a plant that misses its change, a worker that crashes, and a worker's
  tree that is not as it found it each fail the whole run. The shares are balanced by the
  seconds each plant took, as `tests/negative_times.json` records them. No plant is
  dropped, skipped or merged, no expected refusal changes, and with one worker, the
  default, the run is as it was.

  The variable lets the pre-flight and the yards choose N without changing their commands:
  `scripts/safe_push.py` passes the checks every variable of its caller's but those of
  Git's, so it is not changed.

  This entry approves the change to `scripts/negative_tests.py`, which runs the plants in N
  workers when asked, and one by default.

  This entry approves the change to `tests/test_negative_tests.py`, which plants the
  workers' failures and compares N workers' report with one worker's.

  This entry approves the new `tests/negative_times.json`, the seconds each plant took in a
  pre-flight on the Mac on 28 October 2026, which balance the workers' shares.
