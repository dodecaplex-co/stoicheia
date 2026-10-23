- **The cadence suite's time limit goes from 150 minutes to 300.** The scheduled run of
  `.github/workflows/safe-push-tests.yml` runs the landing tool's whole suite
  (`scripts/test_safe_push.py`). On the cadence it took 72 to 78 minutes, and 137 on the
  run of 04:44 UTC on 23 October (39901919693), on a slow runner. The run of 11:33 UTC
  that day (39946930069), the first with the train checks of
  [#383](https://github.com/jackChallis/stoicheia/pull/383), reached the job's
  `timeout-minutes` of 150 and was cancelled there, mid-suite and with no hang: it ran on
  a runner as slow as the 04:44 run's (in it the tests older than #383 alone took 144
  minutes), and #383's tests took it over the limit. A later run on as slow a runner would
  end the same way. A red cadence run opens or updates an issue labelled
  `blocks-release`, so the release waits for a later green run; the repository's rules
  let other trains land meanwhile, but the lane, the coordinator's landing tool outside
  the repository, lands a tooling train only while the latest finished cadence run is
  green and under seven hours old, so a cancelled run holds every tooling train. Under the
  coordinator's ruling of 23 October 08:15 Pacific time (15:15 UTC), the
  `safe-push-tests` job's limit is now 300 minutes, under GitHub's 360 for a job on its
  hosted runners. This is operational: no check, test or step changes, and a run lasts
  no longer for it; a slow run finishes green where it was cancelled. The lasting fix is
  to shard the suite, card [#233](https://github.com/jackChallis/stoicheia/issues/233).

  This entry approves the new limit in `.github/workflows/safe-push-tests.yml`: its
  `safe-push-tests` job's `timeout-minutes` is 300, and its comment says why, with the
  runs it rests on.
