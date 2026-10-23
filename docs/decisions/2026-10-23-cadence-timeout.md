- **The cadence suite's time limit goes from 150 minutes to 300.** The scheduled run of
  `.github/workflows/safe-push-tests.yml` runs the landing tool's whole suite
  (`scripts/test_safe_push.py`). It took 38 to 45 minutes on GitHub's runners, and 78 on
  the morning of 23 October. The run of 11:33 UTC that day (39946930069), the first with
  the train checks of [#383](https://github.com/jackChallis/stoicheia/pull/383), whose
  tests take 20 to 90 seconds each, was cancelled at the job's `timeout-minutes` of 150,
  mid-suite and with no hang. Each later run would end the same way. The lane lands a
  tooling train only while the latest finished cadence run is green and under seven hours
  old, so a cancelled run holds every tooling train. Under the coordinator's ruling of
  23 October 08:15, the `safe-push-tests` job's limit is now 300 minutes. This is
  operational: no check, test or step changes, and the suite runs as before, with room to
  finish. The lasting fix is to shard the suite, card
  [#233](https://github.com/jackChallis/stoicheia/issues/233).

  This entry approves the change to `.github/workflows/safe-push-tests.yml`, whose
  `safe-push-tests` job's `timeout-minutes` is 300 and whose comment says why.
