- **The safe_push tests run on a cadence, not on each pull request.** On 22 October 2026
  the owner wrote "I'm fine that this needs to run on a cadence and blocks release but
  every run no. And it has to be fast", and approved the plan that moves the suite to a
  cadence. The whole of `scripts/test_safe_push.py` had come to take 38 to 45 minutes on
  GitHub's runners, and past its 60-minute limit on some, on every pull request that
  touched a check input, `.github/` or WORKFLOW; and a defect in one of its tests failed
  every pull request that added a decision entry file. So one pull request had landed in
  eight hours. This takes the `safe-push-tests` job off the pull requests: it runs every
  six hours on main, and on demand, and a red run on main opens one issue labelled
  `blocks-release`, or adds the run to the one already open, with the run's link and the
  tests that failed, so the release waits for it. The five checks main's ruleset requires,
  the pre-flight and its guards are unchanged.

  The plan adds three requirements, which a later change carries, not this one: a change
  to the landing tool posts only with its whole suite run at its head; tooling trains land
  only while the latest cadence run is green; and a release needs a green run at its exact
  head.

  This entry approves the change to `.github/workflows/ci.yml`, which loses the
  `safe-push-tests` job and nothing else.

  This entry approves the new `.github/workflows/safe-push-tests.yml`, which runs the
  suite every six hours on main and on `workflow_dispatch`, with leave to read the
  repository alone and a checkout that keeps no token, and whose second job, which runs
  no code of the repository, alone may write issues, to open or update the issue.

  This entry approves the change to `scripts/test_safe_push.py`, whose test of the advised
  revert from a main without `docs/decisions/` assumed the folder held its README alone,
  and so failed once a pull request added an entry file: it now removes whatever the
  folder holds in the test's own clone, and a second case runs it with an entry in the
  baseline.
