- **The lane-condition test runs on each pull request's own path, as a check of CI's
  `check` job ([#346](https://github.com/jackChallis/stoicheia/issues/346)).** The first
  part of #346 added a unit test that reads every workflow and finds a step after a job's
  lane step without the lane's condition, as #339's steps in CI's `negative` job were. It
  ran only in `Units` and on the six-hourly cadence, so the pull request that added such a
  step was not failed by it. Now that the registry of checks
  ([#229](https://github.com/jackChallis/stoicheia/issues/229)) lets a check be added as a
  file, the test is a check of its own, at order 135, after `tests/test_screen.py`: CI's
  `check` job runs it on each pull request, and the pre-flight runs it once it is on main.
  The coordinator approved this on 22 October at 23:10, as one file of the registry and
  section 8's regenerated block. The test reads the workflows with PyYAML, which CI's
  `check` job did not install, so the command would have failed there at its import, as
  it did when run in a fresh environment without the parser; by the coordinator's ruling
  of 24 October 02:35, which amends that approval, the job now installs the parser, after
  elan and before the run of the checks, from the pinned
  `scripts/requirements-test_safe_push.txt`, the file that CI's `queue-integrity` job and
  the cadence's `safe-push-tests` job already install. Section 8 says that the check
  needs the parser, so that a contributor running the sequence or the pre-flight installs
  it once. The test of the `check` job's shape allowed no setup step
  beyond checkout, Python and elan; by the coordinator's ruling of 24 October 02:40, it
  now allows that one install, exactly that line, once, straight after elan, with no
  condition, environment, shell or working directory. Existing planted refusal cases
  remain refused, but removing elan now reports "CI check setup prefix is incomplete before
  the parser's install" instead of "CI check setup prefix is incomplete before the first
  check." Six new planted cases are refused: the install of
  another requirements file, an extra package on the line, the install after the run of
  the checks, the install twice, the install before elan, and no install. With the guard
  that refuses each taken out, its case was seen to be accepted. The train is of class R5,
  since it changes the CI workflow.

  This entry approves the new file `checks/24-lane-condition.toml`, which runs the
  lane-condition test of `scripts/test_safe_push.py` in CI's `check` job at order 135.

  This entry approves the change to `.github/workflows/ci.yml`, whose `check` job gains
  one step that installs the pinned YAML parser from
  `scripts/requirements-test_safe_push.txt` before the run of the checks.

  This entry approves the change to `scripts/test_safe_push.py`, whose model of the
  `check` job allows that one install, exactly, after elan, with six planted refusals.
