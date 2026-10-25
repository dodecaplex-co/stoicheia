- **The lane-condition test runs on each pull request's own path, as a check of CI's
  `check` job ([#346](https://github.com/jackChallis/stoicheia/issues/346)).** The first
  part of #346 added a unit test that reads every workflow and finds a step after a job's
  lane step without the lane's condition, as #339's steps in CI's `negative` job were. It
  ran only in `Units` and on the six-hourly cadence, so the pull request that added such a
  step was not failed by it. Now that the registry of checks
  ([#229](https://github.com/jackChallis/stoicheia/issues/229)) lets a check be added as a
  file, the test is a check of its own, at order 135, after `tests/test_screen.py`: CI's
  `check` job runs it on each pull request, and once it is on main the pre-flight runs it
  for each train of class R3 and above. The coordinator approved this on 22 October at
  23:10, as one file of the registry and section 8's regenerated block.

  The test reads the workflows with PyYAML, which CI's `check` job did not install, so the
  command would have failed there at its import, as it did when run in a fresh
  environment without the parser. By the coordinator's ruling of 24 October 02:35, which
  amends that approval, the job now installs the parser, after elan and before the run of
  the checks, from the pinned `scripts/requirements-test_safe_push.txt`, the file that
  CI's `queue-integrity` job and the cadence's `safe-push-tests` job already install.
  Section 8 says that the check needs the parser, so that a contributor running the
  sequence or the pre-flight installs it once. The install keeps the checkout's root off
  the import path, by the coordinator's ruling of 24 October 03:35, which amends that of
  02:40: plain `python3 -m pip` puts the working directory first on the import path, so a
  `pip.py` at the checkout's root, which is no protected path, would run in place of pip
  before the checks, and could make the job pass with none of them run, as the review of
  this train showed. The train first did so with `-P`. CI then failed it at landing (pull
  request #434, run 40155222351): `tests/test_check_queue.py` requires every run of a
  Python module in CI to be isolated, from the runner's temporary directory, as
  `queue-integrity` installs the same file. So, as the coordinator asked on 24 October at
  19:45, the step now runs `python3 -I -m pip install -r
  "$GITHUB_WORKSPACE/scripts/requirements-test_safe_push.txt"` from `${{ runner.temp }}`:
  `-I` takes in `-P`, and nothing of the checkout is in the working directory either.
  That test's list of the jobs that run a module gains `check`, the job this train gives
  one.

  The test of the `check` job's shape allowed no setup step beyond checkout, Python and
  elan. By the coordinator's ruling of 24 October 02:40, as amended at 03:35 and 19:45, it
  now allows that one install, exactly that line, once, straight after elan, with no
  condition, environment or shell, from `${{ runner.temp }}`, the one working directory it
  allows, and on that step alone. Every case it refused before is still refused. Two kinds
  of message change: with elan removed, the refusal now reads "CI check setup prefix is
  incomplete before the parser's install", not "CI check setup prefix is incomplete before
  the first check"; and the three cases that name a planted step by its place (an unlisted
  action, and the checkout or the Python setup after the run) name a place one further on,
  since the job has one step more. Fourteen new planted cases are refused: the install of
  another requirements file, an extra package on the line, the install without `-I`, and
  the install with `-P` alone, each from the temporary directory and from the checkout;
  the install in the checkout, and in another directory; the install after the run of the
  checks, the install twice, the install before elan, and no install. With the test that
  decides each taken out, its case was seen to be accepted: the line's equality, for a
  changed line in the temporary directory; the directory's, for the install in the
  checkout or in another directory; both, for a changed line from the checkout; and for
  the last four, the guard of order or count that refuses it. The train is of class R5,
  since it changes the CI workflow.

  This entry approves the new file `checks/24-lane-condition.toml`, which runs the
  lane-condition test of `scripts/test_safe_push.py` in CI's `check` job at order 135.

  This entry approves the change to `.github/workflows/ci.yml`, whose `check` job gains
  one step that installs the pinned YAML parser from
  `scripts/requirements-test_safe_push.txt`, isolated and from the runner's temporary
  directory, before the run of the checks.

  This entry approves the change to `scripts/test_safe_push.py`, whose model of the
  `check` job allows that one install, exactly, after elan, from the runner's temporary
  directory, with fourteen planted refusals.

  This entry approves the change to `tests/test_check_queue.py`, whose list of the CI jobs
  that run a Python module, each isolated and from the runner's temporary directory, gains
  `check`.
