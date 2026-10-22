- **The cadence's red report survives a long list of failures
  ([#300](https://github.com/jackChallis/stoicheia/issues/300)).** The report step of
  `.github/workflows/safe-push-tests.yml` runs under bash with `-e` and `pipefail`, and
  kept the first hundred failing tests with `head -n 100`. With a long list, `head` stops
  reading, `printf` meets a closed pipe and is killed, and `pipefail` ends the step before
  the issue labelled `blocks-release` is opened: the very run that most needs reporting
  would report nothing. The step now keeps them with `sed -n '1,100p'`, which reads all
  its input, and nothing else in the step changes.

  This entry approves the one-line change to `.github/workflows/safe-push-tests.yml`, with
  a comment saying why.

  This entry approves the new class `CadenceReport` in `scripts/test_safe_push.py`, which
  runs the step's own script as GitHub runs it, with a stand-in for `gh`, on a log of a
  thousand failures of nearly three hundred characters each: the issue opens with the
  first hundred; three failures are listed whole; and the old `head` form ends the step
  with no issue, so the test would catch its return.
