- **The registry of checks is ruled before it comes
  ([#229](https://github.com/jackChallis/stoicheia/issues/229)).** The train that brings
  the registry of checks, one file per check under `checks/`, is judged by origin/main's
  harness, which did not know the folder: it took the registry's files for content the
  checks judge, and origin/main's own checks failed on them (its risk table's audit found
  them unruled), so the pre-flight kept the train apart as a check changed together with
  what it checks. So this change, landed first, gives the folder its place in the checks
  before any file of it exists: `checks/` is a protected path and a check input, and its
  files are of risk class R3, while the registry's reader and runner, `scripts/registry.py`
  and `scripts/run_checks.py`, are R5, as `scripts/risk.py` is. Nothing else changes, and
  no file of these names exists yet.

  This entry approves the change to `scripts/safe_push.py`, whose PROTECTED and
  CHECK_INPUTS now hold `checks/`.

  This entry approves the change to `scripts/risk.py`, which rules `checks/*` R3 and the
  registry's reader and runner R5.

  This entry approves the change to `tests/test_risk.py`, which pins those classes, and
  that adding a check file with WORKFLOW's regenerated block and its decision entry is R3.
