- **`docs/ACCEPTANCE.md` is a check input and a protected path
  ([#249](https://github.com/jackChallis/stoicheia/issues/249)).** ACCEPTANCE's table of
  the limitations allowed and `scripts/check_acceptance.py`'s `ALLOWED_LIMITS` are tied
  by `tests/test_acceptance_limits.py`, so an allowance added or removed changes all
  three, and each half fails that test alone. To the pre-flight, `docs/ACCEPTANCE.md` was
  content the checks judge, so a pull request changing them together was a check change
  together with what it checks, and keep_apart refused it: a deadlock for #214's removal
  of III.16's and III.31's allowances, and for #116's allowance train. Now
  `docs/ACCEPTANCE.md` is one of safe_push's `CHECK_INPUTS`, and so origin/main's copy
  judges the commit and a change to it needs its own copy to pass too; it is one of its
  protected paths, so a change to it needs a new line in the decisions record naming it
  by its whole path and the label `security-review`; and it is no longer judged content,
  so the table and the check change together as one check change. `scripts/risk.py`
  classes it R3, Checks, where it was R1 by its row of documents, so a change to it takes
  the full pre-flight. It takes one thing from keep_apart: ACCEPTANCE no longer counts as
  content the checks judge, as the guides and the other check inputs do not, so a check
  change that fails with origin/main's copies and also edits it is noted for the security
  review where it was refused. In its place a change to it needs a decisions line, the
  label `security-review` and the full pre-flight, and its own copy must pass. The
  coordinator's landing tools outside the repository read the classes from
  `scripts/risk.py` and hold no table of their own, so they take the new class when this
  lands.

  This entry approves the change to `scripts/safe_push.py`, whose `PROTECTED` and
  `CHECK_INPUTS` now hold `docs/ACCEPTANCE.md`.

  This entry approves the change to `scripts/risk.py`, which classes `docs/ACCEPTANCE.md`
  R3 among the checks and no longer R1.

  This entry approves the change to `scripts/test_safe_push.py`, whose protected-paths
  test names `docs/ACCEPTANCE.md` as protected and a check input, never judged, and whose
  new test commits the table, the check and its test together and finds nothing judged
  and nothing kept apart, while a page of the edition beside them is kept apart.

  This entry approves the change to `tests/test_risk.py`, whose rows class
  `docs/ACCEPTANCE.md` R3 and a file beside it R0.
