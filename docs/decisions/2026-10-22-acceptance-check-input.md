- **`docs/ACCEPTANCE.md` is a check input and a protected path
  ([#249](https://github.com/jackChallis/stoicheia/issues/249)).** ACCEPTANCE's table of
  the limitations allowed and `scripts/check_acceptance.py`'s `ALLOWED_LIMITS` are tied
  by `tests/test_acceptance_limits.py`, so an allowance added or removed changes both,
  and each half fails that test alone. To the pre-flight, `docs/ACCEPTANCE.md` was
  content the checks judge, so a pull request changing both was a check change together
  with what it checks, and keep_apart refused it: a deadlock for #214's removal of
  III.16's and III.31's allowances, and for the last train of #116. Now
  `docs/ACCEPTANCE.md` is one of safe_push's `CHECK_INPUTS`, and so origin/main's copy
  judges the commit and a change to it needs its own copy to pass too; it is one of its
  protected paths, so a change to it needs a new line in the decisions record naming it
  and the label `security-review`; and it is no longer judged content, so the table and
  the check change together as one check change. `scripts/risk.py` classes it R3,
  Checks, where it was R1 by its row of documents. This adds to what the pre-flight
  guards and takes nothing from it. The lane's own `risk.py` loads main's
  `scripts/risk.py` and holds no table, so it takes the new class when this lands.

  This entry approves the change to `scripts/safe_push.py`, whose `PROTECTED` and
  `CHECK_INPUTS` now hold `docs/ACCEPTANCE.md`.

  This entry approves the change to `scripts/risk.py`, which classes `docs/ACCEPTANCE.md`
  R3 among the checks and no longer R1.

  This entry approves the change to `scripts/test_safe_push.py`, whose protected-paths
  test names `docs/ACCEPTANCE.md` as protected and a check input, never judged, and whose
  new test commits the table, the check and its test together and finds nothing judged
  and nothing kept apart, while a page of the edition beside them is kept apart.

  This entry approves the change to `tests/test_risk.py`, whose rows class
  `docs/ACCEPTANCE.md` R3, a file beside it R0, and `docs/STYLE.md` still R1.
