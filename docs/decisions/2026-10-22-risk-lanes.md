- **Risk lanes: CI's checks follow a pull request's risk class (tooling).** On 22 October
  2026 the owner decided that the checks a change must pass follow its risk, and that its
  risk is determined from its files before it lands: "if trains can split into lower risk
  territories they ship faster"; "we need to tag that risk up front. But clearly determine
  the risk."; and "tags should be on Github. Documentation should clearly say how to
  handle. CI/CD should manage and be appropriate." Card #276 is the coordinator's record
  of the decision. This entry records its first part, CI's gating by class; the labels on
  GitHub and the full guide in WORKFLOW follow in a later change.

  `scripts/risk.py` is now the one source of the classes: R0 (docs), R1 (text and
  records), R2 (proofs), R3 (checks), R4 (foundations) and R5 (the landing tool and CI).
  It holds an ordered table in which a file takes the class of the first rule that matches
  it, and R5 when no rule does, and a change takes the highest class among its files. The
  table is the one drawn up for the card, with three files added: the classifier itself at
  R5, since it decides which checks run; and at R4 `lakefile.lean`, a build file that Lake
  would read before `lakefile.toml`, and the formal model's kernel check, which the
  `formal-model` job runs; and `.gitignore` and `.gitattributes`, at the root or below it,
  are raised from R0 to R3, since a rule of either can hide a file from the whole-worktree
  check below or change how Git reads one. Its audit finds a rule for every tracked file.

  CI's new first job, `risk`, runs main's copy of the classifier over what the pull
  request's merge commit changes on main. A push to main is R5; a push to another branch
  is classified as its pull request is, by main's copy against main, so that the branch's
  own run, which the merge gate also waits for, runs no more than the pull request's. The
  `check`, `model` and `acceptance` jobs run in full for every class. `negative` runs in
  full for R3, R4 and R5, and `formal-model` for R4 and R5, the classes of every change to
  `model/`, to the axiom lock and to the model's kernel check; for a lower class each
  passes at once and says why in its log. The `check` job also now requires, after the
  build and the render, that `git status --porcelain` over the whole worktree print
  nothing, as the pre-flight already requires: that covers the generated pages, as the
  narrower form did, and every other file a check might leave changed or new.

  Why this is safe. The five checks that main's ruleset requires keep their names
  (`check`, `model`, `negative`, `formal-model` and `acceptance`), so GitHub's settings
  need no change. A pull request of R0, R1 or R2 can change nothing under `.github/` or
  `scripts/`, nor the classifier, so main's workflow and main's classifier judge it; one
  of R3 or R4 may change scripts, but neither of the other two. A gated job fails, and is
  never skipped, when `risk` fails or is cancelled, for GitHub would take a skipped
  required check as passed. Until main holds the classifier, the pull request that adds it
  is classified by its own copy, and it changes `.github/`, so it is R5 by either. The
  negative tests still run on every pull request of R3 and above, and the formal model on
  every one of R4 and above; every push to main runs both in full, after each merge; and
  the cadence workflow now runs both on main every six hours, beside the safe_push tests,
  where a red run opens or updates the issue labelled `blocks-release` that holds the
  release.

  What this gives up, as the owner decided. Skipping the negative tests on pull requests
  of R0 to R2 takes those tests off those pull requests' merge path, and the formal model
  comes off the merge path of R0 to R3. A text or proof change can still break them: the
  negative tests plant their breaks in I.1 and in other content, and the formal model's
  `Check` library imports `Elements.BookI.Prop07` and `Elements.Figure.Circles`, with what
  they import. The cadence shows such a break within six hours, and the release waits for
  its repair.

  This entry approves the change to `.github/workflows/ci.yml`: the new `risk` job, the
  `negative` and `formal-model` jobs gated by its class, and the whole-worktree check in
  the `check` job.

  This entry approves the change to `.github/workflows/safe-push-tests.yml`, which gains
  two jobs, `negative` and `formal-model-kernel`, each with leave to read the repository
  alone, and a report that names every job that was red.

  This entry approves the new `scripts/risk.py`, the classifier.

  This entry approves the new `tests/test_risk.py`, which tests the classifier without
  Lean.

  This entry approves the change to `scripts/negative_tests.py`, which runs the
  classifier's tests beside its other regressions, before it plants anything.

  This entry approves the change to `scripts/test_safe_push.py`, whose tests pin the
  whole-worktree form of the check and refuse one narrowed to a list of paths.

  This entry approves the change to `tests/test_decision_entries.py`, whose docstring now
  says which runs of CI's `negative` job run it.
