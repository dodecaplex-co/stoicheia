- **Risk lanes: CI's checks follow a pull request's risk class (tooling).** On 22 October
  2026 the owner decided that the checks a change must pass follow its risk, and that its
  risk is determined from its files before it lands: "if trains can split into lower risk
  territories they ship faster"; and "tags should be on Github. Documentation should
  clearly say how to handle. CI/CD should manage and be appropriate." On 22 October 2026
  the owner also asked that every train's risk be tagged up front and clearly determined.
  Card #276 is the coordinator's record of the decision. This entry records its first
  part, CI's gating by class; the labels on GitHub and the full guide in WORKFLOW follow
  in a later change.

  `scripts/risk.py` is now the one source of the classes: R0 (docs), R1 (text and
  records), R2 (proofs), R3 (checks), R4 (foundations) and R5 (the landing tool and CI).
  It holds an ordered table in which a file takes the class of the first rule that matches
  it, and R5 when no rule does, and a change takes the highest class among its files. The
  table is the one drawn up for the card, with three files added: the classifier itself at
  R5, since it decides which checks run; `lakefile.lean` at R4, a build file that Lake
  would read before `lakefile.toml`; and the formal model's kernel check at R4, since the
  `formal-model` job runs it. Two kinds of file are also raised, from R0 to R3:
  `.gitignore` and `.gitattributes`, at the root or below it, since a rule of either can
  hide a file from the whole-worktree check below or change how Git reads one. Its audit
  finds a rule for every tracked file.

  CI's new first job, `risk`, runs main's copy of the classifier, never the change's own,
  over what the pull request's merge commit brings to main: the pull request's own run is
  classed exactly, from GitHub's merge commit, and a checkout that is not that merge of
  the pull request's head is R5. A pull request whose run starts with the `release` label
  is R5, and so are a pull request into any branch but main, a push to main, a tag, every
  other event, and a change whose base holds no classifier; a label can only raise the
  class. The label is read from the event that started the run, and `git safe-push` adds a
  pull request's labels after it pushes, so a label given with that push counts from the
  next push; main's run after the merge runs every job in full; and requiring an R5 run at
  a release pull request's head is left to the merge gate, in a later part of #276. A push
  to another branch is classified by main's copy against main, from where the branch left
  it, and the merge gate waits for that run as well as the pull request's own. The
  `check`, `model` and `acceptance` jobs run in full for every class. `negative` runs in
  full for R3, R4 and R5. `formal-model` runs in full for R4 and R5, the classes of every
  change to `model/`, to the axiom lock and to the model's kernel check, and for a change
  of any class to a file of the main package that the formal model imports, directly or
  through others. The classifier finds those files from the import lines of the model's
  own files, at both ends of the change, so the set follows the imports as they change;
  today it holds `Elements/BookI/Prop07.lean`, `Elements/BookI/Prop13.lean` and
  `Elements/Figure/Circles.lean`, among others. It reads those lines by a narrow grammar,
  and fails closed rather than try to match Lean's, which reads more: while any file among
  them, at either end of the change, has a header it cannot read cleanly (a module part
  `«.»`, `«..»` or `«»`, a letter or symbol past ASCII, an `import` with no module after
  it), or while the tree holds a `.gitattributes` anywhere (an encoding or filter there
  can make the text Lean reads from the checkout differ from the text Git holds, which the
  reader reads), `formal-model` runs in full for every change, and the log names the file.
  So a header that Lean reads otherwise can only widen the set. It also fails closed on an
  import that names a module for which the tree holds no file at the usual path, unless
  the module's root is Check, Model, Mathlib, Lean, Init or Std
  ([#296](https://github.com/jackChallis/stoicheia/issues/296)): the /no-mistakes pipeline
  built that, and the captain kept it after reading it line by line, with the
  coordinator's agreement of 22 October, since it only makes the formal model run more
  often; on this tree every import of the model resolves, so nothing falls to it.
  Otherwise a gated job passes at once and says why in its log. The `check` job also now
  requires, after the build and the render, that `git status --porcelain` over the whole
  worktree print nothing, as the pre-flight already requires: that covers the generated
  pages, as the narrower form did, and every other file a check might leave changed or
  new.

  Why this is safe. The five checks that main's ruleset requires keep their names
  (`check`, `model`, `negative`, `formal-model` and `acceptance`), so GitHub's settings
  need no change. A pull request of R0, R1 or R2 can change nothing under `.github/` or
  `scripts/`, nor the classifier, so main's workflow and main's classifier judge it; one
  of R3 or R4 may change scripts, but neither of the other two. A gated job fails, and is
  never skipped, when `risk` fails or is cancelled, for GitHub would take a skipped
  required check as passed. The negative tests still run in CI on every pull request of R3
  and above, and in the pre-flight of `git safe-push` on every pull request; the formal
  model on every one of R4 and above, on every one that touches a file the model imports,
  and on every one while a header among those files cannot be read; both on a pull request
  whose run starts with the `release` label; every push to main runs both in full, after
  each merge; and the cadence workflow now runs both on main every six hours, beside the
  safe_push tests, where a red run opens or updates the issue labelled `blocks-release`
  that holds the release.

  What this gives up, as the owner decided. Skipping the negative tests on pull requests
  of R0 to R2 takes those tests off those pull requests' merge path. A text or proof
  change can still break them, for they plant their breaks in I.1 and in other content:
  the cadence shows such a break within six hours, and the release waits for its repair.
  The formal model gives up nothing on the merge path for its own inputs: it leaves the
  merge path only of a change of R0 to R3 that touches none of them, while the classifier
  reads every header among them.

  Left to a later part of #276. The card's rule that a red cadence run holds only the
  classes it guards is not built here: for now any red job of the cadence opens or updates
  the one `blocks-release` issue, which holds the release.

  This entry approves the change to `.github/workflows/ci.yml`: the new `risk` job, the
  `negative` and `formal-model` jobs gated by what it finds, and the whole-worktree check
  in the `check` job.

  This entry approves the change to `.github/workflows/safe-push-tests.yml`, which gains
  two jobs, `negative-tests` and `formal-model-kernel`, each with leave to read the
  repository alone, and a report that names every job that was red.

  This entry approves the new `scripts/risk.py`, the classifier, which also finds the
  files the formal model imports.

  This entry approves the new `tests/test_risk.py`, which tests the classifier without
  Lean.

  This entry approves the change to `scripts/negative_tests.py`, which runs the
  classifier's tests beside its other regressions, before it plants anything, and whose
  plant of a stale page reads the whole worktree's status, as CI's check now does.

  This entry approves the change to `scripts/test_safe_push.py`, whose tests pin the
  whole-worktree form of the check and refuse one narrowed to a list of paths.

  This entry approves the change to `tests/test_decision_entries.py`, whose docstring now
  says which runs of CI's `negative` job run it.
