- **Checks scaled to risk: the pre-flight by class, and CI once per commit (tooling).** On
  22 October 2026, asked whether trains of R0 to R2 could skip the heavy local pre-flight,
  the owner answered: "Yes we should not be spending the same amount of time on high risk
  and low risk. It's either overkill or underkill." Before that, the same day: "I thought
  we should go a lot faster now." Card #292 is the coordinator's record of the decision,
  and #301, the release's need for a green run of the safe_push tests at its head, joined
  the same train. Card #276 and its entry,
  [2026-10-22-risk-lanes](2026-10-22-risk-lanes.md), covered the first part:
  `scripts/risk.py`, the classes, and CI's `negative` and `formal-model` jobs gated by
  them.

  Why. #290, a records train of class R1 that added 8 lines to 4 review records, took 33
  minutes to land: 17 on the coordinating Mac and 16 on GitHub, where CI ran twice for the
  one commit, on the push and on the pull request. The pre-flight's log for its head shows
  where the Mac's time went: steps 1 to 3, the scan and the guards, took about 10 seconds,
  and step 4 took 945, 647 of them the negative tests with their build.

  What changed. `git safe-push` now takes the class of the commit it checks from
  origin/main's copy of `scripts/risk.py`, read out of Git and run from a temporary
  directory, on `git diff origin/main...<commit>`, as CI's `risk` job runs it: never the
  commit's own copy, and never a label, save that a pull request labelled `release`
  (given with `--label`, or on the open pull request, which the pre-flight now reads
  before its checks) is R5. A label can only raise the class. Any failure to compute it
  is R5, and so is an origin/main with no classifier. The class and why are a step line
  at the head of step 4, which reaches the summary in the pull request, and the record
  keeps it as `class`. For R0, R1 and R2, steps 1 to 3 run as before, every guard and
  scan with them, and step 4 (the builds, `Facts.lean`, the kernel's self-test, the
  model's run, the rest of section 8 and the negative tests) is skipped, with one line
  saying the class and that CI runs those checks before the merge. For R3, R4 and R5 the
  pre-flight is the full one, unchanged. At `--merge`, a record that left step 4 to CI
  stands in for it only while the class, recomputed then by origin/main's classifier for
  that head against that base, is still R0 to R2. A pull request labelled `release`
  merges only on a record of the full pre-flight of its head, and only with a green run
  of `.github/workflows/safe-push-tests.yml` at that exact head, in which every job passed
  but `report`, which runs only for a red run on main (#301); `--merge` refuses
  otherwise, naming what is missing. CI now runs on a push to main alone, with the pull
  request's own events, so each commit of a pull request runs once.

  Why this is safe. A change of R0 to R2 can change no check, no script, no workflow and
  not the classifier, for the table puts `scripts/`, `tests/`, `.github/` and
  `scripts/risk.py` at R3 or above. The pre-flight does not take the table's word alone:
  a change to a check input or to a protected path that is not content the checks judge
  takes the full path whatever its class, so the rule that keeps a check change apart
  from what it checks cannot be needed on the short path. The classifier that judges is
  origin/main's, so a change cannot lower its own class. CI's `check` job runs the section
  8 sequence on every pull request, of every class, before the merge, beside its `model`
  and `acceptance` jobs, on GitHub's merge of the head into main, whose tree is the
  head's, since origin/main must be an ancestor of the head; and `--merge` waits for
  those checks green. Main's run after each merge runs every job in full, the cadence
  runs the suite, the negative tests and the formal model on main every six hours, and a
  release runs everything at its own head. The kernel's self-test stays in CI's `check` job for every
  class: the pre-flight skips it for R0 to R2, CI does not, since the tests of
  `scripts/test_safe_push.py` refuse a condition on any step of that job.

  What it gives up. For a change of R0 to R2, the negative tests now run nowhere before
  the merge: until now the pre-flight ran them on every pull request, and CI's `negative`
  job already passed at once for those classes. A text, record or proof change that
  breaks one of them, as one can, since they plant their breaks in content, is found
  after it lands, by main's run or within six hours by the cadence, and the release waits
  for its repair. A build that fails, or a check that the guards do not repeat, is found
  by CI after the push instead of by the pre-flight before it, so such a train is pushed
  and its pull request opened before its failure shows. And a branch pushed without a
  pull request has no CI run, nor has a tag: `git safe-push` opens or updates the pull
  request with every push of its branch, and a tag is made on main, after its merge's
  run.

  This entry approves the change to `scripts/safe_push.py`: the class from origin/main's
  classifier, the short path for R0 to R2 with its fallback to the full one, the class
  in the record and the summary, the record's use at `--merge`, and the release's two
  new needs.

  This entry approves the change to `scripts/test_safe_push.py`: a new class of tests,
  `RiskPreflight`, planted commits of each class and each failure; a stand-in for
  GitHub's runs of the safe_push tests; the classifier among the files of the harness
  under test; and the commits of the tests that need the full pre-flight's record, a
  release's or a merge's that reads it, made R3 by a line in `docs/WORKFLOW.md`, each
  checking what it checked before.

  This entry approves the change to `.github/workflows/ci.yml`: CI runs on a push to main
  and on the pull request's events, no longer on the push of another branch or a tag;
  the `risk` job loses its case for a branch's push; and the comments and the log line of
  `negative` say where the negative tests run now.
