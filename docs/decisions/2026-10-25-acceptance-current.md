- **The acceptance checker refuses a stale build, and holds the committed report to the
  head it is released at (tooling,
  [#155](https://github.com/jackChallis/stoicheia/issues/155)).** Card #155, "Acceptance in
  CI: the full gate, its page, and a current report", has two of its finished-when items
  still open, and the coordinator's orders of 25 October 2026 assign them. This change meets
  the first, and gives the second its check and writes the regeneration into step 10, for
  the release's own pull request; the regeneration itself happens at the candidate. The
  switch of `ACCEPTANCE_GATE` to `full` stays with that pull request too. Nothing here
  changes a Lean file, a lock, a statement, a definition or a `--` line, and no refusal the
  checker had is loosened: this only tightens.

  First, a stale build. The checker asks Lean about the catalogues' names (B2 and E2) and
  runs checks that read the build, which is what `lake build` left and not the sources; a
  tree whose build was older than its sources was checked as if it were current. Now a
  checking run, before any check and before it writes anything, runs
  `lake build --no-build Elements Audit` in the repository's root. Lake decides what is
  stale by its traces, not by the times of files, and `--no-build` builds nothing, so the
  checker still changes nothing. Lake exits 0 when both targets are current, and 3 when one
  is not (`noBuildCode` in Lean 4.35's Lake), naming the first modules it would build; on
  this worktree, never built, it exited 3 at once. On exit 3 the checker prints the command,
  its exit, the last lines Lake printed and what to run (`lake build`, `lake build Audit`,
  then `lake env lean Certificate/Facts.lean`), and exits 2, "cannot begin", with no report
  and no verdicts written. Any other exit is not called a stale build: it is Lake unable to
  answer whether the build is current, a toolchain or lakefile problem, say (a lakefile it
  cannot read exits 1), and the checker says so, with the same lines, and exits 2 as well.
  So it does when there is a `lake` that cannot be started, and when Lake does not answer
  within ten minutes. Each of these goes to stdout, as the checker's other "cannot begin"
  messages do. When there is no `lake` to run at all, the run goes on as before, and the
  checks that need Lean say that they could not ask it. CI is unaffected: its `acceptance`
  job builds `Elements` and `Audit` and computes the certificate before each of its two
  runs, in the step "Build, and compute the certificate" for the pull request, and in "Check
  main against the checklist, with the pull request's checks" for main's worktree.

  Second, the committed report. A new mode, `--check-current`, runs no check, needs no Lean
  and writes nothing. It reads the report as HEAD holds it, through git, and not the working
  copy. It exits 0 when the report's revision is a commit that HEAD descends from and
  differs from in nothing but the report, when the report was a run of every item on files
  as committed, and when the worktree has no change, staged, unstaged or untracked, the
  report's own included. Otherwise it exits 1, naming each reason and what to do. A file the
  index marks so that git does not compare it with the worktree, assume-unchanged or
  skip-worktree (any tag but `H` from `git ls-files -v`), is such a reason too, for
  `git status` shows no change in it; and its git commands run with
  `GIT_NO_REPLACE_OBJECTS=1`, so that no `git replace` lets another commit's tree stand for
  the revision's. Files git ignores, by `.gitignore` or `.git/info/exclude` alike, are not
  counted. It exits 2 when it cannot begin: no git checkout with a commit, no report at
  HEAD, or a report that is not UTF-8, or has no generated marker on its first line, or no
  Revision or Run line. It takes no other option. HEAD is compared with the report's
  revision tree to tree, and not by the walk of first parents with which the report names
  its revision. That way the check holds on the head that `--merge` merges and, when main
  has not moved since, on main's merge commit of it too, where the walk stops at once, for
  that commit differs from its first parent in all that the release changed; when main moved
  first, the merge differs from the candidate in what main changed, and the check names
  those files. The walk itself, the generator's `revision()`, now runs `git diff` with
  `--no-renames`, as the check does, so that a commit moving a file onto the report's path
  is not taken for a change to the report alone. It is a release step and not a check of
  every pull request: every pull request's job has the build and the run, but only the
  release candidate is held to committing the regenerated report; on an ordinary pull
  request CI's ratchet recomputes the verdicts. Step 10 of
  [WORKFLOW](../WORKFLOW.md#10-how-a-book-is-made-and-released), section 10, now makes the
  acceptance report the third generated account made again at the release's head, the last
  of them and committed by itself, and has the coordinator run `--check-current` where the
  screen's own check runs.

  The checker's tests gain both. With a stand-in for `lake`, as the screen's tests use, a
  stale build, in lines of the form Lake prints that name Audit modules, as the card's case
  is a stale Audit build, stops the run with exit 2 before any check, saying so on stdout,
  with nothing written; so do Lake's exit 1, said to be Lake unable to answer and not a
  stale build, a `lake` that cannot be started, and Lake with no answer; a current build
  lets it go on; with no `lake` to run it goes on as before, on a real PATH without one too;
  and neither `--compare` nor `--check-current` asks Lake. On a repository of their own,
  with git's environment cleared, the cases of `--check-current` take every outcome above.
  Among them are a `--no-ff` merge of the candidate into an unmoved main, current at the
  candidate and at the merge, where `revision()` names the merge itself, and the same merge
  after main moved first, not current and naming the file main changed; a branch and a tag
  named as the report's digits, at a commit with the same files; a rename onto the report's
  path, which git's rename detection shows as the report alone, and one off it; a
  `git replace` of the revision; a file marked assume-unchanged or skip-worktree; a revision
  that names no commit; a Run line neither of every item nor `--quick`; and a report that is
  not UTF-8. Each was checked by mutation, in memory, with the script's source compiled
  under its own path and no file of the repository changed: without the guard; with no
  `lake` made a refusal, or any `OSError` taken for no `lake`; with every exit of Lake read
  as a stale build, or none; with the refusal on stderr; with the report's own change,
  untracked files, other files, a `--quick` run, a report of uncommitted changes, the
  history, the index's marks, or the test that the digits begin the commit they name,
  ignored; with renames detected, in the check or in `revision()`; with replacements read;
  with HEAD held to `revision()`'s walk exactly; with the reasons for a revision of no
  commit and a Run line of neither kind misstated; with a report that is not UTF-8 decoded
  leniently; and with the working copy read in place of HEAD's report: at least one new case
  failed each time. Unmutated, all pass, and the existing cases pass unchanged. The rename
  off the report's path is seen with or without `--no-renames`, for git pairs a rename only
  from a path deleted, and HEAD holds the report.

  This entry approves the change to `scripts/check_acceptance.py`, which asks Lake whether
  the build is current before a checking run and exits 2 when it is not or Lake cannot say,
  gains `--check-current`, its docstring saying both, and gives `revision()`'s `git diff`
  the option `--no-renames`.

  This entry approves the change to `tests/test_check_acceptance.py`, which gains the cases
  of a stale build and of `--check-current`, and one of `revision()` over a rename onto the
  report, with words on them in its docstring, its existing cases unchanged.

  This entry approves the change to `docs/ACCEPTANCE.md`, whose "Running it" now says how a
  stale build is refused and what `--check-current` does, and whose paragraph on the full
  gate says that the report is regenerated and committed at the release candidate, and
  `--check-current` passes there; its table of the limitations allowed is unchanged.
