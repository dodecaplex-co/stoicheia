- **The acceptance checker refuses a stale build, and holds the committed report to the
  head it is released at (tooling,
  [#155](https://github.com/jackChallis/stoicheia/issues/155)).** Card #155, "Acceptance
  in CI: the full gate, its page, and a current report", has two of its finished-when
  items still open, and the coordinator's orders of 25 October 2026 assign them; this
  change meets both. The switch of `ACCEPTANCE_GATE` to `full` stays with the release's
  own pull request. Nothing here changes a Lean file, a lock, a statement, a definition or
  a `--` line, and no refusal the checker had is loosened: this only tightens.

  First, a stale build. The checker asks Lean about the catalogues' names (B2 and E2) and
  runs checks that read the build, which is what `lake build` left and not the sources; a
  tree whose build was older than its sources was checked as if it were current. Now a
  checking run, before any check and before it writes anything, runs
  `lake build --no-build Elements Audit` in the repository's root. Lake decides what is
  stale by its traces, not by the times of files, and `--no-build` builds nothing, so the
  checker still changes nothing. Lake exits 0 when both targets are current, and 3 when
  one is not, naming the modules it would build; on this worktree, never built, it
  exited 3 at once. On any exit but 0 the checker prints to stderr the command, its exit,
  the last lines Lake printed and what to run (`lake build`, `lake build Audit`, then
  `lake env lean Certificate/Facts.lean`), and exits 2, "cannot begin", with no report and
  no verdicts written. When Lake does not answer within ten minutes it exits 2 as well.
  When there is no `lake` to run at all, the run goes on as before, and the checks that
  need Lean say that they could not ask it. CI is unaffected: its `acceptance` job builds
  `Elements` and `Audit` and computes the certificate before each of its two runs, in the
  step "Build, and compute the certificate" for the pull request, and in "Check main
  against the checklist, with the pull request's checks" for main's worktree.

  Second, the committed report. A new mode, `--check-current`, runs no check, needs no
  Lean and writes nothing. It reads the report as HEAD holds it, through git, and not the
  working copy. It exits 0 when the report's revision is a commit that HEAD descends from
  and differs from in nothing but the report, when the report was a run of every item on
  files as committed, and when the worktree has no change, staged, unstaged or untracked,
  the report's own included. Otherwise it exits 1, naming each reason and what to do. It
  exits 2 when it cannot begin: no git checkout with a commit, no report at HEAD, or a
  report without the generated marker on its first line or without its Revision or Run
  line. It takes no other option. HEAD is compared with the report's revision tree to
  tree, and not by the walk of first parents with which the report names its revision.
  That way the check holds on the head that `--merge` merges and on main's merge commit of
  it too, where the walk stops at once, for that commit differs from its first parent in
  all that the release changed. It is a release step and not a check of every pull
  request, since the report needs the full build and run, which only the release
  candidate's head is held to; on an ordinary pull request CI's ratchet recomputes the
  verdicts. Step 10 of [WORKFLOW](../WORKFLOW.md#10-how-a-book-is-made-and-released),
  section 10, now makes the acceptance report the third generated account made again at
  the release's head, the last of them and committed by itself, and has the coordinator
  run `--check-current` where the screen's own check runs.

  The checker's tests gain both. With a stand-in for `lake`, as the screen's tests use, a
  stale build stops the run with exit 2 before any check, with nothing written; a current
  one lets it go on; with no `lake` to run it goes on as before, on a real PATH without one
  too; and neither `--compare` nor `--check-current` asks Lake. On a repository of their
  own, with git's environment cleared, the cases of `--check-current` take every outcome
  above. Each was checked by mutation, in memory, with the script's source compiled under
  its own path and no file of the repository changed: without the guard, with no `lake`
  made a refusal, with the report's own change, untracked files, other files, a `--quick`
  run, a report of uncommitted changes or the history ignored, and with the working copy
  read in place of HEAD's report, at least one new case failed each time; unmutated, all
  pass, and the existing cases pass unchanged.

  This entry approves the change to `scripts/check_acceptance.py`, which asks Lake whether
  the build is current before a checking run and exits 2 when it is not, and gains
  `--check-current`, its docstring saying both.

  This entry approves the change to `tests/test_check_acceptance.py`, which gains the cases
  of a stale build and of `--check-current`, with words on them in its docstring, its
  existing cases unchanged.

  This entry approves the change to `docs/ACCEPTANCE.md`, whose "Running it" now says how a
  stale build is refused and what `--check-current` does, and whose paragraph on the full
  gate says that the report is regenerated and committed at the release candidate, and
  `--check-current` passes there; its table of the limitations allowed is unchanged.
