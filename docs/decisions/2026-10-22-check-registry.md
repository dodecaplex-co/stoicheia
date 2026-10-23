- **The checks in a registry, one file each (tooling).** Card #229 found three lists that
  had to agree: the pre-flight's `CHECKS` in `scripts/safe_push.py`, the steps of CI's
  `check` job in `.github/workflows/ci.yml`, and the first command block of section 8 of
  [`docs/WORKFLOW.md`](../WORKFLOW.md). A train that added a check edited all three, in
  the same places as every other such train, and those lines conflicted again and again on
  21 October. Like #205 and #210, the card's remedy is one file per item.

  What changed. Each check of CI's `check` job is now a file of its own,
  `checks/<NN>-<slug>.toml`, which holds its order, its name, its job, its command (or
  `empty = true`, for the check that `git status --porcelain` prints nothing) and its line
  of section 8, with a comment on what it is for. `scripts/registry.py` is their one
  reader, and refuses the whole folder, naming the file, for an unknown or missing field,
  two entries sharing a name or an order, a command that is not a list of strings, a job
  other than `check`, or a file it cannot read. CI's `check` job keeps its name and its
  setup, then runs one step, `python3 scripts/run_checks.py --job check`, which runs that
  job's entries in order, each a named group of the log, and stops at the first that
  fails. `render.py` writes section 8's first block from the registry, between markers
  that the pre-flight's guards read as generated. The pre-flight's step 4 runs
  origin/main's registry, which origin/main's copy of `scripts/registry.py` reads out of
  Git from a temporary directory, and a line of the step says how many checks it runs and
  from which tree.

  What stays the same. The checks, their commands and their order. The negative tests, in
  CI's `negative` job and in the pre-flight's `NEGATIVE`, which the coordinator ruled out
  of this card's scope. CI's `model` job, whose command stays a list of the pre-flight's
  own beside `NEGATIVE`, since the registry holds the `check` job alone: on 22 October
  2026 the coordinator ruled that it stays built in, as `NEGATIVE` does. That list leaves
  out the job's second step, `results_check.py`, which only CI runs until it joins the
  list ([#378](https://github.com/jackChallis/stoicheia/pull/378)), and the tests name it
  as the job's one step CI alone runs. Every
  job's name, and so the ruleset's required checks. While origin/main holds no registry,
  as for the train that brings it, the pre-flight runs the sequence built into
  `scripts/safe_push.py`, the one every train was judged by before. The tests pin that
  list to one of their own, as they pin the `model` and negative lists, and never to the
  registry, which grows without it. A follow-up card,
  [#328](https://github.com/jackChallis/stoicheia/issues/328), removes the list, and the
  fallback to it, once the registry is on main. Until then a train that deleted both
  `checks/` and `scripts/registry.py` would, once merged, put every later pre-flight back
  on that frozen list, with only the step line that names the list to show it, though each
  file it deleted would be a protected path, named in its entry.

  Why it is safe. CI runs the pull request's registry, as it has always run the pull
  request's own copy of the workflow, and the `check` job is a required check of the pull
  request: a train that changes the registry changes the checks its own CI runs. Three
  things keep that safe. Every train that touches `checks/` is R3 or above, so its
  pre-flight runs main's whole registry on it, in both passes, whatever its CI runs. The
  change is protected: each registry file a train adds, removes or changes is named in a
  decision entry, and the pull request carries `security-review`. And the change judges
  later trains only once it has merged. The registry is a check input as well, so a change
  to it is kept apart from content the checks judge, as a change to a script is. The
  reader, `scripts/registry.py`, and the runner, `scripts/run_checks.py`, are R5 by
  `scripts/risk.py`, with the rest of the landing tool and CI: main's reader decides the
  pre-flight's sequence, and the runner is CI's `check` job. The pre-flight holds the
  names of the checks itself, whatever main's reader allows: only the check that `git
  status --porcelain` prints nothing bears its name, and every other check is named by its
  command's words, so that no command can bear a name whose failure the pre-flight passes
  over as stale pages. A registry at origin/main that cannot be read, or whose reader
  fails, prints no list or gives no check, refuses the pre-flight: it never runs an empty
  list. Section 8 of `docs/WORKFLOW.md` now says all of this, and its section 10 says how
  to add a check.

  What it makes easier. Adding a check is now a change of class R3: one new file in
  `checks/`, section 8's block as `render.py` regenerates it, and an entry naming the
  file. Such a train touches neither `scripts/safe_push.py` nor the CI workflow, each of
  class R5, and the tests need no change for it: a test adds a file to a copy of the tree,
  renders the block, and finds the copy agreeing as the tree does. The new check runs in
  its own pull request's CI, and joins the pre-flight once it merges.

  What it gives up. On GitHub the `check` job shows one step where it showed seventeen:
  each check is a group of that step's log, and a failure names its check there and in an
  error annotation. And a registry at origin/main that could not be read would hold every
  train, of every class, its own repair among them, since step 3 reads the registry in
  every class, so that repair would need the owner's leave to land without the pre-flight.
  `render.py` and CI's run of the registry load the reader from `scripts/` and read the
  worktree, so they cannot show that the reader works as the pre-flight runs it, alone and
  out of Git: a reader that imports a module beside it passes both. So step 3 of the
  pre-flight, in every class, reads the commit's own registry with the commit's own reader
  as a later pre-flight will read it once the commit is main's, and refuses the commit,
  naming why, when it cannot; it skips only a commit that holds neither the registry nor
  its reader. The reader must stay one self-contained file of the standard library, and
  its docstring says so.

  This entry approves `scripts/registry.py`, a new file: the registry's reader, from the
  worktree or from a revision in Git, and the source of section 8's block; it must stay
  self-contained, of the standard library alone.

  This entry approves `scripts/run_checks.py`, a new file, which runs one job's checks as
  the worktree's registry lists them, for CI's `check` job.

  This entry approves `scripts/safe_push.py`, whose step 4 takes the `check` job's
  sequence from origin/main's registry with origin/main's reader and refuses one it cannot
  read or whose names it does not hold, keeps its old sequence as the stand-in while
  origin/main has none, and counts `checks/` among its protected paths, its check inputs
  and, for section 8's block, its generated pages; and whose step 3 reads the commit's own
  registry with the commit's own reader, as a later pre-flight will.

  This entry approves `scripts/test_safe_push.py`, whose tests of the sequence now hold
  the registry, section 8's block and the one step of CI's `check` job to one another, pin
  the built-in list to a list of their own, add a check to a copy of the tree with no
  change to the harness, keep every refusal of a skipped, suppressed or overridden step,
  and add a class of tests, `Registry`, beside new cases in `RiskPreflight` and
  `ProtectedPaths`, step 3's reading of the commit's registry among them.

  This entry approves `scripts/render.py`, which writes section 8's first command block
  from the registry and refuses a registry its reader refuses.

  This entry approves `scripts/risk.py`, whose table classes `checks/` R3, and
  `scripts/registry.py` and `scripts/run_checks.py` R5.

  This entry approves `tests/test_risk.py`, which holds those classes, and the class of a
  train that adds one check.

  This entry approves `scripts/negative_tests.py`, whose `count_source_copy` copies the
  files of `checks/` beside the scripts, so that `render.py` finds the registry in its
  copy before they are committed.

  This entry approves `.github/workflows/ci.yml`, whose `check` job keeps its setup and
  runs its checks by one step of `scripts/run_checks.py`, its other jobs as they were.

  This entry approves `checks/README.md`, which says what a file of the registry holds and
  how to add one.

  This entry approves `checks/01-lake-build.toml`, the check `lake build`.

  This entry approves `checks/02-lake-build-audit.toml`, the check `lake build Audit`.

  This entry approves `checks/03-lake-build-staging.toml`, the check `lake build Staging`.

  This entry approves `checks/04-facts.toml`, the check that computes the certificate.

  This entry approves `checks/05-test-certificate.toml`, the certificate's own tests.

  This entry approves `checks/06-check-kernel.toml`, the kernel's replay and its
  self-test.

  This entry approves `checks/07-heath.toml`, the check of the contracts.

  This entry approves `checks/08-check-fidelity.toml`, the fidelity check.

  This entry approves `checks/09-test-check-style.toml`, the style check's own cases.

  This entry approves `checks/10-test-release-gate.toml`, the release gate's cases.

  This entry approves `checks/11-test-jev-models.toml`, the Jev client's model check.

  This entry approves `checks/12-jev-self-test.toml`, the Jev client's self-test.

  This entry approves `checks/13-test-screen.toml`, the overlap screen's cases.

  This entry approves `checks/14-test-acceptance-limits.toml`, the cases of item P3.

  This entry approves `checks/15-check-style.toml`, the style check.

  This entry approves `checks/16-render.toml`, the render of the pages.

  This entry approves `checks/17-clean-worktree.toml`, the check that the worktree is
  clean after them.

  This entry approves `checks/18-check-links.toml`, the check of links and anchors.

  This entry approves `checks/19-sweep-self-test.toml`, the citation sweep's self-test,
  which runs in the `check` job since #356.

  This entry approves `checks/20-sweep.toml`, the citation sweep's listing of candidates.

  This entry approves `checks/21-check-queue-tree.toml`, the merge queue judge's `--tree`
  check that the decisions page repeats no dated heading, which
  [#383](https://github.com/jackChallis/stoicheia/pull/383) put in the check job after the
  worktree check and before the links check, where its order of 175 keeps it.

  On 22 October 2026 the coordinator ruled that WORKFLOW section 8's command block between
  the `<!-- checks -->` markers is generated output, and that a train that changes
  `checks/` commits it regenerated with `render.py`, as for any generated output the train
  causes; AGENTS.md lists the region with that rule, in this change.
