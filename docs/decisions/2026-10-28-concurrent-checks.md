- **Step 4's checks that may run beside each other run concurrently (checks,
  [#608](https://github.com/dodecaplex-co/stoicheia/issues/608)).** Card #608 is the
  coordinator's record of the second step in making the pre-flight faster, after the
  negative tests' workers (#607). Once the build and `Certificate/Facts.lean` are done,
  step 4 ran about twenty checks one after another, though most of them only read the
  tree: on the Mac, `tests/test_certificate.py` alone takes about 78 seconds and the kernel
  self-test about 70.

  The registry gains two optional fields. `concurrent = true` declares that a check writes
  nothing in the worktree but Python's ignored bytecode, reads nothing another check
  writes, has no limit timed by the clock tight enough to fail on a busy machine, and does
  not itself fill the machine; the reader accepts `true` alone, and never for the check
  with `empty`. `after`, with `concurrent` only, names earlier checks that must have ended
  before the check starts, so that a check's own test still runs before its verdict. A
  check without the field runs alone, after every earlier check has ended and before any
  later one starts, so every new check runs alone until a reviewed change declares it. The
  reader's JSON carries both fields; a copy of `scripts/safe_push.py` from before this
  change reads only an entry's name, command, empty and job, and so ignores them.

  The declarations follow a read-only audit of every check at c592c1664: seventeen
  checks of the registry are declared concurrent, with the model job beside them in
  `scripts/safe_push.py`, and `check_paths.py --self-test` and
  `check_superposition_pins.py` each wait for their own tests. The three builds,
  `Facts.lean`, `render.py` and the clean-tree check write or judge the tree, and run alone.
  So do `scripts/heath.py`, whose plants each have half a second by the clock, and
  `tests/test_check_style.py`, one of whose cases has two seconds: raising either limit
  would weaken a check, so they are scheduled alone instead. `sweep_citations.py` already
  runs one Lean per core, and runs alone too. The negative job is unchanged. Each check's
  file says in one comment line why it is concurrent or runs alone.

  The pre-flight runs concurrent checks that come next to each other in order as a group,
  up to `STOICHEIA_CHECK_WORKERS` at once, and never more than half the machine's cores;
  the check list line says the number and the cap, and any other value than a whole number
  from 1 fails it. Every check is still started by the harness's one launcher, `run()`, as
  every command it starts is: at more than one worker, each check of a group on a thread
  of its own. Unset, empty or 1, the variable means one, and every check runs as before
  this change, one after another on the harness's own thread, with only the guard below
  added around each group; so nothing runs concurrently until the lane sets it. The report
  and the logs are written in the registry's order, by the harness's own thread, each with
  its own time and output, as when the checks ran one at a time. Where a failure refuses,
  no check starts after one fails, every running check is waited for, and the refusal
  names the first failing check in the registry's order, nothing after it reported or
  logged; where a failure is noted, every check runs and is noted in order, and the
  main-checks cache records each in order. An interrupt (Ctrl-C, SIGTERM or SIGHUP), or
  any other exception, starts no further check and waits for every check already running,
  at most the number of workers, to end before the pass cleans or removes its worktree,
  even through a further interrupt. Those checks are not stopped, as a check in `run()` is
  not killed on another thread's behalf; a terminal's Ctrl-C reaches them too, in the
  run's process group, and they end. Stopping their process groups is left to a later
  card. Around each group, at every number of workers, the pre-flight takes the worktree's
  state as `git status` sees it, untracked files included and ignored ones not, with the
  bytes of each file it lists hashed, writing neither the index nor an object; a group
  that changes it fails the step "concurrent checks left the tree as they found it",
  naming the group's checks and the paths, and in origin/main's pass that note keeps the
  pass out of the main-checks cache. A registry with no concurrent check, as origin/main's
  before this change, gives no group and no extra step: the run is as before. The new
  check, `tests/test_concurrent_checks.py`, runs early in the sequence and alone, since it
  starts processes of its own and measures how many run at once.

  This entry approves the change to `scripts/safe_push.py`, which reads the two fields,
  runs the groups, guards the tree around each and waits for their checks on an
  interrupt.

  This entry approves the change to `scripts/registry.py`, which reads and checks the two
  fields and prints them in its JSON.

  This entry approves the change to `checks/README.md`, which says what `concurrent`
  promises and how the pre-flight runs a group.

  This entry approves the new `tests/test_concurrent_checks.py`, which puts the runs and
  the registry's rules to stand-in checks.

  This entry approves the new `checks/27-test-concurrent-checks.toml`, which runs that
  test before the build, alone.

  This entry approves the change to `checks/05-test-certificate.toml`, which declares its
  check concurrent.

  This entry approves the change to `checks/06-check-kernel.toml`, which declares its check
  concurrent.

  This entry approves the change to `checks/08-check-fidelity.toml`, which declares its
  check concurrent.

  This entry approves the change to `checks/10-test-release-gate.toml`, which declares its
  check concurrent.

  This entry approves the change to `checks/11-test-jev-models.toml`, which declares its
  check concurrent.

  This entry approves the change to `checks/12-jev-self-test.toml`, which declares its check
  concurrent.

  This entry approves the change to `checks/13-test-screen.toml`, which declares its check
  concurrent.

  This entry approves the change to `checks/14-test-acceptance-limits.toml`, which declares
  its check concurrent.

  This entry approves the change to `checks/15-check-style.toml`, which declares its check
  concurrent.

  This entry approves the change to `checks/18-check-links.toml`, which declares its check
  concurrent.

  This entry approves the change to `checks/19-sweep-self-test.toml`, which declares its
  check concurrent.

  This entry approves the change to `checks/21-check-queue-tree.toml`, which declares its
  check concurrent.

  This entry approves the change to `checks/22-test-check-superposition-pins.toml`, which
  declares its check concurrent.

  This entry approves the change to `checks/23-check-superposition-pins.toml`, which
  declares its check concurrent.

  This entry approves the change to `checks/24-lane-condition.toml`, which declares its
  check concurrent.

  This entry approves the change to `checks/25-test-check-paths.toml`, which declares its
  check concurrent.

  This entry approves the change to `checks/26-check-paths.toml`, which declares its check
  concurrent.

  This entry approves the change to `checks/01-lake-build.toml`, whose check runs alone, and
  which says why.

  This entry approves the change to `checks/02-lake-build-audit.toml`, whose check runs
  alone, and which says why.

  This entry approves the change to `checks/03-lake-build-staging.toml`, whose check runs
  alone, and which says why.

  This entry approves the change to `checks/04-facts.toml`, whose check runs alone, and
  which says why.

  This entry approves the change to `checks/07-heath.toml`, whose check runs alone, and
  which says why.

  This entry approves the change to `checks/09-test-check-style.toml`, whose check runs
  alone, and which says why.

  This entry approves the change to `checks/16-render.toml`, whose check runs alone, and
  which says why.

  This entry approves the change to `checks/17-clean-worktree.toml`, whose check runs alone,
  and which says why.

  This entry approves the change to `checks/20-sweep.toml`, whose check runs alone, and
  which says why.
