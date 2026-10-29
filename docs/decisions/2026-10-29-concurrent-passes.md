<!-- entry: id=concurrent-passes cards=609 line="Step 4's two passes may run at once, each in a worktree of its own, reported in the order of one after another." -->
- **Step 4's two passes may run at once (checks,
  [#609](https://github.com/dodecaplex-co/stoicheia/issues/609)).** Card #609 is the
  coordinator's record of the third step in making the pre-flight faster, after the
  negative tests' workers (#607) and step 4's concurrent checks (#608). A commit that
  changes a check input runs step 4 twice: with origin/main's copies of the checks, and
  then with its own. The two passes are independent, but they ran one after another; on
  the Mac, #594's two passes took 31.6 minutes together.

  With `STOICHEIA_PASS_WORKERS=2`, the two passes run at once. When origin/main's pass is
  taken from the main-checks cache, only the commit's pass runs, so there is nothing to
  run beside it. Otherwise origin/main's pass runs in a second worktree, given the first
  one's build, and the commit's runs in the first. Each
  runs on a thread of its own and keeps its rows to itself. The harness's own thread puts
  the rows into the report in the order of one after another:
  1. origin/main's checks;
  2. keep_apart's judgement of them;
  3. the commit's checks;
  4. the same three for the negative tests.

  The verdicts, the lines printed, the summary and the log files are those of the run
  one after another, with three exceptions:
  - the paths in them name the worktree each pass ran in;
  - the stricter refusal of a tree left changed, below;
  - a check limited by the clock, which may fail under the other pass's load, below.

  Each exception is stricter, never looser. "The first failure stops the run" keeps its
  meaning, since the failure reported is the first in that order.

  When origin/main's pass fails outright, or keep_apart refuses, the commit's pass of
  that loop is discarded: its rows are never put in, and its logs are removed. The
  negative tests begin only once both passes of the checks have been judged. A pass is
  told to stop between its steps, so a refusal of this kind waits for the commit's
  current step, or group, to end before it is reported. No main-checks cache entry is
  kept from a pass a signal stopped. The harness's own thread decides that, once it has
  taken in the signal. An entry written before the signal, once origin/main's negative
  tests have ended, stays, as it does one after another.

  Each pass still begins at the commit, as `at_commit` checks. Once origin/main's
  worktree is reset, its pass is also asked what the commit's pass would begin with in
  the same worktree, one after another, and a refusal there is reported in the same
  place. So a pass that leaves its tree in a state `at_commit` refuses is refused as it
  would be one after another: a skip-worktree flag survives `git reset --hard`, and a
  nested repository survives `git clean -fd`.

  The stricter refusal of a tree left changed. At two passes, each pass's worktree runs
  its negative tests after its checks: the second worktree serves both loops of
  origin/main's pass, and no third worktree is made. So the commit's negative tests begin
  with `at_commit` in the worktree its checks ran in, not in a fresh one. A tree those
  checks leave changed, if no check refuses it, is refused there; one after another, it
  would pass.

  While the harness waits for the two passes, its handlers for SIGINT, SIGTERM and SIGHUP
  only record a signal, as #608's do while a group runs. Once a signal is recorded:
  - neither pass starts a further step, or a further check of a group at one worker;
  - each pass's current step, or group at more than one worker, runs to its end;
  - every thread is joined;
  - the previous handlers go back with the signals held, the hold lifted whatever happens,
    as #650 does for a group;
  - only then is what the first signal would have raised raised.

  No row of the loop a signal stopped is put in, and the commit's logs of that loop are
  removed, where one after another keeps the rows and logs of the steps run before the
  signal. An interrupted run has no verdict either way.

  A terminal's Ctrl-C reaches the checks too, through the run's process group, and they
  end. So no check of either pass still runs when a worktree is cleaned or removed.

  The cap allows two passes at once only when twice the larger of two numbers is no more
  than half the machine's cores: the check workers (`STOICHEIA_CHECK_WORKERS`, as #608
  caps it) and the negative workers (`STOICHEIA_NEGATIVE_WORKERS`). That is the same half
  as #608's. Otherwise the passes run one after another. The check list line says which,
  with the numbers, and a value that is not a whole number from 1 fails it. The cap bounds
  the checks the harness starts at once and the negative tests' workers. A single check,
  a build or the sweep, may itself use every core, at one pass or two.

  A check that runs alone does so within its pass, as the check list line says. It may
  now run beside a check of the other pass, as it already may beside another yard's
  pre-flight on the same machine. Two checks have limits timed by the clock:
  `scripts/heath.py` gives each plant half a second, and one case of
  `tests/test_check_style.py` has two seconds. Under the other pass's load, the sweep's
  Leans among it, either may fail at two passes where it passes one after another. The
  failure is stricter, never looser, but it is a false refusal. A stronger guarantee, for
  checks that must run beside nothing at all, is left to a card of its own.
  `checks/README.md` now says what "alone" means at two passes. The commit's checks
  also run while origin/main's pass runs in the second worktree. Code of the commit could
  reach that worktree while the pass runs: the same class as #197 and #218, code of a
  commit that runs at elaboration, now without needing a process left running.

  Unset or empty, the variable means one pass at a time, and the run is the one before
  this change, but for one line, below. So nothing runs at once until the lane sets the
  variable.

  The untimed work between the rows. The card took 22 of 51 minutes on GitHub's free
  4-core runner to be untimed work. That came from a misreading of the benchmark's
  summary by its parser. The negative tests' row is a note, whose line gives its time
  after a long path, and its 1,282 seconds were counted as untimed. Measured again from
  the same logs, the untimed work in the whole of step 4 is about a second on every
  runner. On the Mac it is under a second at each switch between the passes. Each piece
  is now named and timed, and step 4 ends with one plain line saying them, `between the
  rows of step 4:`. It is no row of the report, so the summary and the record are
  unchanged. At two passes the line sums pieces that ran at the same time, and says so.

  The pieces:
  - `worktree add` and `worktree remove`;
  - `copy_build`;
  - `at_commit`;
  - `base_copies`, origin/main's copies put in;
  - `reset and clean`, which takes them out;
  - `tree_state`, #608's guard of each group;
  - the main-checks cache's lookup and save;
  - keep_apart's judgement.

  At two passes the third worktree, and its build copied in, are gone. Each piece kept
  must stay:
  - **`at_commit`:** it lets a pass trust its tree, and it only asks Git. The two that
    recheck a tree nothing in the harness has touched since are cheap, run at the same
    time as the other pass, and catch a process left running (#218).
  - **The reset and clean:** they take origin/main's copies out before the tree is
    checked again or removed.
  - **The second worktree and its build:** two passes need two trees, and the build saves
    the second a full one.
  - **`tree_state`, the cache's lookup and save, and keep_apart:** they are the guard, the
    cache and the rule themselves.

  On the Mac all of them come to between 1.1 and 1.6 seconds a run.

  The change lands with one pass at a time the default, for the lane to set. It was
  measured on the Mac (16 cores, so the cap is 8) on 29 October 2026, from 06:57 to
  08:23. The runs were taken in turn (B, A, B, A), at nice 10, with negative workers 4
  and check workers unset, as the lane runs them, while the lane, yards, ships and other
  work ran as usual. They ran in a simulated clone whose main was this change at
  2ecac9271. Reviews came after the measurement. They changed four things, none of
  which changes the work a passing run does:
  - where a pass told to stop saves to the cache, which acts only once a signal is
    recorded;
  - where the entry is saved at two passes: on the harness's own thread once
    origin/main's pass has ended, the same save moved;
  - a stop check between the checks of a group at one worker, likewise;
  - three more pieces timed in the line of the work between the rows, which only reads
    the clock around work the run already did.

  One commit was judged throughout: a comment in `scripts/check_links.py`,
  with an entry naming it, so that step 4 runs both passes. The column B is
  `STOICHEIA_PASS_WORKERS=2`, and A is unset.

  | run | mode | dry run, wall (s) | exit | load, median (range) |
  |---|---|---|---|---|
  | 1 | B | 790 | 0 | 15.3 (10.8-34.4) |
  | 2 | A | 1502 | 0 | 12.5 (6.3-40.2) |
  | 3 | B | 899 | 0 | 21.1 (13.3-42.5) |
  | 4 | A | 1920 | 0 | 21.4 (11.3-85.3) |

  One pass at a time took 1,711 seconds on average, and two at once 845, so two at once
  was 2.0 times as fast. Even the least favourable pairing, run 3 at a load of 21.1 against
  run 2 at 12.5, gives 1.67 times. The ship's own tests ran beside runs 3 and 4, from
  about 07:45 to 08:05, as the lane's usual work does. Every run passed, and the summaries
  of all four runs are the same, row for row (88 rows), once times are masked. The line
  of the work between the rows gave 1.1 to 1.6 seconds in every run.

  The same measurement on GitHub's free 4-core runner remains. It is built on the branch
  bench/passes609, with one job a pair so that both modes share a CPU. On four cores the
  cap allows two passes at once only with negative workers 1, against the 4 that CI's
  negative job uses.

  This entry approves the change to `scripts/safe_push.py`, which reads the variable and
  runs the two passes at once.

  This entry approves the new `tests/test_concurrent_passes.py`, which puts the two passes
  to stand-in checks: the same verdicts, rows, lines and logs with one pass at a time and
  two at once.

  This entry approves the new `checks/28-test-concurrent-passes.toml`, which runs that test
  early in the sequence and alone.

  This entry approves the change to `checks/README.md`, which says that a check without
  the field runs alone within its pass.

  This entry approves the change to `tests/test_concurrent_checks.py`, whose check list
  test no longer takes `STOICHEIA_PASS_WORKERS` from its environment, and whose list of
  checks that run alone names the new one.
