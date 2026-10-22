- **The safe_push tests run as seven shards side by side
  ([#233](https://github.com/jackChallis/stoicheia/issues/233), its first part).** CI's
  `safe-push-tests` job ran the whole of `scripts/test_safe_push.py` in one job: 37.7
  minutes on #239 and 45.4 on #232, on GitHub's runners, and on #240 it ran past its
  60-minute limit and was cancelled, while the rest of CI together takes about 11 (its
  median). The 61 tests of `Merge` alone take 20 minutes, so whole classes cannot balance,
  and the suite is dealt out test by test. `python3 scripts/test_safe_push.py --shard K/N`
  lists the suite's tests with unittest's own loader, so that a new test is never missed,
  and weighs each by the seconds it took on a GitHub runner, kept in the new
  `scripts/test_safe_push_times.json`: 288 tests, read from the timestamps of #239's run,
  with an estimate of the module's setup, the clone of the repository that every shard
  pays once. It deals them out longest first, each to the shard with the least time so
  far, then the fewest tests, then the lowest number, ties between tests going by name, so
  that every test lands in exactly one shard, the same one on every machine; shard K runs
  exactly its own, in unittest's order. A test the file does not name weighs the median,
  2.7 seconds, and every shard's log names it. Without `--shard` the whole suite runs, as
  before, and WORKFLOW section 8's commands stay as they were, with a line added for one
  shard. In `.github/workflows/ci.yml` the one job becomes three. `safe-push-paths`
  decides, as the old step did, with the same paths, messages and failures, whether the
  pull request changes safe_push's check inputs, `.github/` or `docs/WORKFLOW.md`.
  `safe-push-shards`, a matrix of seven, runs only when it does, each shard with the whole
  history, no token kept, Python 3.12, the pinned PyYAML and a 30-minute limit, none
  stopping the others when it fails; each is given its N as `strategy.job-total`, so that
  the matrix's list is the one place N is written. `safe-push-tests`, the check's name
  unchanged, needs both, runs whatever happened before it (`always()`, on pull requests
  only), and passes at once, with the old message, when nothing it guards changed, and
  otherwise only when the shards' result is success: a shard that failed, was cancelled or
  was skipped fails it, and its log says which, as it does when the paths job did not
  succeed. So that no test can fall off that path unseen, the check also proves the
  coverage, from what the shards ran rather than from the dealing: each shard writes the
  tests it ran, each with its outcome (`--ran FILE`), and keeps the list as an artifact,
  a test having failed or not, for 35 days, beyond the 30 in which GitHub lets a run's
  failed jobs be run again, which reruns no shard that passed, and `safe-push-tests`,
  whatever the shards' result, checks out the commit they ran, GitHub's merge of the pull
  request into main, as they did and as the job did before it was sharded, fetches every list and runs `--cover DIR`, before its verdict on that
  result. That lists the tests with unittest's loader at the commit, reads N from the
  matrix, and fails, naming each, on a test no shard ran, a test run twice, a shard that
  left no list (as one that stops before its end leaves none), a test the loader does not
  list, and a test that did not pass. Seven, because by the measured times each shard then holds about 330 seconds,
  setup included (five and a half minutes), where six would hold 6.4 minutes; the time
  after comes from this pull request's own CI run, and the times file says that its
  figures are to be measured again from that run. `--times-from-log` does it: it reads a
  run's logs (`gh run view RUN --log`), each line timestamped by GitHub, and writes the
  file, the setup's time measured up to a line `setUpModule` now prints when its clone is
  ready. Given #239's log, with that line put in, it gives back each of the 288 times the
  file holds. Nothing is selected out: every test still runs on every pull request that
  ran the job before. Running only the classes a change touches, the issue's second part,
  is the owner's decision, and waits on it. A new class, `Shards`, without git or network,
  checks that for the N of CI's matrix the names that `--shard K/N --ran FILE` hands
  unittest, and the lists it writes, for each K, hold every test of the loader's list
  once, in its order, and pass the proof; that a test the file does not name, planted as a
  later pull request would add it, is dealt to one shard, handed to unittest and listed
  there, and passes the proof; that the proof, given the lists with one fault planted,
  names the test dropped, a test two shards ran or one ran twice, a list missing, a test
  the loader does not list, a test that failed, and a list too many or not a list; that a
  shard's list gives each test's outcome, a failing subtest failing its test; that the
  times read from a few lines of a CI log are those its timestamps give, and that a run
  cut short, miscounted or without the setup's line is refused; that the dealing is the
  same whatever order its inputs come in; that each form of the command line stands alone;
  that each shard runs the checkout, Python, parser and command above and keeps its list;
  and that `safe-push-tests` is named so, needs the matrix job, runs if `always()`,
  refuses every result but success when the paths job says the tests must run, by running
  its verdict's script under bash for each result, its steps' conditions read as GitHub
  reads them; that the proof runs before the verdict whatever the shards' result, and
  after a failed fetch, which still fails the job; and that a failing shard keeps its
  list, and the proof names the test that failed. Main's ruleset still does not require
  the check; a failing shard, like any failing check, holds a merge through the merge
  gate.
  [WORKFLOW](../WORKFLOW.md), sections 8 and 10, describes the shards and how to run one.
  The protected files changed are `.github/workflows/ci.yml`, `scripts/test_safe_push.py`
  and `scripts/test_safe_push_times.json`. No check is weakened.
