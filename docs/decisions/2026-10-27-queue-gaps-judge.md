- **The queue judge's two reads of a queued entry must agree, an exact revert's merges
  are pull requests, every `.github/` file chooses its tests, and a review cell must give
  its verdict beside its commit
  ([#259](https://github.com/jackChallis/stoicheia/issues/259)).** Card #259 holds the
  findings that the /no-mistakes run on train 3B, the merge queue's producers, rated as
  errors on 21 October, and the queue is not turned on until it is closed. On 27 October
  2026 the owner chose, of the options the coordinator put to them, "Pull forward now",
  for the merge queue; in the coordinator's record of that choice, the owner turns the
  queue on once #259 is closed. The queue's judge, `scripts/check_queue.py`, now answers
  three of the card's findings, and the train check, `scripts/check_train.py`, a fourth,
  each with tests that fail with main's copy of the script and pass with this one. Fixes
  for them were first written on 21 October, on an older main, and never landed; they
  are ported here by hand, with the corrections the review of that work asked for. No
  check is loosened, and no existing test's assertion or expected value changes: the
  fixtures that stand for GitHub's answers gain the fields the new checks read.

  The editor and the body (queue-editor-snapshot-toctou). The judge read who last edited
  each queued entry from the queue's GraphQL answer, and the body it judges later, from
  the pull request's REST answer, so a bot's edit made between the two reads could be
  judged as a person's. The GraphQL read now asks for each entry's body beside its head,
  its editor and its last rename, and an entry whose REST body differs from that
  answer's, or whose body that answer lacks or gives as anything but text, is
  unreadable, so the job fails. The heads were already compared, through the queue
  order. So the body judged is the one whose editor that answer names. The new tests ask
  the read for the body; give an edit seen by REST alone, to both entries (with main
  red, one that adds the line that lets an entry land as main's fix) and to the second
  alone; and give a body missing or malformed. Main's judge does not ask for the body,
  and passes the group in each of the other cases.

  The pull requests of a reverted push
  (exact-revert-does-not-validate-pr-merge-contract). An automatic revert's failed push
  had only to be two-parent merges, so the revert of a merge no pull request made could
  pass, though `scripts/auto_revert.py` would not make it. Before any revert is computed,
  each merge of the push must now meet what `auto_revert.py`'s `trains` and `read_trains`
  require on main: its subject, read as `trains` reads it, names a pull request; no
  number comes twice; and GitHub's REST answer for that number records it merged, with
  that merge as its merge commit, the merge's second parent as its head, `main` of this
  repository as its base, a title that is not blank and a kind label, one of
  `safe_push.KIND_LABELS`, which `tests/test_auto_revert.py` holds equal to the revert
  script's own list. A value that breaks one refuses, and a field missing or in the
  wrong form is unreadable, as everywhere in the judge, so nothing they refuse passes.
  There is a test for each field, the base repository's whole name among them (one of
  `owner/other` refuses where this repository is `owner/repository`), and one for the
  subject: Git keeps a leading space or tab in it and drops a trailing one, and the
  judge, like `trains`, finds no pull request in the first and #1 in the second. Main's
  judge passes the revert in every case that refuses.

  The tests of `.github/` (workflow-changes-select-no-gap-tests). The queue's gap tests
  ([WORKFLOW](../WORKFLOW.md), section 10, "The gaps of what is new") chose no test for a
  changed workflow, so a group could replace an enforced command with `true` and pass
  them. Now `GITHUB_TESTS` names, for each of the five files under `.github/` on main, the
  tests that read it, found by searching `tests/` and `scripts/test_*.py` for each file's
  name and reading what each match does: `scripts/test_safe_push.py` reads all five;
  `tests/test_auto_revert.py` and `tests/test_check_queue.py` read `ci.yml` and
  `post-merge.yml`; and `tests/test_release_gate.py` reads the pull request template.
  Five other test files name `ci.yml` only in a docstring or as a path in their own
  fixtures, and are not named. A file the map names, changed or deleted, asks for every
  test named for it, and none is excused for being deleted: while one is missing, the
  group is refused, naming the test and the file. A test the map names asks for itself
  whether or not the group changes a file it reads, so a group that only deletes it is
  refused too. Any other path under `.github/`, a new workflow, `CODEOWNERS` or `.github`
  itself among them, is refused, naming it, until main's judge names its tests. The new
  tests run each mapped file's tests, changed and deleted, and refuse an unmapped path, a
  mapped test deleted beside a changed workflow, and a mapped test deleted alone; main's
  judge passes each of those groups, choosing no test for it.

  What a chosen test checks is its own. Of `release-gate.yml`, the one test that reads
  it, `scripts/test_safe_push.py`, checks only that it reads as YAML, since it has no
  lane step whose conditions that test reads. Holding every job of every workflow to its
  meaning is the card's finding ci-semantic-coverage-excludes-enforced-jobs, which this
  train does not close.

  The review cells of a train (incomplete-review-evidence-still-passes). The train check,
  `scripts/check_train.py`, took any letter beyond a commit as a completed review, so
  "Findings will be added later at <sha>" passed. It now reads each `/code-review` and
  `/security-review` cell three times: as written, as a reader sees it, and as a reader
  sees it with the inline Markdown markers (`*`, `_`, `` ` `` and `~`) taken out, each
  with Unicode's default-ignorable characters dropped, the Hangul fillers among them, so
  markup or an invisible letter inside a word (`w<i></i>ill`, `w*i*ll`, `not<i></i>
  required`, `n*o*t required`) cannot hide the word from all three at once: one reading or
  another reads it whole. In each reading the cell must give a verdict in the same clause
  as a commit it names, a clause ending at every semicolon, exclamation mark, line end and
  line break a reader sees (`<br>`, `<p>`), at the full stops of other scripts, at every
  question mark but one that begins a link's query (`?pr=2`), and at every full stop but
  one between two letters or digits, inside a name or a number ("Claude Opus 5.5",
  `SCHEMA.md`), so `Started at <sha>; CI passed`, `Started at <sha>. CI passed` and
  `Started at <sha>!CI passed` refuse, while a full stop with no space after it before a
  word (`<sha>.CI passed`) ends no clause. The verdicts are pass, passes or passed;
  approve, approves or approved; fixed, resolved or stamped; "found no", "found nothing",
  "nothing found", "skipped nothing" and "nothing blocking"; no findings or defects, or a
  number of them; and, on `/security-review`, "not required". A verdict is none after a
  negation, modal or hedge among the three words before it in its phrase ("may have
  passed", "almost passed", "didnt pass"), as a noun ("a first pass", "two passes"),
  struck through (`~~passed~~`), or followed at once by a word saying the review is
  unfinished ("passed (partial)"). The clause's commit may be any the cell names; with a
  repository, the cell must also name one of the member's own, though not necessarily in
  that clause. As a second layer, words that say a review is still to come, in progress or
  provisional refuse anywhere in the cell: "will", "yet", "outstanding", "in progress",
  "so far", "to follow", "to be reported", "to do", "not started", "not finished", "not
  reviewed", "unreviewed", "unread", "preliminary", "provisional", "continues", "resumes",
  "tomorrow", "next week", "for now", "still running", "in principle" and their like,
  "later" where it says when, "after the merge" but not "after the merge of main", and a
  question mark that does not begin a link's query; and the lists are read in a fourth
  reading too, as written with Unicode's other invisible characters kept as separators, so
  that one of them between two words ("review", U+2065, "pending") joins them in no
  reading. Two are narrowed where a real completed cell needs it: "yet" but not "does not
  yet exist", and "unread" only after "still", "is", "remains" and their like, since "the
  records were unread" and "#240 unread" are findings. "Follows", "deferred",
  "incomplete", "unfinished", "partial", "interim", "not yet", "not done", "to be done"
  and their like refuse in a phrase that also names the review, a finding, a verdict or
  the rest, so "the full review follows" refuses and "the deferred hardening is filed as
  #221" and "#116's interim texts" do not. The commit is still read where a reader sees
  it, and must be one of the member's own; a member that changes a protected path may not
  say "not required" in its security cell in any reading. Every cell that the first review
  of the 21 October attempt listed refuses, and so does every cell that the review of 27
  October lists as passing this train's first fix; with main's copy of the check, the new
  tests give 301 failures and 28 errors.

  Of the 395 distinct `/code-review` and `/security-review` cells of the coordinator's 211
  fed and rejected train files, none the check refused is accepted, and eleven it accepted
  are refused, each because it gives its verdict only in a sentence of its own, not beside
  a commit (F2-ii14, ER-iii1calls, C7-circle294a, C7-guard, C7-t429, ER-pins168b,
  C7-t162b, C7-t539, C7-t162, HM-accci and HM-ctag). The check judges only a `train/*`
  branch's body, by its Members table, and no body in the lane or among the items waiting
  to be fed has one, so no work in flight is held. A rule read from prose cannot list
  every way of saying that a review is not done ("PASS if CI is green" still passes); the
  cells are written by the coordinator's crews, and each is read by the lane as well.

  Two things stay open, outside this train's findings. A change to any file under
  `.github/` makes queue-gaps run the whole of
  `scripts/test_safe_push.py`, which took 72 to 78 minutes in one job
  (`safe-push-tests.yml`), against queue-gaps' limit of 75 minutes: the queue's trial is
  to measure it, and if it does not fit, the suite is sharded there or the limit raised.
  And the files the workflows run, `scripts/copy_acceptance_checks.sh`,
  `scripts/requirements-test_safe_push.txt` and `scripts/hooks/`, still choose no test
  of their own.

  This entry approves the change to `scripts/check_queue.py`, which reads each queued
  entry's body in the queue's GraphQL answer, checks the pull requests of a reverted
  push, and maps the files under `.github/` to their tests, as above.

  This entry approves the change to `tests/test_check_queue.py`, which gains twenty
  tests, and whose fixtures now give each pull request a title and a base, give each
  queued entry's body in the queue's answer, edit both answers when a body changes, and
  record each pull request of a failed push as merged at its merge, as GitHub records it.

  This entry approves the change to `docs/WORKFLOW.md`, whose section 10 now says, in
  "The gaps of what is new", that a file under `.github/` asks for the tests that read
  it and that a test named for one is never excused for being deleted, and, of an
  automatic revert, that each merge of the failed push must be a pull request's recorded
  merge; and whose account of a train's `--body-file`, in the same section, now says how
  review cells are read, as above.

  This entry approves the change to `scripts/check_train.py`, which reads review cells
  as above.

  This entry approves the change to `tests/test_check_train.py`, which gains nine tests
  and changes none.
