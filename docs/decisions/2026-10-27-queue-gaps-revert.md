- **The post-merge record step is run as Actions runs it, the shared readings are compared
  by what they do, and a stale `main-red` clears (tooling,
  [#259](https://github.com/jackChallis/stoicheia/issues/259)).** On 27 October 2026 the
  owner chose, of the options the coordinator put to them, "Pull forward now", for the
  merge queue; in the coordinator's record of that choice, the owner turns the queue on
  once #259 is closed. This change answers four of that card's
  findings: the three it names in `tests/test_auto_revert.py`, and the `main-red` left
  stale after a slow failure, which the review of its fix round found. The first three
  are about what a test takes as evidence, and need no change to the code, so the tests
  that close them pass with main's code too; their evidence is a set of changes made in
  memory to the workflow or the code, against which main's tests and the new ones were
  both run. The fourth changes `scripts/auto_revert.py`, and each of its four tests fails
  with main's copy of that file, in 19 cases in all.

  *post-merge-final-invocation-remains-uncovered.* The tests ran the step that takes the
  trusted script from the previous main, and the fallback's shell with an environment of
  their own, but never the step "Record the failure and enqueue the revert". A new test
  reads the revert job from `.github/workflows/post-merge.yml` as the file holds it, with
  a reader of the YAML forms the file uses that fails the test on any other form, on a
  line break other than a line feed, and on a key it does not model, at the workflow's
  top or the job's, such as `defaults` or a workflow-wide `env`. It evaluates the job's
  `if` for each result of the job it needs, and the two recording steps' `if` over every
  state the earlier steps can leave, whether the job so far has succeeded, failed or been
  cancelled: the job runs only when integration failed, and exactly one of the two steps
  runs. It then runs each step's `run` text as Actions runs it, in bash, with the job's
  environment and the step's, their expressions given fake values, and stand-ins for
  `python3` and `gh` on the path that record their arguments and environment. The record
  step must call the trusted script in Python's isolated mode with the push's own
  arguments, give it the job's token and the App's secrets, which the job has only
  through its `auto-revert` environment, hold the token or the App's key in no other
  variable but `GH_TOKEN`, the job's own token, and fail the job whenever the script
  exits with anything but 0. The fallback must open the issue with `gh` alone, holding
  the job's token and never the App's key, and fail the job. Of 33 changes to the
  workflow's text that alter what the revert job does, main's tests catch 3, all in the
  fallback's shell, and the new tests catch 32: the one they miss takes `issues: write`
  from the job's permissions, which no shell run can show. Of five changes that keep what
  it does (`; exit 0` after the call among them, which `bash -e` never reaches when the
  script fails), the new tests pass all five.

  *link-policy-test-compares-regex-source-shape.* The test of the link reading compared
  the patterns `auto_revert.py` copies from `check_links.py` by their text and flags. It
  now compares what the two readings do: the links and anchors each reads in the five
  real pages it read before and in eight small files, one for each form the reading
  decides (schemes, fences, headings, comments, link text, reference definitions, HTML
  and line ends); whether each of 21 targets is relative; and whether each of 26 anchors
  resolves in six files and folders. Three rewrites of a pattern that keep its behaviour
  fail the old test and pass the new; ten changes of behaviour, a fence that needs four
  backticks among them, fail both.

  *protected-policy-test-scrapes-python-source.* The test of the protected paths parsed
  `safe_push.py`'s source for its lists. It now imports `safe_push`, as it already
  imported `check_links`: it is the trusted script that must not import the revision it
  reverts, and it still does not. Each path of a corpus built at the edges of every
  prefix of either list is protected by `auto_revert.py` exactly when
  `safe_push.is_protected` protects it, and each prefix's own files are protected, while
  the same path under another folder, and a name that only begins alike, are not.
  `auto_revert.py`'s list reordered fails the old test and passes the new; an entry
  dropped from either list, an entry added to `auto_revert.py`'s, or its matching made to
  take any path that begins with an entry, so that `lean-toolchain.notes` counts as
  `lean-toolchain`, fails both. A slash dropped from the same entry in both lists passes
  both, and fails the test of a revert's labels instead.

  *The stale `main-red`.* A failed push whose run is slow can record its issue after a
  later push's run has passed and cleared, which leaves main paused though its tip is
  green. Unless it enqueues a revert, `auto_revert.py` now reads main's tip afresh once
  the issue is open. While the tip is still the failed push it changes nothing more,
  since a later push's run that passes clears the issue as any other. When main has moved
  on, it removes `main-red` from the issue it opened only if the tip contains the failed
  push, the tip's latest post-merge run, every page of runs read, completed with success,
  and main still names that tip just before the removal. If any of that cannot be read or
  confirmed, or main's tip cannot be read, the label stays and the issue says how to
  clear it: re-run the `clear` job of a passing run at main's tip.
  [WORKFLOW](../WORKFLOW.md), section 10, says so at the end of "Out of a red main".

  `.github/workflows/post-merge.yml`, `scripts/safe_push.py`, `scripts/check_queue.py`
  and every check are unchanged, and no test or expected value is weakened.

  This entry approves the change to `scripts/auto_revert.py`: the stale `main-red`
  removed on that evidence or kept with word of how to clear it (`HOW_TO_CLEAR`,
  `runs_at`, `clear_moved_on` and `record`), with its docstring and dry run.

  This entry approves the change to `tests/test_auto_revert.py`: the revert job's record
  step and fallback run as Actions runs them, the link reading and the protected paths
  compared by behaviour, and the tests of the stale `main-red`.
