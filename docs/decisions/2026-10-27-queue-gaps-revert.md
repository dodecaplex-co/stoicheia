- **The post-merge record step is run as Actions runs it, the shared readings are compared
  by what they do, and a stale `main-red` clears (tooling,
  [#259](https://github.com/jackChallis/stoicheia/issues/259)).** On 27 October 2026 the
  owner chose, of the options the coordinator put to them, "Pull forward now", for the
  merge queue; in the coordinator's record of that choice, the owner turns the queue on
  once #259 is closed. This change answers four of that card's
  findings: the three it names in `tests/test_auto_revert.py`, and the `main-red` left
  stale after a slow failure, which the review of its fix round found. The first three
  are about what a test takes as evidence, and need no change to the code, so the tests
  that close them pass with main's code too; their evidence is a set of changes made to
  the workflow or the code, each in a scratch copy of the tree in which main's tests and
  the new ones were both run. The fourth changes `scripts/auto_revert.py`, and each of
  its six tests fails with main's copy of that file, in 35 cases in all.

  *post-merge-final-invocation-remains-uncovered.* The tests ran the step that takes the
  trusted script from the previous main, and the fallback's shell with an environment of
  their own, but never the step "Record the failure and enqueue the revert". A new test
  reads the revert job from `.github/workflows/post-merge.yml` as the file holds it, with
  a reader of the YAML forms the file uses that fails the test on any other form, on a
  line break other than a line feed, on a key given twice at the workflow's top or among
  its jobs, and on a key it does not model, at the workflow's top or the job's, such as
  `defaults` or a workflow-wide `env`. It holds the job's permissions exactly, and its
  steps exactly and in order: the three before the last two as the file holds them, less
  their run text, with the ids `failed` and `trusted` that the conditions read, and then
  the two it runs. It holds the exact names of the variables those two run with, the
  job's six and each step's own, so that a step added before the record, or a variable
  such as `BASH_ENV` or `LD_PRELOAD` that would run the failed push's code beside the
  credentials, fails it. It evaluates the job's `if` for each result of the job it needs,
  and the two recording steps' `if` over every state the earlier steps can leave, whether
  the job so far has succeeded, failed or been cancelled: the job runs only when
  integration failed, and exactly one of the two steps runs. It then runs each step's
  `run` text as Actions runs it, in bash, with the job's environment and the step's,
  their expressions given fake values, stand-ins for `python3` and `gh` on the path that
  record their arguments and environment, and bash's trace (`set -x`) of each command
  the step runs. The record step must run two commands alone, `cat` to read the failed
  jobs and then the trusted script, and perhaps `exit`; it must call the script in
  Python's isolated mode with the push's own arguments, give it the job's token and the
  App's secrets, which the job has only through its `auto-revert` environment, hold the
  job's token in `GH_TOKEN` and `GITHUB_TOKEN` alone and the App's key in its own
  `STOICHEIA_REVERT_APP_KEY` alone, and fail the job whenever the script exits with
  anything but 0. The fallback must run exactly the commands of its text, in order, on
  the path the test gives it, call GitHub with `gh` alone, the job's token in `GH_TOKEN`
  and no other credential in any variable, and fail the job. Each of the two earlier
  steps has its run text run, traced in the same way, by tests of its own (one of them
  new, since no test ran the step that reads the failed jobs): each must run exactly the
  commands of its text on each path those tests take, and neither may write to
  `GITHUB_ENV` or `GITHUB_PATH`, through which it could change what the record step runs
  with. So a command added to a step's text, on a path a test takes, fails it even when
  it finds in the test's checkout no file of the failed push to run. Of 55 changes to the
  workflow's text, main's tests catch 5, four in the fallback's shell and one in the step
  that takes the trusted script, and the new tests catch 54: the one they miss changes
  the workflow's trigger, `on:`, which no test reads and which is outside #259. Of eight
  changes that keep what the job does (`; exit 0` after the call among them, which
  `bash -e` never reaches when the script fails), the new tests pass all eight. Of 13
  further changes, among them a line in each of the four steps that runs a file of the
  failed push only when the checkout holds one, the new tests catch 12: the one they miss
  stops the integration job, whose failure starts the revert job, from running at all,
  which is outside #259. They pass both of two further changes that keep what the job
  does.

  *link-policy-test-compares-regex-source-shape.* The test of the link reading compared
  the patterns `auto_revert.py` copies from `check_links.py` by their text and flags. It
  now compares what the two readings do: the links and anchors each reads in the five
  real pages it read before and in eight small files, one for each form the reading
  decides (schemes, fences, headings, comments, link text, reference definitions, HTML
  and line ends); whether each of 21 targets is relative; and whether each of 26 anchors
  resolves in six files and folders. Among the small files' forms are a code span that
  only a run of backticks of its own length closes, and an escaped underscore in a
  heading. Of 24 changes of behaviour to the copied reading, main's tests catch 15 and
  the new ones all 24; of eight rewrites that keep its behaviour, main's tests fail all
  eight and the new ones pass all eight.

  *protected-policy-test-scrapes-python-source.* The test of the protected paths parsed
  `safe_push.py`'s source for its lists. It now imports `safe_push`, as it already
  imported `check_links`: it is the trusted script that must not import the revision it
  reverts, and it still does not. Each path of a corpus built at the edges of every
  prefix of either list is protected by `auto_revert.py` exactly when
  `safe_push.is_protected` protects it, and each prefix's own files are protected, while
  the same path under another folder, and a name that only begins alike, are not. And,
  read from the real tree, each entry that names a folder of the repository must end in
  `/` and protect a file under it in both scripts, so a slash dropped from the same entry
  in both lists, which would leave that folder's files unprotected in both, fails it.
  Of 18 changes to either script's policy, main's tests catch 12 and the new ones all
  18; of three that keep what it decides, main's tests fail the two that reorder
  `auto_revert.py`'s list, and the new ones pass all three.

  *The stale `main-red`.* A failed push whose run is slow can record its issue after a
  later push's run has passed and cleared, which leaves main paused though its tip is
  green. Unless it enqueues a revert, `auto_revert.py` now reads main's tip afresh once
  the issue is open. While the tip is still the failed push it changes nothing more,
  since a later push's run that passes clears the issue as any other. When main has moved
  on, it removes `main-red` from the issue it opened only if GitHub's comparison of the
  failed push with the tip shows the tip ahead of it and not behind (the job's checkout
  holds main only as it stood when the job began), the tip's latest post-merge run,
  every page of runs read, completed with success, and main still names that tip just
  before the removal. If any of that cannot be read or confirmed, or main's tip cannot be
  read, the label stays and the issue says how to clear it: re-run the `clear` job of a
  passing run at main's tip. The tests hold these guards of that reading too, by a case
  each: a run of another branch or event, a run listed twice, a count that changes
  between pages, a run id of 0, a run not completed though it names a conclusion, a page
  listed newest first, as GitHub lists runs, whose newest run is in progress, and a
  comparison that is missing, malformed or diverged; and, one guard at a time, a
  comparison that is an ahead tip's in every field but one: its status behind or
  identical, the tip also behind or ahead by none, or another base or merge base.
  [WORKFLOW](../WORKFLOW.md), section 10, says so at the end of "Out of a red main", and
  its sentence that the job that clears `main-red` runs no repository code now names the
  `clear` job, since the revert job, which runs the previous main's script, can now
  remove the label too.

  `.github/workflows/post-merge.yml`, `scripts/safe_push.py`, `scripts/check_queue.py`
  and every check are unchanged, and no test or expected value is weakened.

  This entry approves the change to `scripts/auto_revert.py`: the stale `main-red`
  removed on that evidence or kept with word of how to clear it (`HOW_TO_CLEAR`,
  `github_is_ancestor`, `runs_at`, `clear_moved_on` and `record`), with its docstring
  and dry run, and its comment on the protected list, which no longer claims an order,
  since order decides nothing there.

  This entry approves the change to `tests/test_auto_revert.py`: the revert job's record
  step and fallback run as Actions runs them, with the job's permissions, steps and
  variables held; the step that reads the failed jobs run; each of the four steps' run
  text traced, and held to the commands of its text; the link reading and the protected
  paths compared by behaviour, the folders read from the tree; and the tests of the
  stale `main-red` and of the guards of its reading.
