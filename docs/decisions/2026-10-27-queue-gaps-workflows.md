- **Every enforced job of every workflow is held to a contract of its meaning, and a
  workflow file in one of seven forms that GitHub may read otherwise than PyYAML is
  refused (tests, [#259](https://github.com/jackChallis/stoicheia/issues/259)).** On 27
  October 2026 the owner chose, of the options the coordinator put to them, "Pull forward
  now", for the merge queue; in the coordinator's record of that choice, the owner turns
  the queue on once #259 is closed, and the coordinator's standing order against new
  guards or tests in `safe_push.py` and `test_safe_push.py` is waived for #259's findings
  only. This entry records the change for one of them,
  ci-semantic-coverage-excludes-enforced-jobs, which the reviewer wrote as: "Workflow
  normalization covers only `jobs.check`; weakening the negative, model, formal-model,
  acceptance, or safe-push jobs remains invisible." Until now, `scripts/test_safe_push.py`
  modelled CI's `check` job alone, and its other tests of the workflows read some settings
  of some jobs: the `negative` job's lane step made to run `true`, so that none of the
  job's checks runs, passed them all.

  The model. The tests now read every `.yml` and `.yaml` file of `.github/workflows/`, and
  every job and step of each, into its meaning: a workflow's name, triggers, permissions,
  environment, defaults and jobs; a job's name, runner, permissions, needs, condition,
  continue-on-error, timeout, environment, defaults, strategy, outputs, deployment
  environment, concurrency, called workflow and steps; and a step's id, action, inputs,
  run, condition, environment, shell, working directory and continue-on-error. A run is
  read as its lines, split at line feeds alone, as bash splits them. A step's name is left
  out, since it is shown and never run. Any other setting, in any workflow, job or step,
  enforced or not, is refused, so a new way to weaken a job cannot pass unread. The model
  takes `if: ${{ x }}` as `if: x`, a need written alone as a list of one, triggers written
  as a list as a mapping, and a continue-on-error that is false as none, since GitHub
  reads each so. An `if` with text beside its `${{ }}`, or a second `${{ }}` in it, is
  refused, since GitHub reads it as a string, which is always true.

  The contracts. `WORKFLOW_CONTRACTS`, in the test file, holds the contract of each of the
  sixteen enforced jobs: CI's `risk`, `check`, `negative`, `model`, `formal-model`,
  `acceptance`, `queue-integrity` and `queue-gaps`; post-merge's `integration`, and its
  `revert` and `clear`, which set and lift the `main-red` label that pauses the queue; the
  release gate's `release-gate`; and the cadence's `safe-push-shards`, `safe-push-tests`,
  `negative-tests` and `formal-model-kernel`. Each states every setting the model reads of
  the job and of each step: what it checks out, at which ref, with what history and
  without its token; each command, line by line, or, for a step of logic, by a digest of
  its lines (below), and the directory it runs in; each
  condition; the jobs it needs; its timeout; and, where it has them, its runner,
  permissions, environment and deployment environment. A step or job set to continue on
  error, or a command whose failure is suppressed by `|| true`, `set +e` or a last
  `exit 0`, therefore differs from its contract and is refused. The values are compared
  type for type, so `0` is not `false` nor `"30"` the number 30. The cadence's `report`
  acts on the others' results and checks nothing: the model reads it, and its contract
  names it with that reason and holds its permissions, `issues: write` alone, and its
  concurrency, one report at a time and none cancelled. A workflow file with no contract,
  a `.yaml` among them, and a contract with no file, are refused.

  The steps of logic. Thirteen steps are held by the first 128 bits of the SHA-256 of
  their lines, with what each does said beside it. That digest is a lock on their text,
  not a statement of what they do: an edit to one, a reworded message among them, must
  change its digest in the same pull request. Three of them, the lane steps of CI's
  `negative` and `formal-model` jobs and the cadence's verdict, are held by what they do
  as well, as evidence beside the lock. Each is run as GitHub runs a step with no shell
  named, `bash -e` over a file of its lines, once for each row of its whole input table,
  with that row and `GITHUB_OUTPUT` alone as its environment: the risk job's result
  (success, failure, cancelled, skipped or none) and class (R0 to R5, R6, `r5` or none),
  and for the formal model's lane its flag too (true, false or none), 45 and 135 rows;
  and the shards' result and the proof's, 25 rows. In every row, its exit status and the
  lines it writes to `GITHUB_OUTPUT` must be the ones its contract gives the row. The
  table shows what the locked lines do over those inputs, not that they read nothing
  else; that is for the review of a change to them, as for the other ten. So the
  negative lane made to pass when the risk job did not succeed is refused by its digest
  and by the first row it changes; a reworded message, a branch on an input the table
  does not give, such as the event's name, and a failure suppressed by `|| true`, which
  would turn a failed write of `full=` green, change no row and are refused by the digest
  alone. A local run on macOS's bash 3.2 may refuse a form that CI's bash 5 accepts, such
  as `[[ -v ]]`, failing closed. The other ten need Git, GitHub or an event's fixtures to
  run: the risk job's classification, three of the acceptance job's, the queue judge's
  run, the gap tests' plan, and four of the revert and clear jobs', the read of the failed
  jobs, the taking of the previous main's revert script, the issue opened without them and
  the lifting of `main-red` (`tests/test_auto_revert.py` runs the last three). The revert
  job's record step is written out in its contract, line by line;
  running it is the subject of #259's finding
  post-merge-final-invocation-remains-uncovered, in `tests/test_auto_revert.py`.

  Where they run. The contracts are tests of `scripts/test_safe_push.py`, and run where the
  rest of that file runs: on main, on the six-hourly cadence of `safe-push-tests.yml`; and,
  once the fix of #259's finding workflow-changes-select-no-gap-tests lands, in the merge
  queue's gap tests, which then run `scripts/test_safe_push.py` whole for a change to any
  file under `.github/` (their map, `GITHUB_TESTS`, names it for each such file, and
  refuses a file it does not name). Until then no pull request's CI runs them, so a change
  that weakens a workflow can land with them unrun, and the cadence finds it only once it
  is on main. An entry in the registry of `checks/` could run them on every pull request,
  as `checks/24-lane-condition.toml` runs one test of this file; that is the
  coordinator's to approve, and this change adds none.

  The YAML. The two reviews of the attempt of 21 October found readings that PyYAML, which
  reads YAML 1.1, and GitHub may take apart, and the review of this change found more. The
  loader now reads YAML 1.2's meanings where PyYAML would give YAML 1.1's (`on` is a key,
  `no` a word, and a number with a leading zero, as `036` (30 to YAML 1.1, 36 to YAML
  1.2), a string, which matches no contract's number), and refuses a workflow file in any
  of seven forms: one that holds U+0085, U+2028 or U+2029; a `%` directive; a tag,
  verbatim or not, but the non-specific `!` written alone on a scalar, which it reads as a
  string, as YAML 1.2 does; a key `<<`; a key given twice in one mapping; a flow
  collection that spans lines, whose indentation PyYAML does not check; and a file that is
  a symbolic link, or anything else but a regular file, or that stands in a `.github` or
  `.github/workflows` folder that is a link, since GitHub reads the entry in the commit's
  tree. No workflow uses any of the seven. Seventeen edits of `ci.yml`, each of which
  leaves its jobs as they were to PyYAML, a run's lines split by `str.splitlines`, are
  refused as file text: each of the three characters in place of a line feed of the
  formal model's kernel step, `persist-credentials: !!bool no`, `timeout-minutes: !!int
  036`, `{!!merge <<: *a}`, `{<<: *a}`, a `%YAML 1.1` directive, `!<!> 30`, a `run` given
  twice, `timeout-minutes: 036`, `persist-credentials: no`, `timeout-minutes: ! 30`, a `!`
  on a checkout's inputs and on a job's steps, the inputs written as a flow mapping over
  two lines, and the triggers as a flow sequence over two lines. So are `post-merge.yml`
  made a symbolic link to its own text, a folder in its place, and the folder of
  workflows made a link to a copy of itself. Main's tests pass all seventeen edits, and
  the link to `post-merge.yml`.

  The evidence. `weakenings` generates, from the workflows as they stand, each weakening
  of each enforced job: a trigger, the job, a need, a step or a line of a run dropped; a
  step added first; the job or a step set to continue on error, or given another
  condition or none; a longer timeout; another workflow called; a run made `true`, run
  elsewhere, or with its failure suppressed by `|| true`, `set +e` or a last `exit 0`; a
  checkout of another ref or history, or keeping its token; and the report's permissions
  or concurrency changed. On main there are 1,087, and the contracts refuse all 1,087;
  the test of the weakenings refuses any that they pass. Twenty-two of them leave every
  row of a tabled step's table as it was, and its digest alone refuses them: one of its
  messages dropped (ten); one of the three suppressions (nine); and one of the verdict's
  arms for a failed, cancelled or skipped result dropped, so that the result falls to its
  last arm, red as well (three). Written as file text and given to
  main's own tests of the workflows in a scratch copy of main's tree (the eight tests of
  `Units` that read them, and `CadenceReport` and `Shards` for the cadence's file), 211
  of the 1,087 made one of them fail, and 876 passed them all. Main's tests caught every
  weakening of CI's `check` job, 42; 45 of the 105 of CI's `negative` and `model` jobs,
  by the comparison of their commands with safe_push's lists, the lane-condition test and
  the test that every checkout keeps no token; 18 of the `formal-model` job's 96, by the
  last two; 98 of the 103 of the cadence's `safe-push-shards` and `safe-push-tests`, which
  `Shards` runs; and eight others: a checkout keeping its token in each of CI's `risk`,
  `acceptance`, `queue-integrity` and `queue-gaps` and post-merge's `revert` and `clear`,
  and the cadence's `negative-tests` and `formal-model-kernel` dropped. They caught none
  of the release gate's 24, none of post-merge's `integration`'s 5, none of the other 260
  of `revert` and `clear`, none of the report's 2, and none of the triggers' 7. Main's
  tests pass every workflow as it stands, and as it is rewritten for that run. The review
  of this change wrote 33 weakenings of its own as file text: the contracts refuse 30 of
  them, and main's tests, with `tests/test_auto_revert.py` for post-merge's and
  `tests/test_release_gate.py` for the release gate's, catch 10. The three the contracts
  pass change the report's condition or add a step to it, which its contract does not
  hold, and `CadenceReport` and `Shards` catch all three. Rewritings that keep the
  meaning hold their contracts: flow style with the keys sorted and each collection on
  one line, every string double-quoted, each condition in `${{ }}`, a need as a list,
  continue-on-error false on each job and step, CI's triggers as a list, and the
  non-specific tag on a string.

  This entry approves the change to `scripts/test_safe_push.py`, whose new workflow model,
  contracts of the sixteen enforced jobs, YAML loader and five tests of `Units` are
  described above.

  No workflow, check script, statement, definition, lock, record or `--` line changes, and
  no existing test or expected value changes.
