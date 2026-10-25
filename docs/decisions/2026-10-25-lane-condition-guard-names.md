- **The guards that refuse the planted cases of the `check` job's parser install, named,
  and one claim of their entry corrected
  ([#430](https://github.com/jackChallis/stoicheia/issues/430)).** The entry of 24
  October, [the lane-condition test runs on each pull request's own
  path](2026-10-24-lane-condition-in-ci.md), lists the fourteen planted cases of
  [#346](https://github.com/jackChallis/stoicheia/issues/346) that the model of CI's
  `check` job refuses, and says that, with the test that decides each taken out, its case
  was seen to be accepted; but it names those tests only as the line's equality, the
  directory's, and the guard of order or count. Card #430, from TS's review of #346, asks
  that they be named in a later entry. That entry, being history, is not edited. This one
  names each guard, as the code stands on main at f3cfef05, and corrects one of its
  claims.

  Where the cases are. They are subtests of
  `Units.test_ci_check_job_rejects_unmodeled_setup_and_environment`, in the landing
  tool's tests, `test_safe_push.py`. Each changes the workflow's YAML for the `check` job
  and hands it, through `normalized_check_job`, to `enforced_check_commands`, the
  function that judges the job's setup prefix and its one run of the checks. That
  function walks the steps in order. For each it first works out `is_parser`, which holds
  when the step uses no action, its run is the one line of `PIP_INSTALL` (the clause
  `step.run == PIP_INSTALL`, the line's equality), and its working directory is
  `PIP_DIRECTORY`, the runner's temporary directory (the clause
  `step.working_directory == PIP_DIRECTORY`, the directory's). It counts the setup steps
  it has seen in `setup_index`, against the three of `setup_order` (the checkout, the
  Python setup and elan), and the install in `parser_installed`.

  The cases, each with the condition of `enforced_check_commands` that refuses it, and
  its message:

  - the four changed lines in the temporary directory (another requirements file, an
    extra package, the install without `-I`, and the install with `-P` alone, each "in
    the temporary directory"): the line's equality fails, so `is_parser` is false, and
    the condition `step.has_working_directory and not is_parser` refuses the step, as
    one that "has a working directory";
  - the same four lines from the checkout, with no working directory: both clauses fail,
    and the step, neither setup nor the install, is refused by the condition
    `step.uses is not None or RUN_CHECKS not in step.run`, as one that "is neither the
    run of the registry's checks nor the modelled setup";
  - the install in the checkout: the directory's clause fails, and that same condition
    refuses it, with the same message;
  - the install in another directory, `${{ github.workspace }}`: the directory's clause
    fails, and the working-directory condition refuses it;
  - the install after the run: the run of the checks comes first, finds
    `parser_installed` false, and is refused by the second clause of its condition,
    `setup_index != len(setup_order) or not parser_installed`, as "CI check setup
    prefix is incomplete before the first check";
  - the install twice: the second install finds `parser_installed` true, and the
    parser's branch refuses it by `if parser_installed`, as "CI check setup sequence
    differs from the required prefix";
  - the install before elan: it comes with `setup_index` at 2, and the parser's branch
    refuses it by `setup_index != len(setup_order)`, as "CI check setup prefix is
    incomplete before the parser's install";
  - no install: the run of the checks finds `parser_installed` false, and is refused by
    `not parser_installed`, as after the run.

  The plants. Each guard was taken out in a scratch copy of main's tree, never in the
  worktree, and the test was run there, each subtest's outcome read: refused as the test
  expects, accepted (its `assertRaisesRegex` failing with "AssertionError not raised"), or
  refused with another message. Unplanted, the copy's test file is main's, byte for byte,
  and all 37 subtests pass. With the line's equality taken out of `is_parser`, the four
  changed lines in the temporary directory were accepted; with the directory's, the
  install in the checkout and the install in another directory; with
  `if parser_installed` and its refusal, the install twice; with the refusal
  `setup_index != len(setup_order)` in the parser's branch, the install before elan; and
  with the clause `or not parser_installed` of the run's condition, the install after
  the run and no install. In each, every other subtest was refused as the test expects.
  For those ten cases the earlier entry's sentence holds, and its guard of order or
  count is, for the last four, these three.

  The refusals that raise are not those guards. With the working-directory condition
  taken out alone, the four changed lines in the temporary directory and the install in
  another directory were refused all the same, as steps neither setup nor the install.
  With the unmodelled-step condition taken out alone, the four changed lines from the
  checkout and the install in the checkout were refused all the same, by
  `not parser_installed`, as "CI check setup prefix is incomplete before the first
  check", since no install had been seen.

  The correction. The earlier entry says that with both clauses taken out, a changed
  line from the checkout was seen to be accepted. As the code stands, that is not so; how
  that plant was made is not recorded. With both taken out, `is_parser` is
  `step.uses is None`, which the run of the checks, a step of no action too, also meets:
  so the run is taken for a second install, and every job is refused, the unplanted one
  among them. None of the fourteen cases was accepted: twelve, the four changed lines
  from the checkout among them, were refused as "CI check setup sequence differs from
  the required prefix"; the install before elan as before; and no install as "CI check
  job does not run the registry's checks exactly once". The two clauses are still all
  that keep those four lines out, as a plant that keeps the run of the checks apart
  shows: with both taken out and `RUN_CHECKS not in step.run` in their place, each of the
  four was accepted, beside the six cases that one clause alone keeps out. So the earlier
  sentence is true of what decides those four cases, and not of the plain removal of
  both.

  This entry changes no code, no test and no expected value, and approves no file.
