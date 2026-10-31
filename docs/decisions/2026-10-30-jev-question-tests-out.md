<!-- entry: id=jev-question-tests-out cards=861 line="The Jev question generator's tests, which ran in no job and failed on main, are taken out." -->
- **The Jev question generator's tests taken out (tooling,
  [#861](https://github.com/dodecaplex-co/stoicheia/issues/861)).** On 30 October 2026
  the owner said of Jev: "Jev is about quick, cheap, accurate decisions. If it's not that -
  skip it.", then "Use gpt-6-luna instead of Jev. Quick and fast (though not always
  accurate!)", and, of the proposal to take out its question tests among other redundant
  tests: "Yes take these out." Those are the owner's words; what follows is the
  coordinator's record of what they take out.

  `tests/test_jev_questions.py`, the 135 tests of the Jev question generator, is deleted.
  It ran in no CI job and no check of `checks/`: one of its tests checks out a commit of
  19 October that the `check` job's one-commit checkout does not hold. Run on 30 October
  on main (5d10e4b28) with the whole history, that commit included, 55 of its 135 tests
  errored and 6 were skipped. The generator,
  `scripts/audit/jev_questions.py`, stays, since other tests read it. Section 8 of
  `docs/WORKFLOW.md` says so in place of its account of the deleted tests.

  Why: a test that runs in no job guards nothing, and keeping it costs its upkeep.
