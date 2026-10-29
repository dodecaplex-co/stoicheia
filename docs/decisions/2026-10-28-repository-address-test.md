- **The pre-flight's test of a GitHub address uses the repository's new home (tooling,
  [#626](https://github.com/dodecaplex-co/stoicheia/issues/626)).** A unit test of
  `github_slug` and `is_local` reads the repository's own address, in its two forms, and
  that address moved to the organization dodecaplex-co on 27 October 2026. The test now
  reads `dodecaplex-co/stoicheia` in both forms and expects that slug. It tests what it
  tested before: the same three assertions, on the same forms of address, with no case
  added or taken away.

  This entry approves the change to [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py),
  whose class `Units` holds those assertions.

  The regressions of the decision entries build the lines `render.py` writes in a notes
  region, each linking its cards at the repository's address, and compare them with lines
  the test writes out in full. Since `render.py` names the new home, the test's issue
  address names it too: one constant, with no case added or taken away.

  This entry approves the change to
  [`tests/test_decision_entries.py`](../../tests/test_decision_entries.py), whose
  constant `ISSUE` holds that address.
