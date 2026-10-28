- **The pre-flight's test of a GitHub address uses the repository's new home (tooling,
  [#626](https://github.com/dodecaplex-co/stoicheia/issues/626)).** A unit test of
  `github_slug` and `is_local` reads the repository's own address, in its two forms, and
  that address moved to the organization dodecaplex-co on 27 October 2026. The test now
  reads `dodecaplex-co/stoicheia` in both forms and expects that slug. It tests what it
  tested before: the same three assertions, on the same forms of address, with no case
  added or taken away.

  This entry approves the change to [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py),
  whose class `Units` holds those assertions.
