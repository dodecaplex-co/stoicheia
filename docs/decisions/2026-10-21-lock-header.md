- **The lock's writer keeps the header the committed lock has
  ([#260](https://github.com/jackChallis/stoicheia/issues/260)).** On main, `python3
  scripts/check_fidelity.py --write-lock` wrote `Certificate/axioms.lock` with a header
  whose last lines pointed to `docs/decisions/`, while the committed lock's header still
  points to the decisions page. So a lock written again with no axiom and no word changed
  had other bytes and another sha256, and looked like a lock change to the reviews, to the
  pre-flight's guard on the lock and to `model/lock.sha256`, which pins the lock's bytes.
  The writer's header was changed in the pull request that made decision entries files of
  their own; the lock was not written again then, and a header change alone would have
  renewed the model's hashes and the model's generated files for nothing. So the writer
  takes back the committed header, byte for byte, and the lock itself does not change:
  this is no lock change. The header still names the decisions page as where a decision is
  recorded; it is renewed with the next change of the lock, when `LOCK_HEADER` and the
  lock change together and the model's hashes are renewed with them.

  This entry approves the change to `scripts/check_fidelity.py`, whose `LOCK_HEADER` is
  the committed lock's header again, with a comment saying why it moves only with the
  lock. This entry approves the new `tests/test_axiom_lock.py`, which needs no Lean:
  written from the committed `facts.json`, the lock comes back byte for byte and the
  writer reports no change; the lock read and rendered again is the same text; and a
  header changed by one character, or a word of the vocabulary changed in a copy of
  `facts.json`, makes each comparison fail. This entry approves the change to
  `scripts/negative_tests.py`, which runs the new test after the decision entry
  regressions, before planting, and with `--counts-only` too. Section 8 of
  `docs/WORKFLOW.md` says so in one bullet.
