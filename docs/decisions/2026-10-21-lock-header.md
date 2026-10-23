- **The lock is written again byte for byte, by a test
  ([#260](https://github.com/jackChallis/stoicheia/issues/260)).** For a time, `python3
  scripts/check_fidelity.py --write-lock` wrote `Certificate/axioms.lock` with a header
  whose last lines pointed to `docs/decisions/`, while the committed lock's header still
  pointed to the decisions page: the writer's header was changed in the pull request that
  made decision entries files of their own,
  [#239](https://github.com/jackChallis/stoicheia/pull/239), and the lock was not written
  again then. So a lock written again with no axiom and no word changed had other bytes
  and another sha256, and looked like a lock change to the reviews, to the pre-flight's
  guard on the lock and to `model/lock.sha256`, which pins the lock's bytes. The lock
  change of [#342](https://github.com/jackChallis/stoicheia/pull/342), which gave the lock
  the outline companions' words, wrote it again with the writer's header, so on main the
  two now agree. Nothing held them together, though, and nothing would have caught the
  next such drift. Now `tests/test_axiom_lock.py` does: from the committed `facts.json`,
  the writer must give back the committed lock byte for byte, its header included. The
  header and the lock change only together, as a lock change. `LOCK_HEADER` itself is
  unchanged; a comment above it says why it moves only with the lock.

  This entry approves the change to `scripts/check_fidelity.py`, a comment above
  `LOCK_HEADER` saying that it is the committed lock's header byte for byte and changes
  only with the lock. This entry approves the new `tests/test_axiom_lock.py`, which needs
  no Lean: written from the committed `facts.json`, the lock comes back byte for byte and
  the writer reports no change; the lock read and rendered again is the same text; and a
  header changed by one character is seen in the bytes, though the writer still reports no
  change, while one word's definition changed in `facts.json`'s data, read into memory, is
  seen both in the bytes and in what the writer reports. This entry approves the change to
  `scripts/negative_tests.py`, which runs the new test after the risk class
  regressions, before planting, and with `--counts-only` too. Section 8 of
  `docs/WORKFLOW.md` says so in one bullet.
