- **The lock's writer keeps the header the committed lock has
  ([#260](https://github.com/jackChallis/stoicheia/issues/260)).** On main, `python3
  scripts/check_fidelity.py --write-lock` wrote `Certificate/axioms.lock` with a header
  whose last lines pointed to `docs/decisions/`, while the committed lock's header still
  points to the decisions page. So a lock written again with no axiom and no word changed
  had other bytes and another sha256, and looked like a lock change to the reviews, to the
  pre-flight's guard on the lock and to `model/lock.sha256`, which pins the lock's bytes.
  The writer's header was changed in the pull request that made decision entries files of
  their own, [#239](https://github.com/jackChallis/stoicheia/pull/239); the lock was not
  written again then. So the writer takes back the committed header, byte for byte, and
  the lock itself does not change: this is no lock change. The header still names the
  decisions page as where a decision is recorded, which has been out of date since #239.
  It is to be renewed by a lock change of its own, a follow-up card: `LOCK_HEADER` and the
  lock together, `model/lock.sha256` and `tests/model/lock.sha256` renewed and the model's
  generated files written again, with its decision entry, and nothing else. A lock change
  that comes with Lean cannot carry it, for the pre-flight keeps check code apart from
  what the checks judge.

  This entry approves the change to `scripts/check_fidelity.py`, whose `LOCK_HEADER` is
  the committed lock's header again, with a comment saying why it moves only with the
  lock. This entry approves the new `tests/test_axiom_lock.py`, which needs no Lean:
  written from the committed `facts.json`, the lock comes back byte for byte and the
  writer reports no change; the lock read and rendered again is the same text; and a
  header changed by one character is seen in the bytes, though the writer still reports no
  change, while one word's definition changed in `facts.json`'s data, read into memory, is
  seen both in the bytes and in what the writer reports. This entry approves the change to
  `scripts/negative_tests.py`, which runs the new test after the decision entry
  regressions, before planting, and with `--counts-only` too. Section 8 of
  `docs/WORKFLOW.md` says so in one bullet.
