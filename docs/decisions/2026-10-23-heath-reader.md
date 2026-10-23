- **#206's reader of Lean moves into `heath.py`
  ([#349](https://github.com/jackChallis/stoicheia/issues/349)).** #206 gave the scripts
  one reader of Lean's comments, strings, character literals, raw strings and names, in
  `scripts/check_fidelity.py`. Two readers left out of it are the landing tool's own:
  `safe_push.statement_end` and `risk.py`'s `past_space`. Neither can import
  `check_fidelity`. The harness that runs is origin/main's `safe_push.py` and `heath.py`,
  copied out alone, and origin/main's `risk.py` runs alone from a temporary directory.
  The coordinator's ruling of 22 October 23:50 chose to move the reader into `heath.py`,
  which already travels with the harness, and to give `risk.py` a small pinned copy with
  a test that the two agree. This train makes the move, with no change of behaviour; the
  next brings `safe_push` and `risk.py` to the reader.
  The reader's constants and its ten functions (`read_lean`, `without_comments`,
  `lean_comments`, `comment_end`, `closed_up` and their helpers) move verbatim, but for
  one name: `heath.py` already had a `WORD`, the pattern of its review records' item
  keys, so the reader's, one character `\w` takes, is `WORD_CHAR`. `check_fidelity.py`
  imports the reader under the names it had, the very objects, so every script that
  reads Lean through it (`check_style.py`, `check_acceptance.py`, `render.py`,
  `sweep_citations.py`, `generated_counts.py`, `negative_tests.py`) reads it as before.
  On this train's tree `check_fidelity.py`, `heath.py`, `check_style.py --no-lean`,
  `check_links.py` and `negative_tests.py --counts-only` print exactly what they print on
  main, with the same exit codes, and `render.py` changes nothing. The Jev question
  generator, which takes `comment_end` alone from a file it names, now names `heath.py`.
  Under the coordinator's ruling of 23 October 04:40, three of `CommentReaderTests`, those
  of where the generator finds the reader, change only the reader's file name, the
  message that names it and two test names. In one, `heath.py` now holds the planted
  reader after the line that fails should the helper run first, since it is both the
  reader's file and a helper. Every reading test is unchanged, and a new test holds that
  `check_fidelity`'s reader names are `heath`'s own objects and that it defines none of
  them, so that no second reader can drift apart.

  This entry approves the change to `scripts/heath.py`, which gains #206's reader and
  `functools` for its cache.

  This entry approves the change to `scripts/check_fidelity.py`, which imports the reader
  from `heath.py` in place of defining it.

  This entry approves the change to `scripts/audit/jev_questions.py`, whose `READER` names
  `scripts/heath.py`.

  This entry approves the change to `tests/test_negative_tests.py`, whose three Jev reader
  tests name `heath.py` and whose new test holds the reader to one set of objects.
