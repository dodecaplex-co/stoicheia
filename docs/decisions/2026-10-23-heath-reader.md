- **#206's reader of Lean moves into `heath.py`
  ([#349](https://github.com/jackChallis/stoicheia/issues/349)).** #206 gave the scripts
  one reader of Lean's comments, strings, character literals, raw strings and names, in
  `scripts/check_fidelity.py`. Two readers left out of it are the landing tool's own:
  `safe_push.statement_end` and `risk.py`'s `past_space`. Neither can import
  `check_fidelity`. The harness that runs is origin/main's `safe_push.py` and `heath.py`
  (and `check_train.py`, for a train), copied out alone, and origin/main's `risk.py` runs
  alone from a temporary directory. The coordinator's ruling of 22 October 23:50 chose to
  move the reader into `heath.py`, which already travels with the harness, and to give
  `risk.py` a small pinned copy with a test that the two agree. This train makes the
  move, with no change of behaviour; the next brings `safe_push` and `risk.py` to the
  reader.
  The reader's constants and its ten functions (`read_lean`, `without_comments`,
  `lean_comments`, `comment_end`, `closed_up` and their helpers) move verbatim, but for
  one name: `heath.py` already had a `WORD`, the pattern of its review records' item keys
  and tags, so the reader's, one character `\w` takes, is `WORD_CHAR`, with a comment
  saying so. `comment_end`'s docstring now says who holds copies of it.
  `check_fidelity.py` imports the reader under the names it had, the very objects, so
  every script that reads Lean through it (`check_style.py`, `check_acceptance.py`,
  `render.py`, `sweep_citations.py`, `generated_counts.py`, `negative_tests.py`) reads it
  as before.
  On this train's tree `check_fidelity.py`, `heath.py`, `check_style.py --no-lean` and
  `negative_tests.py --counts-only` print exactly what they print on main, with the same
  exit codes, and so does `check_links.py` but for its count of Markdown files, which
  gains this entry; `render.py` changes nothing.
  The Jev question generator read `comment_end` alone from `check_fidelity.py`. It must
  also read the evidence commit's `heath.py` as a helper, and at the evidence commit of
  19 October, `heath.py` has no reader, so it cannot read the reader from there. Under the
  coordinator's ruling of 23 October 05:20, which supersedes the file-path detail of the
  ruling of 23 October 04:40, it holds its own copy of `comment_end`, word for word but
  for its name, `shared_comment_end`, in place of reading one from a file, and the
  evidence of 19 October regenerates again: `tests/test_jev_questions.py`'s check at that
  commit passes, and no longer copies `check_fidelity.py` into its checkout. Of
  `CommentReaderTests`, the three tests of where the generator found its reader now test
  its copy: that it is `heath.comment_end` by its syntax tree, that it reads as heath's
  does on a corpus of nested blocks, doc comments, strings, character literals and «…»
  names, and, unchanged but for its name, that the generator returns its copy's reading
  and refuses an unclosed comment through it. Every
  reading test is unchanged, and a new test holds that `check_fidelity`'s reader names,
  functions and constants, are `heath`'s own objects and that it binds none of them
  itself. So #206's purpose, one reading of comments, holds, enforced by identity tests on
  every copy.

  This entry approves the change to `scripts/heath.py`, which gains #206's reader and
  `functools` for its cache.

  This entry approves the change to `scripts/check_fidelity.py`, which imports the reader
  from `heath.py` in place of defining it.

  This entry approves the change to `scripts/audit/jev_questions.py`, which holds a copy
  of `heath.comment_end` in place of reading one from a file.

  This entry approves the change to `tests/test_negative_tests.py`, whose Jev reader tests
  test the generator's copy and whose new test holds the reader to one set of objects.

  This entry approves the change to `tests/test_jev_questions.py`, whose evidence-commit
  check no longer copies `check_fidelity.py` into its checkout.
