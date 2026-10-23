- **The landing tool reads Lean's comments as Lean does
  ([#349](https://github.com/jackChallis/stoicheia/issues/349)).** Two of the readers
  #206 left out are the landing tool's. `safe_push.statement_end`, which finds where a
  proposition's statement ends for the guard that no statement changes, read a block
  comment's body from its third character and took the `"` of a character literal for a
  string: after `/-/- -/`, a `'"'` or a `'('`, the statement ran to the end of the text,
  so a change after its `:=` would have counted as a statement change. `risk.py`'s
  `past_space`, which reads the Lean headers of the formal model's inputs, read blocks
  the same way: after `/-/- -/` it read no import where Lean reads one, which narrowed
  the model's inputs, against its docstring's claim that a misread header can only
  widen them; and after `/--/` it read an import inside a doc comment and missed the one
  after it. Under the coordinator's ruling of 22 October 23:50, both now read comments
  with the scripts' one reader, which the previous train moved into `heath.py`.
  `statement_end` finds the first `:=` outside brackets in `heath.read_lean(text)`, which
  blanks comments, literals and «…» names in place. `risk.py`, which runs alone and can
  import nothing of the repository's, holds a copy of `heath.comment_end`, word for word,
  and `past_space` steps over each comment by it. Every proposition's statement and
  porism on main reads the same with the new `statement_end` as with the old, 257 in all,
  so the guard judges nothing differently on the edition as it stands.

  This entry approves the change to `scripts/safe_push.py`, whose `statement_end` reads
  through `heath.read_lean`.

  This entry approves the change to `scripts/risk.py`, which holds a copy of
  `heath.comment_end` and reads a header's comments with it.

  This entry approves the change to `scripts/test_safe_push.py`, whose new test plants a
  `/-/- -/`, a `'"'` and a `'('` before a statement's `:=`, with comments, strings and
  names that hold one, and finds each statement ending at its own; the three planted
  cases fail with the old reader.

  This entry approves the change to `tests/test_risk.py`, whose new tests read
  `/-/- -/` and `/--/` before an import as Lean does (they fail with the old reader), and
  hold `risk.py`'s copy of the comment reader to `heath.py`'s by its source and by what it
  reads on a corpus of nested blocks, doc comments, strings, character literals and «…»
  names.
