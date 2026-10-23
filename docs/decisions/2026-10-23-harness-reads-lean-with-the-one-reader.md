- **The landing tool reads Lean's comments as Lean does
  ([#349](https://github.com/jackChallis/stoicheia/issues/349)).** Two of the readers
  #206 left out are the landing tool's. `safe_push.statement_end`, which finds where a
  proposition's statement ends for the guard that no statement changes, read a block
  comment's body from its third character, took the `"` of a character literal for a
  string and the `(` of one for a bracket, and read «…» names as code: after `/-/- -/`, a
  `'"'` or a `'('`, the statement ran to the end of the text, so a change after its `:=`
  would have counted as a statement change; and a `:=` within a name ended it early.
  `risk.py`'s `past_space`, which reads the Lean headers of the formal model's inputs,
  read blocks the same way: after `/-/- -/` it read no import where Lean reads one, which
  narrowed the model's inputs, against its docstring's claim that a misread header can
  only widen them; and it took `/--/` for a whole comment, so it read an import inside
  the doc comment that Lean's tokenizer reads there and missed the one after it. Under the
  coordinator's ruling of 22 October 23:50, both now read comments with the scripts' one
  reader, which the previous train moved into `heath.py`. `statement_end` finds the first
  `:=` outside brackets in `heath.read_lean(text)`, which blanks comments and literals in
  place, with each «…» name blanked whole as `check_fidelity` blanks them, since the
  reader blanks only a name's `[` and `]`; where the reader cannot read a literal for
  certain before that `:=`, or a string there holds a `{`, whose braces the reader may
  keep as a hole of code, the statement runs to the end of the text, so the guard
  compares more of it, never less. `risk.py`, which runs alone and can import nothing of
  the repository's, holds a copy of `heath.comment_end`, word for word, and `past_space`
  steps over each comment by it. All 258 `theorem PropN…` declarations on main, the
  statements and porisms the guard reads among them, read the same with the new
  `statement_end` as with the old, so the guard judges nothing differently on the edition
  as it stands.

  This entry approves the change to `scripts/safe_push.py`, whose `statement_end` reads
  through `heath.read_lean` and blanks «…» names whole.

  This entry approves the change to `scripts/risk.py`, which holds a copy of
  `heath.comment_end` and reads a header's comments with it.

  This entry approves the change to `scripts/test_safe_push.py`, whose new test plants a
  `/-/- -/`, a `'"'` and a `'('` before a statement's `:=`, with comments, strings and
  names that hold one, names at depth 0 among them, and finds each statement ending at
  its own, and one with a literal the reader cannot read for certain, or a string that
  holds a brace, running to the end; the three first planted cases fail with the old
  reader.

  This entry approves the change to `tests/test_risk.py`, whose new tests read
  `/-/- -/` and `/--/` before an import as Lean's tokenizer ends them (they fail with the
  old reader), and hold `risk.py`'s copy of the comment reader to `heath.py`'s, in two
  tests: by its syntax tree, its code and docstring, and by what it reads on a corpus of
  nested blocks, doc comments, strings, character literals and «…» names.
