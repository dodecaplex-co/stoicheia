- **The fidelity and style checks and the Jev generator read where a Lean comment
  ends with one reader, as Lean 4.35 does, save the docstrings that heath and render
  find by a pattern (#206).**
  Lean begins a block comment's body at its fourth character: after `/--` or
  `/-!`, and past the third character of any other `/-`, which it passes over
  (`whitespace` and `finishCommentBlock`, in `Lean/Parser/Basic.lean`). So `/-/- -/` is
  one whole comment, and the `-/` of `/--/` closes nothing: the doc comment runs on to a
  later `-/`. The train of #32 corrected
  `read_lean` in [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py) to read
  so. Three more readers in the scripts, mended here, began the body at the third
  character:
  `_blank_remarks`, which blanks the remarks of a proposition's proof before its runs of
  `--` lines are read, and so decides where a run ends and which Lean stands beneath it;
  check_style's `lean_note_spans`, which finds the notes the style rules read; and the Jev
  question generator's `comment_end`. The first two read no strings or character literals
  either. Each took the `/-/-` of `/-/- -/` for two openings: the first read the rest of
  the theorem as remark, the second found no note from there to the end of the file, and
  the third refused the file as holding an unterminated comment. No tracked Lean file
  holds `/-/`, so no check passed quietly because of them, but a run boundary could
  disagree with Lean's.

  Now one function says where a comment ends: `comment_end`, in check_fidelity.py, given
  the place a comment begins, returns where Lean ends it, or nothing for a block that no
  `-/` closes. `_read_code`, which `read_lean` runs, calls it and marks each comment it
  reads, and `lean_comments` gives those comments, so that a `/-` in a string, a
  character literal or a `--` comment begins none. `_blank_remarks` blanks the blocks
  `lean_comments` gives, where it had counted openings and closings of its own, and so
  does `theorem_block`, which gathers the `--` lines that are compared with Heath, where
  it had cut each remark at its first `-/` by a pattern. check_style's `lean_note_spans`
  takes its notes from `lean_comments`. The Jev generator's `comment_end` calls
  check_fidelity's, taken alone from that file's checked bytes, since the file imports
  modules by name that a generator run by path, as with `python3 -I`, cannot import.
  Where a comment begins is still the generator's own lexer's to say, as before: it
  reads strings but no character literals, and its refusals for what it may misread,
  `'"'` among them, stand, as does its refusal of `/--/`.

  Nothing a check reads in the tree changes. Over every tracked file, `read_lean` gives
  what it gave before, byte for byte, and so do `proof_lines`, `uncarried_runs`,
  `runs_beneath` and `theorem_block` for each of the 99 propositions, and the Jev
  generator's index and its 328 rows before the controls; `check_fidelity.py` and
  `check_style.py` print what they printed before. Run over the files of its evidence
  commit, `39ae65c2`, the generator gives the rows and the manifest it gave before, byte
  for byte. check_style's notes differ only in two files that it does not read,
  `model/Check/Generator.lean` and `model/Check/RoundTrip.lean`, where the old reader took
  text in string literals for notes.

  Two kinds of text, which no tracked Lean file holds, now read otherwise, and a check
  can pass on them where it failed before. A `--` line within a remark that nests another,
  or that runs on past the theorem's end, is remark to `theorem_block` now, as it is to
  Lean and was already to `proof_lines`, so it is not compared with Heath; one within a
  plain remark was not compared before either. And the readers now read strings and
  character literals as the source scan does, so they share its open gaps
  ([#317](https://github.com/jackChallis/stoicheia/issues/317)): after Lean's token
  `⊕'`, `×'` or `]'` closed up to a `"`, the scan reads a string that Lean does not,
  and a remark within it is text, which `proof_lines` takes for Lean beneath a run and
  check_style for no note, where a reader that read no strings read the remark as Lean
  does. That needs text by which the same gap already hides code from the source scan.

  The cases where the readings could differ are now tests: `/-/- -/`, `/-/ x -/`,
  `/-/-/`, `/--/` before a later `-/`, `/-!/ x -/`, a nested comment, `"/-"` in a string,
  a `"` before a comment's `-/`, character literals `'-'` and `'/'` closed up to a comment
  and `'"'` before one, a `--` within a block, a `/-` within a `--` comment, a comment in
  an interpolated string's hole, and two blocks not closed at the end of a file. Each was
  elaborated in Lean 4.35 as written, alone in a scratch file outside the tree, and its
  expected reading is Lean's: the names after its comments are defined, those within them
  are unknown, and the two not closed are refused as unterminated comments.
  The tests feed the shared reader each case, then the three readers that call it, and
  check that the Jev generator runs check_fidelity's own function. Each reader as it was
  fails them. Plant 30 of the negative tests writes a remark `/-/- … -/` in I.5 before a
  sentence that a plain remark then leaves with no Lean: the check names the sentence, and
  no passage of I.5's record is said to begin no sentence. check_fidelity.py as it was
  misses the sentence, reading the rest of the theorem as remark, and reports three of
  the record's passages as beginning no sentence.

  A search of `scripts/` found five more readers of Lean comments, which read otherwise
  and are not changed here. `statement_end` in `scripts/safe_push.py`, the landing tool,
  begins a block's body at its third character too, and reads no character literals, raw
  strings or «…» names: its change is left to a card of its own,
  [#349](https://github.com/jackChallis/stoicheia/issues/349). So is `past_space` in
  `scripts/risk.py`, which reads the header of a Lean file so; after `/-/- -/` it reads no
  import, where Lean reads on. `heath.theorem_span`, and the pattern by which
  `render.load_axiom_docs` and check_style read an axiom's docstring, begin a docstring's
  text after its `/--`, as Lean does, but end it at the first `-/`, so a docstring that
  holds a nested comment is not found at all; check_style keeps render's pattern, since it
  checks the docstrings that render shows. And `heath.theorem_span` ends a theorem at
  the first line that begins with `end `, `theorem `, `lemma `, `def `, `structure `,
  `/--`, `/-!` or `@[`, even within a remark. These two are left as they are, and to the
  same card, #349. A theorem's docstring that heath does not find fails the fidelity check
  aloud ("no documented `theorem PropN` found"), unless heath finds another: it reads no
  comments, so a `/-- … -/ theorem PropN` written within a remark above the theorem is
  taken for it, and the theorem's own docstring and `--` lines are compared with
  nothing; only the stale review record shows the change. That gap is older than this
  change, and is left to #349 too. An axiom's docstring that render's pattern does
  not find would be missing from its page without a failure, but none of the 971
  docstrings under `Elements/` holds a `/-` before its first `-/`, so none is missed
  today.

  This entry approves the one comment reader in [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py),
  `comment_end` and `lean_comments`, and that file's `_blank_remarks` and `theorem_block`,
  which read remarks by it.

  This entry approves the change to [`scripts/check_style.py`](../../scripts/check_style.py),
  whose `lean_note_spans` reads the notes of a Lean file by check_fidelity's reader.

  This entry approves the change to [`scripts/audit/jev_questions.py`](../../scripts/audit/jev_questions.py),
  whose `comment_end` calls check_fidelity's, taken alone from that file.

  This entry approves the change to [`tests/test_jev_questions.py`](../../tests/test_jev_questions.py),
  which copies check_fidelity.py beside today's generator in its checkout of the
  evidence commit, since the generator takes its comment reader from that file.

  This entry approves plant 30 of [`scripts/negative_tests.py`](../../scripts/negative_tests.py),
  a remark written `/-/- … -/` in I.5 before a sentence left with no Lean.

  This entry approves the change to [`tests/test_negative_tests.py`](../../tests/test_negative_tests.py),
  which gains the cases of the shared comment reader and of the three readers that
  call it.
