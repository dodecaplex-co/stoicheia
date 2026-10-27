- **Two count words, for the screen's rules about circles and the superposition audit's
  dependency checks (checks, [#576](https://github.com/jackChallis/stoicheia/issues/576)).**
  The coordinator's orders of 27 October 2026 assign card #576, under the plan the owner
  approved that day for shared files: each thing is said once, and its restatements are
  compiled from it. Two counts in prose restate what a file says exactly, and have been
  retyped by hand when the file changed. So
  [`scripts/generated_counts.py`](../../scripts/generated_counts.py) gains a count word for
  each, read from the file alone, never by importing it, running it or building anything:

  - `screen-circle-rules`, the number of names in `CIRCLE`, the screen's list of rules about
    circles in [`Audit/screen.py`](../../Audit/screen.py). The file is parsed with Python's
    `ast`. `CIRCLE` must be assigned once, at the top level of the module, a string literal
    split with no arguments; it must be bound or changed nowhere else, and must name no rule
    twice. Any other shape is refused, not counted.
  - `superposition-dependency-checks`, the number of `#print axioms` commands in
    [`Audit/Superposition.lean`](../../Audit/Superposition.lean), outside its comments and
    strings, as `read_lean` blanks them. A `#print` of a definition is no dependency check,
    and is not counted. The file is refused where `read_lean` is unsure of a string, and
    where a comment or a string is left open, which `read_lean` reads on to the end of the
    file without counting it unsure.

  Each word has its `:word` and `:Word` forms, as every count does. The words serve the
  sentence of the catalogue of overlaps, [`docs/reports/overlaps.md`](../reports/overlaps.md),
  that says how many of the axioms the screen tries are in its list of rules about circles,
  and the sentence of [brief 0009](../briefs/0009-superposition.md) that says how many
  dependency checks pin the production evidence. Their markers are placed by card #579's
  migrations, not here: this change places none.

  This entry approves the change to
  [`scripts/generated_counts.py`](../../scripts/generated_counts.py), which adds and
  registers the two words, each refusing, by the file's name, anything it cannot count
  exactly.

  This entry approves the change to
  [`tests/test_generated_counts.py`](../../tests/test_generated_counts.py), which gives the
  two words small fixtures of their own, refusal cases for each reader, a case of the words
  filling markers, and a case that the real files read, without stating their values.

  No Lean file, statement, definition, lock, record, page or `--` line changes.
