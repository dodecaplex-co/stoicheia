- **Four count words, for the screen's rules about circles, the superposition audit's
  dependency checks, the model's planted mutations and the rules now proved (checks,
  [#576](https://github.com/jackChallis/stoicheia/issues/576)).**
  The coordinator's orders of 27 October 2026 assign card #576, under the plan for shared
  files that the owner approved that day. As the orders give the plan's aim, each thing is
  said once, and its restatements are compiled from it. Four counts in prose restate what
  a file says exactly, and have been retyped by hand when the file changed. So
  [`scripts/generated_counts.py`](../../scripts/generated_counts.py) gains a count word for
  each, read from files alone, never by importing them, running them or building anything.
  Each file is refused, by its name, when it cannot be read, decoded or parsed:

  - `screen-circle-rules`, the number of names in `CIRCLE`, the screen's list of rules about
    circles in [`Audit/screen.py`](../../Audit/screen.py). The file is parsed with Python's
    `ast` from its bytes, so a coding cookie is read as Python reads it. `CIRCLE` must be
    assigned once, at the top level of the module, a string literal split with no
    arguments; it must name no rule twice, and only axioms of
    [`Certificate/axioms.lock`](../../Certificate/axioms.lock), since the prose counts how
    many of the certificate's axioms are in the list. Every other binding of the name is
    refused (an assignment of any kind, a target, a `def`, a parameter or keyword argument,
    an import, a `global`, a pattern's capture or `**rest`, and a star import after the
    assignment), as is every store through it and every call of a method that changes a
    list, as `CIRCLE.append`; a read, as `len(CIRCLE)` or `CIRCLE.index(…)`, counts. What
    reaches the
    list by another name (`globals()`, an alias, `exec`) is left to the review of
    `Audit/`, a protected path.
  - `superposition-dependency-checks`, the number of dependency checks pinned in
    [`Audit/Superposition.lean`](../../Audit/Superposition.lean): a bare `#guard_msgs in`,
    then `#print axioms` and one name, ended as `scripts/check_superposition_pins.py` ends a
    name, outside the comments and strings `read_lean` blanks. The file is read as Lean
    reads its bytes (`lean_text`). It is refused where it holds a lone carriage return,
    where `read_lean` is unsure of a string, where a comment or a string is left open, which
    `read_lean` reads on to the end of the file without counting it unsure, where a `«` is
    left in the code, where a syntax quotation stands, and where any other `#print axioms`
    stands: unguarded, or without one name after it. A `set_option` near a pin does not
    stop the count, which counts pins, not what they print.
  - `model-statement-mutations`, the number of planted mutations in
    [`tests/model/mutations.py`](../../tests/model/mutations.py): its module-level
    `M.append(…)` calls, each of one mutation. The file is parsed as the screen is. `M` must
    be bound once at the top level of the module, as `M = []`, appended to only by those
    calls after it, and bound or changed nowhere else, under the screen's rule. What reaches
    the list by another name is left to the review of `tests/`, a protected path.
  - `rules-now-proved`, the number of rules now theorems: the data rows of the tables in
    the section "Rules now proved" of [`docs/FORMALIZATION.md`](../FORMALIZATION.md), up to
    the next heading of level three or above. Each table there must be headed as a table of
    rules, and each row's first cell must be one theorem's name in backticks, no name given
    twice. A table of another kind, a row of another shape, a line a table would read as a
    row, fenced code, an HTML comment and an underline there are refused, not counted. Each
    count marker's value is taken out before the file is read, so the count never rests on
    a value the generator writes, and a marker can stand in the file.

  Each word has its `:word` and `:Word` forms, as every count does. The words serve the
  sentence of the catalogue of overlaps, [`docs/reports/overlaps.md`](../reports/overlaps.md),
  that says how many of the axioms the screen tries are in its list of rules about circles;
  the sentence of [brief 0009](../briefs/0009-superposition.md) that says how many
  dependency checks pin the production evidence; the row of FORMALIZATION.md's table of
  evidence on the numerical model tests, which gives the number of planted mutations, each
  one weakened statement (two of them weaken the same rule, so the row's wording, "15
  statements", is for the owner of that file to settle when the marker is placed); and the
  sentence of [brief book-I](../briefs/book-I.md) that says how many rules are now
  theorems. Their markers are placed later, by each file's subject owner in a migration of
  its own (card #579 or its like), not here: this change places none. The same row of the
  table of evidence says that fourteen
  of the mutations are of rules; that number stays typed, since `mutations.py` tells a
  mutation of a rule from the one of the placement only by a comment and the free text of
  its name.

  This entry approves the change to
  [`scripts/generated_counts.py`](../../scripts/generated_counts.py), which adds and
  registers the four words, each refusing, by the file's name, anything it cannot count
  exactly.

  This entry approves the change to
  [`tests/test_generated_counts.py`](../../tests/test_generated_counts.py), which gives the
  four words small fixtures of their own, refusal cases for each reader, each paired with
  the phrase it must raise, a case of the words filling markers, and a case that the real
  files read, without stating their values.

  No Lean file, statement, definition, lock, record, page or `--` line changes.
