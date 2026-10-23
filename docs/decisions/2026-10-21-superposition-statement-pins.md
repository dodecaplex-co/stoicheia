- **A check that the restriction's theorems are pinned by their statements (#150,
  question 2).** A check change that lands after the content it reads, since it names the
  theorems that change introduces. New: `scripts/check_superposition_pins.py`
  checks that every theorem and definition named in backticks in brief 0009's section "The
  restriction theorem" has a statement pin in `Audit/Superposition.lean`, a bare
  `#guard_msgs in` over `#check @` for a theorem or `#print` for a definition, under its
  full name in `Elements.Superposition`, its one namespace; a pin in a line, block, nested
  or module comment never counts, and is refused with its line wherever the script reads it
  as a pin (an independent review found that one with an inner comment between quotation
  marks escapes the refusal, though it still counts for nothing), while ordinary comments
  remain allowed, and a section that names nothing fails. The audit file may hold nothing
  but its leading imports, comments and pins, each a docstring, a bare `#guard_msgs in`, then
  `#check @`, `#print` or `#print axioms`. Anything else is refused with its line. An
  independent review showed why: `set_option pp.deepTerms false` with a threshold of 0
  shortens what Lean prints, so that a docstring cut down to match passes `lake build Audit`
  and pins almost nothing (`pp.oneline` and a small `pp.maxSteps` shorten it too), and in a
  namespace a new theorem can take a pinned name. So a `set_option` of any kind,
  `namespace`, `section`, `open`, any declaration, `#eval`, `#exit` and a `#guard_msgs` with
  options (`substring := true`, `drop` and the like) are all refused. A later review showed
  that a `#check` pin shows a definition's type and not its body, so that a field added to
  `Interpretation.Embedding` passed under one. So a `#check` pin is refused when Lean's
  print of its type, in the docstring, shows a definition, by ending in a sort or by opening
  a binder with an arrow where a proposition has `∀`; the docstring is read because it is
  Lean's own account of the declaration, held exact by the build, and the brief marks no
  name as a definition. A further review showed that the signs can be got past: the type of
  a structure declared `: id Type`, a sort spelt through a name, prints as `… → id Type`,
  which shows neither, so a field added to `Interpretation.Embedding` passed again under a
  `#check`. So the two definitions the section names, `Rule.Figure` and
  `Interpretation.Embedding`, are held to `#print` by name: each must have a `#print` pin,
  and a `#check` pin of either is refused whatever it prints. The signs stay, as the
  backstop for a definition the section names later. Another review showed that
  `Elements.BookI`, a second namespace the check then tried, opened a way round: a theorem
  `: True` of the same name there, pinned by `#check` in place of `Embedding`'s `#print`
  pin, let a field be added again, and in place of a theorem's pin it let that theorem be
  weakened. No name the section writes is in `Elements.BookI`. So each is read in
  `Elements.Superposition` alone, and a definition held by name counts as pinned only by its
  `#print` pin. That review also noted that a `#print` pin shows one level and does not pin
  the definitions its body or fields name: so the two held by name must open their prints as
  Lean's do today, `Rule.Figure` with `def` and `Interpretation.Embedding` with `structure`,
  and `Embedding` cannot become a `def` that names a new structure. `Placed`, `Val.place`
  and `Metric.names`, which theorems the section names read, must have `#print` pins too,
  and a statement pin whose docstring holds `⋯` or `[...]`, where Lean cut its print short,
  is refused, wherever the option was set (the lakefile, say, or the default `pp.maxSteps`
  on a long statement). An option that hides part of a print with no mark, such as
  `pp.piBinderTypes false`, is another matter: since the audit file may set no option, it
  could be set only in the lakefile, a protected file, and that protection holds it off, not
  this check. `Audit.lean` must import the audit file, since the `Audit` library builds only
  what its root imports. Its cases are in the new
  `tests/test_check_superposition_pins.py`.
  Both run in CI's check job ([`.github/workflows/ci.yml`](../../.github/workflows/ci.yml)),
  in [`scripts/safe_push.py`](../../scripts/safe_push.py)'s list of checks and in WORKFLOW,
  section 8, in the same order.
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) gains two plants, with
  their regressions in [`tests/test_negative_tests.py`](../../tests/test_negative_tests.py):
  a guard over every point added to `Rule.Figure`, which must fail inside
  `Rule.Figure.restrict` while a control, a guard over the figure alone, compiles (this
  shows the theorem's proof refuses that guard, not that no proof could take it); and a new
  `Cited` law with no proof, which must fail the build at `Cited.holds_all` and nowhere
  else. Nothing is loosened.
