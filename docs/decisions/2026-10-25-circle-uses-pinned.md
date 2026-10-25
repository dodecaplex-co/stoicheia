- **No entry's shared steps may name Circle 2, Circle 3 or Intersection 2, and a page
  counts as its own only the lemmas its proofs use (tooling,
  [#429](https://github.com/jackChallis/stoicheia/issues/429)).** The coordinator's orders
  of 24 October 2026 assign card #429, from the reviews of that day, after #294. Two
  claims about the proved circle rules were kept by review alone, and one script counted
  too much as a page's own. The train changes no Lean file, lock, statement or
  definition, nor any `--` line; `facts.json` stays as it was.

  Book III's introduction says of Circle 2 and Circle 3 that no proof here uses either.
  Section 7 of the formalization guide says that no certificate entry uses them, and that
  the proved Intersection 2 has no user in the published proofs; the catalogue of overlaps
  says the same of Intersection 2. All three are theorems proved after III.2, in
  `Elements/BookIII/Prop02.lean`, and `proved_rule_cites` gives III.2 for each. In
  `Certificate/Facts.lean`, `sharedSteps` walks from an entry through its own
  declarations, the theorem, the helpers in its proposition's namespace and Lean's
  auxiliary declarations, and records, without going further, each other declaration of
  the project it meets that is not an entry, an axiom or a Common Notion; `shared_steps`
  keeps those that bring in an entry. So an entry whose own Lean called one of the three
  rules would list it there. At commit 1e0619d no entry lists any of them, or Points 9,
  and no Lean under `Elements/` names any of those four rules outside the declarations in
  `Prop02.lean`.

  A new form of expectation, `"every": "entry"` with no `ref`, reads one field in every
  entry, porisms and companions included, and asks only that it `excludes` some names;
  there a list of objects, as `shared_steps` is, is read by each object's `name`. An entry
  without the field, a step without a name, and a `facts.json` with no entries each fail,
  since each would otherwise let the pin pass. One expectation of this form keeps the
  three rules out of the `shared_steps` of all 140 entries. An expectation naming one
  entry still refuses to read `shared_steps` by name, as a test from #150's review asks.
  The pre-flight compares a key it has no rule for, such as `every`, exactly, so
  dropping or altering it later is a check change, as dropping a `ref` is.

  What the pin cannot see is a rule called only through another lemma outside the entry's
  namespace, one of `Elements/BookIII/MixedAngles.lean`, say, or another proposition's
  helper: that lemma is listed instead, with III.2 among what it brings in. Nineteen
  shared steps bring in III.2 at that commit, and none of them names a circle rule; that
  case stays with review, and the expectation's reason says so. Points 9 is left out,
  since no page says it is unused and a proof after III.2 may call it; adding its name
  later only grows the list, a pinned value.

  On scratch copies of `facts.json`, outside the repository, `check_fidelity.py --facts`
  failed, naming the entry and the rule, with Circle 3 added to III.10's shared steps,
  Circle 2 to III.16 Por.'s and Intersection 2 to III.31 less's; it failed too with
  III.10's `shared_steps` taken away, and with a step that has no name added to it; with
  Points 9 added to III.10's it passed, as it should. On the real `facts.json` it passes.
  Three new tests read the form on small facts, and fail against the checker as it stood
  before.

  `scripts/render.py` called a declaration after a page's theorem a lemma "for its own
  proofs" whenever another declaration of its file used it. Now it does so only when the
  page's own proofs, its theorem, its porism and its companions, use it, or use a
  declaration of the file that uses it, at any remove, a private one included. A
  declaration used only by others that those proofs never reach goes with the lemmas
  beside the proposition, whose words stay true of it: it stands beside the proposition,
  outside its proofs. A name made at the root is now found as the edition writes it:
  `_root_.Elements.Tacit.adjacent_eq_of_right` as `Tacit.adjacent_eq_of_right`, or as
  `adjacent_eq_of_right` after `open Tacit`, where before only the full name, which no
  file writes, was looked for.

  Two pages change. III.16's moves twelve lemmas from its own proofs to beside it: the
  comparisons at another vertex, with the semicircle's and the horn's lemmas that serve
  them, and `Prop16.semicircle_nearVertex`; each serves only `Prop16.semicircle_lt_right`
  or one of the three `compare_alike` lemmas, which nothing in `Elements/` uses. I.13's
  now says that later propositions use `Tacit.adjacent_eq_of_right`, as thirteen files
  under `Elements/` do, where it called the rule a lemma beside the proposition. Before
  this change the script read III.2's four proved rules as beside the proposition,
  rightly, since nothing calls them there, and I.13's rule so too, wrongly, for it looked
  only for the full name that no file writes. The script's own check gains nine cases for
  these readings, and its eleven earlier cases keep their answers, `Fitted.fan.growth`
  now through a companion added to the check's made-up file.

  This entry approves the change to `scripts/check_fidelity.py`, which reads the new form
  of expectation over every entry and fails it when it is malformed, cannot be read, or
  is broken by any entry.

  This entry approves the change to `scripts/render.py`, whose `use_kind` counts a lemma
  as the page's own only when the page's proofs reach it, and reads a name made at the
  root as the edition's Lean writes it, with nine new cases in its own check.

  This entry approves the change to `tests/certificate_expectations.json`, which gains the
  expectation over every entry's shared steps and a sentence of its `about` on that form;
  no expectation or listed name is removed.

  This entry approves the change to `tests/test_certificate.py`, which gains three tests
  of the new form, a class of two tests that runs the certificate on a fixture written in
  the file, where an entry that calls a proved rule itself lists it among its shared
  steps and one that calls it only through another lemma lists that lemma instead, and
  words on both in its docstrings.

  This entry approves the change to `Certificate/FIELDS.md`, whose row for `shared_steps`
  now says when a proved rule is listed there and what is pinned, and whose list of
  readers names the pin.
