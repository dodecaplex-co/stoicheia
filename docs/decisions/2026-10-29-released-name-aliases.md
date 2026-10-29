<!-- entry: id=released-name-aliases cards=700 line="The three Book Zero names that book-III released and main removed are declared again, deprecated, each pointing to the corollary of III.2 that replaces it." -->
- **Three released names declared again, deprecated (Lean,
  [#700](https://github.com/dodecaplex-co/stoicheia/issues/700)).** The coordinator's
  orders of 29 October 2026, 12:18, assign card #700.
  [FORMALIZATION.md](../FORMALIZATION.md), section 2 ("A released name stays, or is
  deprecated first"), holds that a name a release tag's `Elements` declares, helpers and
  Book Zero included, is never renamed or removed "without a deprecated alias for one
  release". Tag `book-III` declares three Book Zero lemmas of
  `Elements/Figure/OnCircles.lean`: `Elements.Triangle.of_onCircle`,
  `Elements.exists_onCircle_oppositeSidesOf` and `Elements.exists_onCircle_sameSideOf`.
  The entry of 24 October, [Circle 3 retired](2026-10-24-circle-3-retired.md), removed
  them, since they rested on Circle 2 and had no user in the repository, and named their
  replacements, III.2's corollaries `Prop2.triangle`, `Prop2.oppositeSide` and
  `Prop2.sameSide`; but it left no alias, and the rule protects the users outside the
  repository. The release-map gate reader found it. The names that `book-III`'s build
  declares were compared with those of a fresh build of origin/main at 511fb5fe5, by the
  probe of the check that card #700's other train adds: these three are the only names
  of `book-III` that main lacks.

  What this train adds. A new module, `Elements/Deprecated.lean`, imported last by
  `Elements.lean`, declares each name again in the form section 2 gives,
  `@[deprecated <replacement> (since := "2026-10-29")]` on a theorem whose type is
  `type_of%` its replacement and whose proof is the replacement. The aliases point into
  Book III, so they come after III.2, not in Book Zero, which cites no proposition; a
  module of their own, after the books, keeps III.2's file and its review record as they
  are, and is where later aliases go. Each replacement has the old theorem's hypotheses,
  by name, order and type, and its implicit binders, `{A B C : Point} {α : Circle}` and
  `{B C K : Point} {α : Circle}`, as at the tag; so `type_of%` gives each alias the
  statement `book-III` released, and a citation written against `book-III` elaborates as
  before, with a warning that names the replacement.

  The audit. `Audit/Deprecated.lean` pins, for each name, its statement by `#check`, with
  every binder shown, and Lean's warning at a use: an `example` that states the old
  theorem's hypotheses, named as at the tag, and applies the old name to them, as a citer
  outside the repository would. Each pin is the whole of what Lean 4.35 prints, under a
  bare `#guard_msgs`. A change to a statement, a lost `deprecated` attribute or a
  replacement renamed fails `lake build Audit`.

  What does not change. No statement, definition or `--` line; no axiom, so the lock and
  the certificate's axioms are as they were; no proposition's Lean file, so no review
  record goes stale; and no generated file, since the certificate lists propositions,
  porisms and companions, and the aliases are none of these. The citation sweep finds
  nothing in the new module.

  When they go. Each alias stays through the release that first ships it deprecated, and
  may be removed in the release after. That release's notes list the three names with
  their replacements, as section 2 asks; the release map's draft card 03, a generated
  list of every name removed or deprecated since the last tag, is to produce that list.

  This entry approves the new `Audit/Deprecated.lean`, the pins of the three aliases'
  statements and warnings.

  This entry approves the new import of `Audit.Deprecated` in `Audit.lean`.

  This entry claims no approval of the owner's.
