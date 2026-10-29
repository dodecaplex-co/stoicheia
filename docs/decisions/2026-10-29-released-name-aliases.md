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
  statement `book-III` released, hypotheses' names included.

  Where a citer finds them. The names now live in the module `Elements.Deprecated`, not in
  `Elements.Figure.OnCircles`, where `book-III` declared them: that module is Book Zero
  and cannot import III.2, and no other module imports it. A citation written against
  `book-III` elaborates as before, with a warning that names the replacement, wherever the
  citer's imports bring in `Elements.Deprecated`, as `import Elements` does. At the tag
  `Elements.Figure.Basics` imported `Elements.Figure.OnCircles`, and every proposition's
  module imports `Basics`; so a citer who imported a single module, as the README's example
  `import Elements.BookI.Prop20` does, had the names too. That citer gets an unknown
  identifier until they add `import Elements.Deprecated`; the release notes say so beside
  the three names.

  The audit. `Audit/Deprecated.lean` pins, for each name, its signature by `#check`, which
  prints every binder by name, the hypotheses' names included, and Lean's warning at a
  use: an `example` that states the old theorem's hypotheses, named as at the tag, and
  applies the old name to them, as a citer outside the repository would. Each pin is the
  whole of what Lean 4.35 prints, under a bare `#guard_msgs`. A change to a statement or
  to a hypothesis's name, a lost `deprecated` attribute or a replacement renamed fails
  `lake build Audit`.

  What does not change. No statement, definition or `--` line; no axiom, so the lock and
  the certificate's axioms are as they were; no proposition's Lean file, so no review
  record goes stale; and no generated file, since the certificate lists propositions,
  porisms and companions, and the aliases are none of these. The citation sweep finds
  nothing in the new module.

  When they go. Each alias stays through the release that first ships it deprecated, and
  may be removed in the release after. As section 2 asks, the notes of the release that
  first ships them list the three names as deprecated, with their replacements and the
  advice on `import Elements.Deprecated` above, and the notes of the release that removes
  them list them as removed. The generated list of names removed or deprecated since the
  last tag ([#702](https://github.com/dodecaplex-co/stoicheia/issues/702)) is to give both
  lists of names; the advice on imports is written into the notes by hand.
  Each `since` is the day the name reaches main: if this train lands on a later day, the
  three dates, in `Elements/Deprecated.lean` and in this entry, move with it.

  This entry approves the new `Audit/Deprecated.lean`, the pins of the three aliases'
  statements and warnings.

  This entry approves the new import of `Audit.Deprecated` in `Audit.lean`.

  This entry claims no approval of the owner's.
