import Elements.BookIII.Prop02

/-!
# Deprecated names

A name that a release declares stays for one release after it is renamed or removed
(docs/FORMALIZATION.md, section 2, "A released name stays, or is deprecated first"). Here
it stays, marked deprecated, dated the day it reaches main and pointing to its
replacement, so that Lean warns at every use and names the replacement. Each may go in
the release after the one that first ships it deprecated.

The module comes after the books, since a replacement may be a proposition's companion
or corollary.
-/

namespace Elements

/-- Released in `book-III` as a Book Zero lemma (`Elements/Figure/OnCircles.lean`), and
removed on 24 October 2026 when Circle 2 was proved after III.2; III.2's corollary
`Prop2.triangle` states the same, with the same binders. -/
@[deprecated Elements.BookIII.Prop2.triangle (since := "2026-10-29")]
theorem Triangle.of_onCircle : type_of% @Elements.BookIII.Prop2.triangle :=
  @Elements.BookIII.Prop2.triangle

/-- Released in `book-III` as a Book Zero lemma (`Elements/Figure/OnCircles.lean`), and
removed on 24 October 2026 when Circle 2 was proved after III.2; III.2's corollary
`Prop2.oppositeSide` states the same, with the same binders. -/
@[deprecated Elements.BookIII.Prop2.oppositeSide (since := "2026-10-29")]
theorem exists_onCircle_oppositeSidesOf : type_of% @Elements.BookIII.Prop2.oppositeSide :=
  @Elements.BookIII.Prop2.oppositeSide

/-- Released in `book-III` as a Book Zero lemma (`Elements/Figure/OnCircles.lean`), and
removed on 24 October 2026 when Circle 2 was proved after III.2; III.2's corollary
`Prop2.sameSide` states the same, with the same binders. -/
@[deprecated Elements.BookIII.Prop2.sameSide (since := "2026-10-29")]
theorem exists_onCircle_sameSideOf : type_of% @Elements.BookIII.Prop2.sameSide :=
  @Elements.BookIII.Prop2.sameSide

end Elements
