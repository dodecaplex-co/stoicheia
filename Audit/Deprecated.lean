import Elements

/-!
# Deprecated names: their statements and their warnings

Tag `book-III` declares `Elements.Triangle.of_onCircle`,
`Elements.exists_onCircle_oppositeSidesOf` and `Elements.exists_onCircle_sameSideOf`, Book
Zero lemmas that main later removed. `Elements/Deprecated.lean` declares them again,
deprecated, each pointing to the corollary of III.2 that replaces it
(docs/FORMALIZATION.md, section 2, "A released name stays, or is deprecated first").

For each name, two pins. The `#check` pin shows its statement with every binder, implicit
ones included, so it pins that the alias is the statement `book-III` released. The
`example` states the old theorem's hypotheses, named as at the tag, and applies the old
name to them, as a citer outside the repository would; its pin is Lean's warning, which
names the replacement. A change to either statement, a lost `deprecated` attribute or a
replacement renamed fails `lake build Audit`.
-/

open Elements

/--
warning: `Elements.Triangle.of_onCircle` has been deprecated: Use `Elements.BookIII.Prop2.triangle` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.of_onCircle` to `BookIII.Prop2.triangle x`).

Hint: Replace the deprecated name:
  E̵l̵e̵m̵e̵n̵t̵s̵.̵T̵r̵i̵a̵n̵g̵l̵e̵.̵o̵f̵_̵o̵n̵C̵i̵r̵c̵l̵e̵B̲o̲o̲k̲I̲I̲I̲.̲P̲r̲o̲p̲2̲.̲t̲r̲i̲a̲n̲g̲l̲e̲
---
info: @Triangle.of_onCircle : ∀ {A B C : Point} {α : Circle},
  OnCircle A α → OnCircle B α → OnCircle C α → A ≠ B → B ≠ C → A ≠ C → Triangle A B C
-/
#guard_msgs in
#check @Elements.Triangle.of_onCircle

/--
warning: `Elements.exists_onCircle_oppositeSidesOf` has been deprecated: Use `Elements.BookIII.Prop2.oppositeSide` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.exists_onCircle_oppositeSidesOf` to `BookIII.Prop2.oppositeSide x`).

Hint: Replace the deprecated name:
  E̵l̵e̵m̵e̵n̵t̵s̵.̵e̵x̵i̵s̵t̵s̵_̵o̵n̵C̵i̵r̵c̵l̵e̵_̵o̵p̵p̵o̵s̵i̵t̵e̵S̵i̵d̵e̵s̵O̵f̵B̲o̲o̲k̲I̲I̲I̲.̲P̲r̲o̲p̲2̲.̲o̲p̲p̲o̲s̲i̲t̲e̲S̲i̲d̲e̲
---
info: @exists_onCircle_oppositeSidesOf : ∀ {B C K : Point} {α : Circle},
  OnCircle B α → OnCircle C α → Triangle B C K → ∃ A, OnCircle A α ∧ OppositeSidesOf A K B C
-/
#guard_msgs in
#check @Elements.exists_onCircle_oppositeSidesOf

/--
warning: `Elements.exists_onCircle_sameSideOf` has been deprecated: Use `Elements.BookIII.Prop2.sameSide` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.exists_onCircle_sameSideOf` to `BookIII.Prop2.sameSide x`).

Hint: Replace the deprecated name:
  E̵l̵e̵m̵e̵n̵t̵s̵.̵e̵x̵i̵s̵t̵s̵_̵o̵n̵C̵i̵r̵c̵l̵e̵_̵s̵a̵m̵e̵S̵i̵d̵e̵O̵f̵B̲o̲o̲k̲I̲I̲I̲.̲P̲r̲o̲p̲2̲.̲s̲a̲m̲e̲S̲i̲d̲e̲
---
info: @exists_onCircle_sameSideOf : ∀ {B C K : Point} {α : Circle},
  OnCircle B α → OnCircle C α → Triangle B C K → ∃ A, OnCircle A α ∧ SameSideOf A K B C
-/
#guard_msgs in
#check @Elements.exists_onCircle_sameSideOf

/--
warning: `Elements.Triangle.of_onCircle` has been deprecated: Use `Elements.BookIII.Prop2.triangle` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.of_onCircle` to `BookIII.Prop2.triangle x`).

Hint: Replace the deprecated name:
  E̵l̵e̵m̵e̵n̵t̵s̵.̵T̵r̵i̵a̵n̵g̵l̵e̵.̵o̵f̵_̵o̵n̵C̵i̵r̵c̵l̵e̵B̲o̲o̲k̲I̲I̲I̲.̲P̲r̲o̲p̲2̲.̲t̲r̲i̲a̲n̲g̲l̲e̲
-/
#guard_msgs in
example {A B C : Point} {α : Circle} (hA : OnCircle A α) (hB : OnCircle B α)
    (hC : OnCircle C α) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) : Triangle A B C :=
  Elements.Triangle.of_onCircle hA hB hC hAB hBC hAC

/--
warning: `Elements.exists_onCircle_oppositeSidesOf` has been deprecated: Use `Elements.BookIII.Prop2.oppositeSide` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.exists_onCircle_oppositeSidesOf` to `BookIII.Prop2.oppositeSide x`).

Hint: Replace the deprecated name:
  E̵l̵e̵m̵e̵n̵t̵s̵.̵e̵x̵i̵s̵t̵s̵_̵o̵n̵C̵i̵r̵c̵l̵e̵_̵o̵p̵p̵o̵s̵i̵t̵e̵S̵i̵d̵e̵s̵O̵f̵B̲o̲o̲k̲I̲I̲I̲.̲P̲r̲o̲p̲2̲.̲o̲p̲p̲o̲s̲i̲t̲e̲S̲i̲d̲e̲
-/
#guard_msgs in
example {B C K : Point} {α : Circle} (hB : OnCircle B α) (hC : OnCircle C α)
    (hK : Triangle B C K) : ∃ A : Point, OnCircle A α ∧ OppositeSidesOf A K B C :=
  Elements.exists_onCircle_oppositeSidesOf hB hC hK

/--
warning: `Elements.exists_onCircle_sameSideOf` has been deprecated: Use `Elements.BookIII.Prop2.sameSide` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.exists_onCircle_sameSideOf` to `BookIII.Prop2.sameSide x`).

Hint: Replace the deprecated name:
  E̵l̵e̵m̵e̵n̵t̵s̵.̵e̵x̵i̵s̵t̵s̵_̵o̵n̵C̵i̵r̵c̵l̵e̵_̵s̵a̵m̵e̵S̵i̵d̵e̵O̵f̵B̲o̲o̲k̲I̲I̲I̲.̲P̲r̲o̲p̲2̲.̲s̲a̲m̲e̲S̲i̲d̲e̲
-/
#guard_msgs in
example {B C K : Point} {α : Circle} (hB : OnCircle B α) (hC : OnCircle C α)
    (hK : Triangle B C K) : ∃ A : Point, OnCircle A α ∧ SameSideOf A K B C :=
  Elements.exists_onCircle_sameSideOf hB hC hK
