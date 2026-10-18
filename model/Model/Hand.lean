module

public import Model.Signature

/-!
# Translated by hand, for now

**This file is written by hand.** It holds the translation of the laws proved so far, and
of the defined words they reach, until the generator described in the
[README](../README.md) writes every law from the elaborated declarations. When the
generator lands, it replaces this file, and the names here become fields of `Laws`.

Each declaration is the library's, word for word, with `S.Point` for `Elements.Point`,
`S.OnCircle` for `Elements.OnCircle`, and so on. The printed original is quoted above each
law, from `Certificate/axioms.lock`. `Check/Hand.lean` puts the library's own words in
for `S` and asks Lean whether each result is the original declaration; the build fails if
it is not.

The laws here are the circle-intersection rules: Intersection 5, the step Euclid takes for
granted in I.1; Intersection 4, in the corrected form we owe to LeanEuclid (Logan Murphy,
Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si), with our thanks; and
Intersections 8 and 9, which say on which side of the line of centres a crossing point
lies.
-/

@[expose] public section

namespace Model

namespace Signature

variable (S : Signature)

/-- `Elements.OppositeSides`, by hand. -/
def OppositeSides (A B : S.Point) (L : S.Line) : Prop :=
  ¬ S.OnLine A L ∧ ¬ S.OnLine B L ∧ ¬ S.SameSide A B L

/-- `Elements.OutsideCircle`, by hand. -/
def OutsideCircle (A : S.Point) (α : S.Circle) : Prop :=
  ¬ S.InsideCircle A α ∧ ¬ S.OnCircle A α

/-- `Elements.CirclesMeet`, by hand: two circles that cut one another in two points. -/
def CirclesMeet (α β : S.Circle) : Prop :=
  ∃ A B : S.Point, A ≠ B ∧ S.OnCircle A α ∧ S.OnCircle A β ∧ S.OnCircle B α ∧ S.OnCircle B β

end Signature

namespace Hand

variable (S : Signature)

/-- `Elements.Tacit.circles_meet` (Intersection 5), by hand. The lock prints it as
`∀ {A B : Elements.Point} {α β : Elements.Circle}, Elements.OnCircle A α →
Elements.InsideCircle B α → Elements.InsideCircle A β → Elements.OnCircle B β →
Elements.CirclesMeet α β`. -/
def circles_meet : Prop :=
  ∀ {A B : S.Point} {α β : S.Circle}, S.OnCircle A α → S.InsideCircle B α →
    S.InsideCircle A β → S.OnCircle B β → S.CirclesMeet α β

/-- `Elements.Tacit.circles_meet_of_on_inside_outside` (Intersection 4, corrected), by
hand. The lock prints it as `∀ {A B : Elements.Point} {α β : Elements.Circle},
Elements.OnCircle A α → Or (Elements.InsideCircle B α) (Elements.OnCircle B α) →
Elements.InsideCircle A β → Elements.OutsideCircle B β → Elements.CirclesMeet α β`. -/
def circles_meet_of_on_inside_outside : Prop :=
  ∀ {A B : S.Point} {α β : S.Circle}, S.OnCircle A α →
    S.InsideCircle B α ∨ S.OnCircle B α → S.InsideCircle A β → S.OutsideCircle B β →
    S.CirclesMeet α β

/-- `Elements.Tacit.circles_meet_same_side` (Intersection 8), by hand. The lock prints it
as `∀ {α β : Elements.Circle} {B C D : Elements.Point} {L : Elements.Line},
Elements.CirclesMeet α β → Elements.Centre C α → Elements.Centre D β → Elements.OnLine C L →
Elements.OnLine D L → Not (Elements.OnLine B L) → Exists fun (A : Elements.Point) => And
(Elements.OnCircle A α) (And (Elements.OnCircle A β) (Elements.SameSide A B L))`. -/
def circles_meet_same_side : Prop :=
  ∀ {α β : S.Circle} {B C D : S.Point} {L : S.Line}, S.CirclesMeet α β → S.Centre C α →
    S.Centre D β → S.OnLine C L → S.OnLine D L → ¬ S.OnLine B L →
    ∃ A : S.Point, S.OnCircle A α ∧ S.OnCircle A β ∧ S.SameSide A B L

/-- `Elements.Tacit.circles_meet_opposite_side` (Intersection 9), by hand. The lock prints
it as `∀ {α β : Elements.Circle} {B C D : Elements.Point} {L : Elements.Line},
Elements.CirclesMeet α β → Elements.Centre C α → Elements.Centre D β → Elements.OnLine C L →
Elements.OnLine D L → Not (Elements.OnLine B L) → Exists fun (A : Elements.Point) => And
(Elements.OnCircle A α) (And (Elements.OnCircle A β) (Elements.OppositeSides A B L))`. -/
def circles_meet_opposite_side : Prop :=
  ∀ {α β : S.Circle} {B C D : S.Point} {L : S.Line}, S.CirclesMeet α β → S.Centre C α →
    S.Centre D β → S.OnLine C L → S.OnLine D L → ¬ S.OnLine B L →
    ∃ A : S.Point, S.OnCircle A α ∧ S.OnCircle A β ∧ S.OppositeSides A B L

end Hand

end Model
