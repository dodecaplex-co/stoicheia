module

public import Model.Hand

/-!
# The intersection rules, translated by hand

**This file is written by hand: hand-translated.** It holds the translation of the
intersection rules beyond `Model/Hand.lean`, and separate hand copies of the two defined
words they reach in `Hand.Intersections`. The generator described in the
[README](../../README.md) writes every law from its elaborated declaration.
`Check/Intersections.lean` compares each locked law and hand word here with its generated
counterpart. The retired rules `line_meets_circle_of_opposite_sides`,
`line_meets_circle_of_inside`, `between_of_inside_chord`, `inside_of_between`,
`outside_of_between` and `not_same_side_of_circles_meet` are compared directly with their
library declarations. Since 19 October 2026 no locked law
reaches `Elements.LineMeetsCircle`, so the generator no longer writes it, and Intersections 2
and 3 use the hand copy here, itself checked against the library's word. Their concrete plane proofs remain as derived facts, with no
generated assumption fields. Overlapping translations keep their statements under
distinct names.

Each declaration is the library's, word for word, with `S.Point` for `Elements.Point`,
`S.OnLine` for `Elements.OnLine`, and so on. The printed original is quoted above each
law, from the lock or its unchanged theorem type. `Check/Intersections.lean` puts the
library's own words in for `S` and asks Lean whether each result is the original
declaration; the build fails if it is not.

System E numbers its intersection rules 1 to 9, and the library keeps two groups of them.
The diagram rules say *that* a crossing exists: Intersection 1 (a line joining points
on opposite sides of a line crosses it), 2 (a line separating two
points on or inside a circle cuts it), 3 (a line through a point inside a circle cuts it),
4 in LeanEuclid's corrected form and 5 (two circles cut one another). In
`Tacit/Constructions.lean`, the rules that say *where* the crossing lies: Intersections 4
and 5 there (a line through a point inside a circle cuts it between that point and a point
outside, and beyond that point on the side away from any other point of the line), and 8
and 9 (two circles cut one another on each side of the line of centres). The two circle
laws of each group are in `Model/Hand.lean` already; the five line laws are here.

With them are the four circle rules, which say where a line and a circle, or two circles,
meet: Circle 1 (a point inside on a chord's line lies between the
chord's ends), 2 (between two points on or inside a circle, every point is inside), 3
(once a line has left a circle it does not come back), and 4 (two circles cut one another
on opposite sides of the line of centres).
-/

@[expose] public section

namespace Model

namespace Hand.Intersections

variable (S : Signature)

/-- `Elements.LineMeetsCircle`, by hand: a line that cuts a circle in two points. -/
def LineMeetsCircle (L : S.Line) (α : S.Circle) : Prop :=
  ∃ A B : S.Point,
    A ≠ B ∧ S.OnLine A L ∧ S.OnCircle A α ∧ S.OnLine B L ∧ S.OnCircle B α

/-- `Elements.LinesMeet`, by hand: two different lines with a common point. -/
def LinesMeet (L M : S.Line) : Prop :=
  L ≠ M ∧ ∃ A : S.Point, S.OnLine A L ∧ S.OnLine A M

end Hand.Intersections

namespace Hand

variable (S : Signature)

/-! ## That a line crosses a line or a circle -/

/-- `Elements.Tacit.lines_meet_of_opposite_sides` (Intersection 1), by hand. The lock
prints it as `∀ {A B : Elements.Point} {L M : Elements.Line}, Elements.OppositeSides A B L →
Elements.OnLine A M → Elements.OnLine B M → Elements.LinesMeet L M`. -/
def lines_meet_of_opposite_sides_intersections : Prop :=
  ∀ {A B : S.Point} {L M : S.Line}, S.OppositeSides A B L → S.OnLine A M → S.OnLine B M →
    S.LinesMeet L M

/-- `Elements.Tacit.line_meets_circle_of_opposite_sides` (Intersection 2), by hand.
The theorem's unchanged type is
`∀ {A B : Elements.Point} {L : Elements.Line} {α : Elements.Circle}, Or
(Elements.InsideCircle A α) (Elements.OnCircle A α) → Or (Elements.InsideCircle B α)
(Elements.OnCircle B α) → Elements.OppositeSides A B L → Elements.LineMeetsCircle L α`. -/
def line_meets_circle_of_opposite_sides : Prop :=
  ∀ {A B : S.Point} {L : S.Line} {α : S.Circle}, S.InsideCircle A α ∨ S.OnCircle A α →
    S.InsideCircle B α ∨ S.OnCircle B α → S.OppositeSides A B L →
    Intersections.LineMeetsCircle S L α

/-- `Elements.Tacit.line_meets_circle_of_inside` (Intersection 3), by hand. The theorem's unchanged type
is `∀ {A : Elements.Point} {L : Elements.Line} {α : Elements.Circle},
Elements.InsideCircle A α → Elements.OnLine A L → Elements.LineMeetsCircle L α`. -/
def line_meets_circle_of_inside : Prop :=
  ∀ {A : S.Point} {L : S.Line} {α : S.Circle}, S.InsideCircle A α → S.OnLine A L →
    Intersections.LineMeetsCircle S L α

/-! ## Where a line crosses a circle -/

/-- `Elements.Tacit.line_circle_between` (Intersections 4 of `Tacit/Constructions.lean`), by
hand. The lock prints it as `∀ {B C : Elements.Point} {L : Elements.Line} {α :
Elements.Circle}, Elements.InsideCircle B α → Elements.OnLine B L → Elements.OutsideCircle
C α → Elements.OnLine C L → Exists fun (A : Elements.Point) => And (Elements.OnCircle A α)
(And (Elements.OnLine A L) (Elements.Between B A C))`. -/
def line_circle_between : Prop :=
  ∀ {B C : S.Point} {L : S.Line} {α : S.Circle}, S.InsideCircle B α → S.OnLine B L →
    S.OutsideCircle C α → S.OnLine C L →
    ∃ A : S.Point, S.OnCircle A α ∧ S.OnLine A L ∧ S.Between B A C

/-- `Elements.Tacit.line_circle_beyond` (Intersections 5 of `Tacit/Constructions.lean`), by
hand. The lock prints it as `∀ {B C : Elements.Point} {L : Elements.Line} {α :
Elements.Circle}, Elements.InsideCircle B α → Elements.OnLine B L → Elements.OnLine C L →
Ne C B → Exists fun (A : Elements.Point) => And (Elements.OnCircle A α) (And
(Elements.OnLine A L) (Elements.Between A B C))`. -/
def line_circle_beyond : Prop :=
  ∀ {B C : S.Point} {L : S.Line} {α : S.Circle}, S.InsideCircle B α → S.OnLine B L →
    S.OnLine C L → C ≠ B →
    ∃ A : S.Point, S.OnCircle A α ∧ S.OnLine A L ∧ S.Between A B C

/-! ## The circle rules -/

/-- `Elements.Tacit.between_of_inside_chord` (Circle 1), by hand.
The theorem's unchanged type is
`∀ {A B C : Elements.Point} {L : Elements.Line} {α : Elements.Circle}, Elements.OnLine A L
→ Elements.OnLine B L → Elements.OnLine C L → Elements.InsideCircle A α →
Elements.OnCircle B α → Elements.OnCircle C α → Ne B C → Elements.Between B A C`. -/
def between_of_inside_chord_intersections : Prop :=
  ∀ {A B C : S.Point} {L : S.Line} {α : S.Circle}, S.OnLine A L → S.OnLine B L →
    S.OnLine C L → S.InsideCircle A α → S.OnCircle B α → S.OnCircle C α → B ≠ C →
    S.Between B A C

/-- `Elements.Tacit.inside_of_between` (Circle 2), by hand.
The theorem's unchanged type is
`∀ {A B C : Elements.Point} {α : Elements.Circle}, Or (Elements.InsideCircle A α)
(Elements.OnCircle A α) → Or (Elements.InsideCircle B α) (Elements.OnCircle B α) →
Elements.Between A C B → Elements.InsideCircle C α`. -/
def inside_of_between_intersections : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.InsideCircle A α ∨ S.OnCircle A α →
    S.InsideCircle B α ∨ S.OnCircle B α → S.Between A C B → S.InsideCircle C α

/-- `Elements.Tacit.outside_of_between` (Circle 3), by hand.
The theorem's unchanged type is
`∀ {A B C : Elements.Point} {α : Elements.Circle}, Or (Elements.InsideCircle A α)
(Elements.OnCircle A α) → Not (Elements.InsideCircle C α) → Elements.Between A C B →
Elements.OutsideCircle B α`. -/
def outside_of_between_intersections : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.InsideCircle A α ∨ S.OnCircle A α →
    ¬ S.InsideCircle C α → S.Between A C B → S.OutsideCircle B α

/-- `Elements.Tacit.not_same_side_of_circles_meet` (Circle 4), by hand.
The theorem's unchanged type is
`∀ {A B C D : Elements.Point} {L : Elements.Line} {α β : Elements.Circle}, Ne α β →
Elements.OnCircle C α → Elements.OnCircle C β → Elements.OnCircle D α → Elements.OnCircle
D β → Ne C D → Elements.Centre A α → Elements.Centre B β → Elements.OnLine A L →
Elements.OnLine B L → Not (Elements.SameSide C D L)`. -/
def not_same_side_of_circles_meet_intersections : Prop :=
  ∀ {A B C D : S.Point} {L : S.Line} {α β : S.Circle}, α ≠ β → S.OnCircle C α →
    S.OnCircle C β → S.OnCircle D α → S.OnCircle D β → C ≠ D → S.Centre A α →
    S.Centre B β → S.OnLine A L → S.OnLine B L → ¬ S.SameSide C D L

end Hand

end Model
