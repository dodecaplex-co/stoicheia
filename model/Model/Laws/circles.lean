module

public import Model.Hand

/-!
# The circle rules, translated by hand

**Hand-translated.** Each statement here is the library's law, word for word, with
`S.Point` for `Elements.Point`, `S.OnCircle` for `Elements.OnCircle`, and so on, as in
`Model/Hand.lean`. The printed original is quoted above each law, from
the lock or, for a retired rule, its unchanged theorem type. `Check/Circles.lean` puts the
library's own words in for `S` and asks the kernel whether each result is the original
declaration; the build fails if it is not. The generator described in the
[README](../../README.md) writes the laws from the elaborated declarations, and
`Check/Circles.lean` also compares each locked law's translation here with
its generated field. The retired rules `centre_unique`, `between_of_inside_chord`,
`inside_of_between`, `outside_of_between`, `not_same_side_of_circles_meet` and
`exists_point_outside_circle` are compared directly with their library declarations,
including binder kinds. Their concrete plane proofs
remain as derived facts, with no generated assumption fields. Overlapping translations
keep their statements under distinct names.

The laws here are those about a single circle, or about where a circle and its points lie:

* Postulate 3, which draws a circle, and Definition 15, which makes its radii equal;
* the generalities about a centre (`centre_unique`, `centre_inside`, `circle_eq`), with our
  own rule that a radius is not nothing (`radius_ne_zero`), and about the inside of a
  circle (`inside_not_on`, `inside_of_len_lt`, `len_lt_of_inside`, `on_circle_of_len_eq`);
* System E's Circle 1 to 4 (`between_of_inside_chord`, `inside_of_between`,
  `outside_of_between`, `not_same_side_of_circles_meet`), which the library owes to Jeremy
  Avigad, Edward Dean and John Mumma, with our thanks;
* the finite avoidance rules for the open regions and the circumference: a point of the
  plane, of either side of a straight line, of the inside or the outside of a circle, or of
  its circumference, not among finitely many points given.

The defined words they reach, `OutsideCircle`, `OppositeSides` and `CirclesMeet`, are
translated in `Model/Hand.lean`. Two laws compare lengths, and there `<` is written
`@LT.lt S.Length _`, naming the carrier: the field `S.len` has the unfolded type
`(S.MagnitudeImpl .length).type`, on which Lean finds no order, while the library's
`‖A C‖ < ‖A B‖` is `LT.lt` at `Length`, through the instance that `S.Length` carries.
-/

@[expose] public section

namespace Model

namespace Hand

variable (S : Signature)

/-! ## Drawing a circle -/

/-- `Elements.Postulate3`, hand-translated. The lock prints it as `∀ (A B : Elements.Point),
Ne A B → Exists fun (α : Elements.Circle) => And (Elements.Centre A α) (Elements.OnCircle B
α)`. -/
def Postulate3 : Prop :=
  ∀ (A B : S.Point), A ≠ B → ∃ α : S.Circle, S.Centre A α ∧ S.OnCircle B α

/-- `Elements.Definition15`, hand-translated. The lock prints it as `∀ {A B C :
Elements.Point} {α : Elements.Circle}, Elements.Centre A α → Elements.OnCircle B α →
Elements.OnCircle C α → Eq (Elements.len A B) (Elements.len A C)`. -/
def Definition15 : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α → S.OnCircle C α →
    S.len A B = S.len A C

/-! ## A centre, and the inside of a circle -/

/-- `Elements.Tacit.centre_unique` (Generalities 2), hand-translated.
The theorem's unchanged type is
`∀ {A B : Elements.Point} {α : Elements.Circle}, Elements.Centre A α → Elements.Centre B α →
Eq A B`. -/
def centre_unique_circles : Prop :=
  ∀ {A B : S.Point} {α : S.Circle}, S.Centre A α → S.Centre B α → A = B

/-- `Elements.Tacit.centre_inside` (Generalities 3), hand-translated. The theorem's unchanged type is
`∀ {A : Elements.Point} {α : Elements.Circle}, Elements.Centre A α → Elements.InsideCircle A
α`. -/
def centre_inside_circles : Prop :=
  ∀ {A : S.Point} {α : S.Circle}, S.Centre A α → S.InsideCircle A α

/-- `Elements.Tacit.inside_not_on` (Generalities 4), hand-translated. The theorem's unchanged type is
`∀ {A : Elements.Point} {α : Elements.Circle}, Elements.InsideCircle A α → Not
(Elements.OnCircle A α)`. -/
def inside_not_on_circles : Prop :=
  ∀ {A : S.Point} {α : S.Circle}, S.InsideCircle A α → ¬S.OnCircle A α

/-- `Elements.Tacit.circle_eq`, hand-translated. The lock prints it as `∀ {A B C :
Elements.Point} {α β : Elements.Circle}, Elements.Centre A α → Elements.Centre A β →
Elements.OnCircle B α → Elements.OnCircle C β → Eq (Elements.len A B) (Elements.len A C) →
Eq α β`. -/
def circle_eq_circles : Prop :=
  ∀ {A B C : S.Point} {α β : S.Circle}, S.Centre A α → S.Centre A β → S.OnCircle B α →
    S.OnCircle C β → S.len A B = S.len A C → α = β

/-- `Elements.Tacit.inside_of_len_lt`, hand-translated. The theorem's unchanged type is `∀ {A B C :
Elements.Point} {α : Elements.Circle}, Elements.Centre A α → Elements.OnCircle B α → LT.lt
(Elements.len A C) (Elements.len A B) → Elements.InsideCircle C α`. -/
def inside_of_len_lt_circles : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α →
    @LT.lt S.Length _ (S.len A C) (S.len A B) → S.InsideCircle C α

/-- `Elements.Tacit.len_lt_of_inside`, hand-translated. The theorem's unchanged type is `∀ {A B C :
Elements.Point} {α : Elements.Circle}, Elements.Centre A α → Elements.OnCircle B α →
Elements.InsideCircle C α → LT.lt (Elements.len A C) (Elements.len A B)`. -/
def len_lt_of_inside_circles : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α → S.InsideCircle C α →
    @LT.lt S.Length _ (S.len A C) (S.len A B)

/-- `Elements.Tacit.on_circle_of_len_eq`, hand-translated. The theorem's unchanged type is `∀ {A B C :
Elements.Point} {α : Elements.Circle}, Elements.Centre A α → Elements.OnCircle B α → Eq
(Elements.len A C) (Elements.len A B) → Elements.OnCircle C α`. -/
def on_circle_of_len_eq_circles : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α →
    S.len A C = S.len A B → S.OnCircle C α

/-- `Elements.Tacit.radius_ne_zero`, hand-translated: a rule of our own, not System E's, that
a radius is not nothing. The lock prints it as `∀ {A B : Elements.Point} {α :
Elements.Circle}, Elements.Centre A α → Elements.OnCircle B α → Ne (Elements.len A B) 0`. -/
def radius_ne_zero : Prop :=
  ∀ {A B : S.Point} {α : S.Circle}, S.Centre A α → S.OnCircle B α →
    S.len A B ≠ (0 : S.Length)

/-! ## System E's Circle 1 to 4 -/

/-- `Elements.Tacit.between_of_inside_chord` (Circle 1), hand-translated.
The theorem's unchanged type is
`∀ {A B C : Elements.Point} {L : Elements.Line} {α : Elements.Circle}, Elements.OnLine A L
→ Elements.OnLine B L → Elements.OnLine C L → Elements.InsideCircle A α → Elements.OnCircle B
α → Elements.OnCircle C α → Ne B C → Elements.Between B A C`. -/
def between_of_inside_chord : Prop :=
  ∀ {A B C : S.Point} {L : S.Line} {α : S.Circle}, S.OnLine A L → S.OnLine B L →
    S.OnLine C L → S.InsideCircle A α → S.OnCircle B α → S.OnCircle C α → B ≠ C →
    S.Between B A C

/-- `Elements.Tacit.inside_of_between` (Circle 2), hand-translated.
The theorem's unchanged type is
`∀ {A B C : Elements.Point} {α : Elements.Circle}, Or (Elements.InsideCircle A α)
(Elements.OnCircle A α) → Or (Elements.InsideCircle B α) (Elements.OnCircle B α) →
Elements.Between A C B → Elements.InsideCircle C α`. -/
def inside_of_between : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.InsideCircle A α ∨ S.OnCircle A α →
    S.InsideCircle B α ∨ S.OnCircle B α → S.Between A C B → S.InsideCircle C α

/-- `Elements.Tacit.outside_of_between` (Circle 3), hand-translated.
The theorem's unchanged type is
`∀ {A B C : Elements.Point} {α : Elements.Circle}, Or (Elements.InsideCircle A α)
(Elements.OnCircle A α) → Not (Elements.InsideCircle C α) → Elements.Between A C B →
Elements.OutsideCircle B α`. -/
def outside_of_between : Prop :=
  ∀ {A B C : S.Point} {α : S.Circle}, S.InsideCircle A α ∨ S.OnCircle A α →
    ¬S.InsideCircle C α → S.Between A C B → S.OutsideCircle B α

/-- `Elements.Tacit.not_same_side_of_circles_meet` (Circle 4), hand-translated.
The theorem's unchanged type is
`∀ {A B C D : Elements.Point} {L : Elements.Line} {α β : Elements.Circle}, Ne α
β → Elements.OnCircle C α → Elements.OnCircle C β → Elements.OnCircle D α → Elements.OnCircle
D β → Ne C D → Elements.Centre A α → Elements.Centre B β → Elements.OnLine A L →
Elements.OnLine B L → Not (Elements.SameSide C D L)`. -/
def not_same_side_of_circles_meet : Prop :=
  ∀ {A B C D : S.Point} {L : S.Line} {α β : S.Circle}, α ≠ β → S.OnCircle C α →
    S.OnCircle C β → S.OnCircle D α → S.OnCircle D β → C ≠ D → S.Centre A α →
    S.Centre B β → S.OnLine A L → S.OnLine B L → ¬S.SameSide C D L

/-! ## Finite avoidance: open regions and the circumference -/

/-- `Elements.Tacit.exists_point`, hand-translated. The lock prints it as `∀ (avoid : List
Elements.Point), Exists fun (A : Elements.Point) => Not (Membership.mem avoid A)`. -/
def exists_point_circles : Prop :=
  ∀ (avoid : List S.Point), ∃ A : S.Point, ¬A ∈ avoid

/-- `Elements.Tacit.exists_point_same_side`, hand-translated. The theorem's unchanged type is `∀ {B :
Elements.Point} {L : Elements.Line}, Not (Elements.OnLine B L) → ∀ (avoid : List
Elements.Point), Exists fun (A : Elements.Point) => And (Elements.SameSide A B L) (Not
(Membership.mem avoid A))`. -/
def exists_point_same_side : Prop :=
  ∀ {B : S.Point} {L : S.Line}, ¬S.OnLine B L → ∀ (avoid : List S.Point),
    ∃ A : S.Point, S.SameSide A B L ∧ ¬A ∈ avoid

/-- `Elements.Tacit.exists_point_opposite_side`, hand-translated. The theorem's unchanged type is
`∀ {B : Elements.Point} {L : Elements.Line}, Not (Elements.OnLine B L) → ∀ (avoid : List
Elements.Point), Exists fun (A : Elements.Point) => And (Elements.OppositeSides A B L) (Not
(Membership.mem avoid A))`. -/
def exists_point_opposite_side : Prop :=
  ∀ {B : S.Point} {L : S.Line}, ¬S.OnLine B L → ∀ (avoid : List S.Point),
    ∃ A : S.Point, S.OppositeSides A B L ∧ ¬A ∈ avoid

/-- `Elements.Tacit.exists_point_inside_circle`, hand-translated. The lock prints it as
`∀ (α : Elements.Circle) (avoid : List Elements.Point), Exists fun (A : Elements.Point) =>
And (Elements.InsideCircle A α) (Not (Membership.mem avoid A))`. -/
def exists_point_inside_circle : Prop :=
  ∀ (α : S.Circle) (avoid : List S.Point), ∃ A : S.Point, S.InsideCircle A α ∧ ¬A ∈ avoid

/-- `Elements.Tacit.exists_point_outside_circle`, hand-translated.
The theorem's unchanged type is
`∀ (α : Elements.Circle) (avoid : List Elements.Point), Exists fun (A : Elements.Point) =>
And (Elements.OutsideCircle A α) (Not (Membership.mem avoid A))`. -/
def exists_point_outside_circle : Prop :=
  ∀ (α : S.Circle) (avoid : List S.Point), ∃ A : S.Point, S.OutsideCircle A α ∧ ¬A ∈ avoid

/-- `Elements.Tacit.exists_point_on_circle`, hand-translated. The theorem's unchanged type is
`∀ (α : Elements.Circle) (avoid : List Elements.Point), Exists fun (A : Elements.Point) =>
And (Elements.OnCircle A α) (Not (Membership.mem avoid A))`. -/
def exists_point_on_circle : Prop :=
  ∀ (α : S.Circle) (avoid : List S.Point), ∃ A : S.Point, S.OnCircle A α ∧ ¬A ∈ avoid

end Hand

end Model
