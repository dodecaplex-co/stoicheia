module

public import Model.Signature
public import Model.Hand

/-!
# The incidence and line laws, translated by hand

**Hand-translated: this file is written by hand,** like `Model/Hand.lean`, alongside the
generated laws described in the [README](../../README.md). Each law here is the library's,
word for word, with `S.Point` for `Elements.Point`, `S.OnLine` for `Elements.OnLine`, and
so on. Its printed statement is quoted above it, from the lock or, for a retired
rule such as `centre_unique` or `centre_inside`, its unchanged theorem type. Each binder keeps its original kind.
`Check/Incidence.lean` puts the library's own words in for `S` and asks the kernel whether
each result is the original declaration; the build fails if it is not. The same check
file compares each locked law's translation with its generated
law, and `centre_unique` directly with the library declaration, including binder kinds.
Its concrete plane proof remains as a derived fact, with no generated assumption field.
The same holds for `centre_inside` and `inside_not_on`, now proved using circle crossings
and the radius rule, without Circle 1, in `Elements/Figure/RuleBase.lean`, and for
`exists_point_between` and `exists_point_on_line_off_line`, proved using smaller circles
and uniqueness of a line, respectively, in `Elements/Figure/Incidence.lean`.

The laws are those of a straight line and the points on it:

* **Postulate 1,** a straight line through two points, and **`line_unique`**, only one;
* the other **generalities** of the diagram rules, about a circle's centre:
  `centre_unique`, `centre_inside` and `inside_not_on`;
* **`lines_meet_of_opposite_sides`** (Intersection 1), lines meeting;
* and the **finite avoidance rules for lines**: a point avoiding any finite list
  (`exists_point`), on a line (`exists_point_on_line`), on one line and off another
  (`exists_point_on_line_off_line`), between two points of a line (`exists_point_between`),
  and beyond one end of a segment (Postulate 2).

The hand translation of `LinesMeet` is retained as `Hand.LinesMeet` and checked against
the generated word; the laws use the generated signature words.
-/

@[expose] public section

namespace Model

namespace Hand

variable (S : Signature)

/-- `Elements.LinesMeet`, by hand: two different lines with a common point. The lock prints
it as `fun (L M : Elements.Line) => And (Ne L M) (Exists fun (A : Elements.Point) => And
(Elements.OnLine A L) (Elements.OnLine A M))`. -/
def LinesMeet (L M : S.Line) : Prop :=
  L ≠ M ∧ ∃ A : S.Point, S.OnLine A L ∧ S.OnLine A M

end Hand

namespace Hand

variable (S : Signature)

/-! ## A straight line through two points -/

/-- `Elements.Postulate1`, hand-translated. The lock prints it as `∀ (A B : Elements.Point),
Ne A B → Exists fun (L : Elements.Line) => And (Elements.OnLine A L) (Elements.OnLine B L)`. -/
def Postulate1 : Prop :=
  ∀ (A B : S.Point), A ≠ B → ∃ L : S.Line, S.OnLine A L ∧ S.OnLine B L

/-! ## Generalities -/

/-- `Elements.Tacit.line_unique`, hand-translated. The lock prints it as `∀ {A B :
Elements.Point} {L M : Elements.Line}, Ne A B → Elements.OnLine A L → Elements.OnLine B L →
Elements.OnLine A M → Elements.OnLine B M → Eq L M`. -/
def line_unique : Prop :=
  ∀ {A B : S.Point} {L M : S.Line}, A ≠ B → S.OnLine A L → S.OnLine B L → S.OnLine A M →
    S.OnLine B M → L = M

/-- `Elements.Tacit.centre_unique`, hand-translated.
The theorem's unchanged type is
`∀ {A B :
Elements.Point} {α : Elements.Circle}, Elements.Centre A α → Elements.Centre B α → Eq A B`. -/
def centre_unique : Prop :=
  ∀ {A B : S.Point} {α : S.Circle}, S.Centre A α → S.Centre B α → A = B

/-- `Elements.Tacit.centre_inside`, hand-translated. The theorem's unchanged type is `∀ {A :
Elements.Point} {α : Elements.Circle}, Elements.Centre A α → Elements.InsideCircle A α`. -/
def centre_inside : Prop :=
  ∀ {A : S.Point} {α : S.Circle}, S.Centre A α → S.InsideCircle A α

/-- `Elements.Tacit.inside_not_on`, hand-translated. The theorem's unchanged type is `∀ {A :
Elements.Point} {α : Elements.Circle}, Elements.InsideCircle A α → Not (Elements.OnCircle A
α)`. -/
def inside_not_on : Prop :=
  ∀ {A : S.Point} {α : S.Circle}, S.InsideCircle A α → ¬ S.OnCircle A α

/-! ## Lines meeting -/

/-- `Elements.Tacit.lines_meet_of_opposite_sides` (Intersection 1), hand-translated. The lock
prints it as `∀ {A B : Elements.Point} {L M : Elements.Line}, Elements.OppositeSides A B L →
Elements.OnLine A M → Elements.OnLine B M → Elements.LinesMeet L M`. -/
def lines_meet_of_opposite_sides : Prop :=
  ∀ {A B : S.Point} {L M : S.Line}, S.OppositeSides A B L → S.OnLine A M → S.OnLine B M →
    S.LinesMeet L M

/-! ## Points avoiding a finite list -/

/-- `Elements.Tacit.exists_point` (Points 1), hand-translated. The lock prints it as
`∀ (avoid : List Elements.Point), Exists fun (A : Elements.Point) => Not (Membership.mem avoid
A)`. -/
def exists_point : Prop :=
  ∀ (avoid : List S.Point), ∃ A : S.Point, ¬ A ∈ avoid

/-- `Elements.Tacit.exists_point_on_line` (Points 2), hand-translated. The lock prints it as
`∀ (L : Elements.Line) (avoid : List Elements.Point), Exists fun (A : Elements.Point) => And
(Elements.OnLine A L) (Not (Membership.mem avoid A))`. -/
def exists_point_on_line : Prop :=
  ∀ (L : S.Line) (avoid : List S.Point), ∃ A : S.Point, S.OnLine A L ∧ ¬ A ∈ avoid

/-- `Elements.Tacit.exists_point_on_line_off_line` (Points 2, off a second line),
hand-translated. The theorem's unchanged type is `∀ {L M : Elements.Line}, Ne L M → ∀ (avoid : List
Elements.Point), Exists fun (A : Elements.Point) => And (Elements.OnLine A L) (And (Not
(Elements.OnLine A M)) (Not (Membership.mem avoid A)))`. -/
def exists_point_on_line_off_line : Prop :=
  ∀ {L M : S.Line}, L ≠ M → ∀ (avoid : List S.Point),
    ∃ A : S.Point, S.OnLine A L ∧ ¬ S.OnLine A M ∧ ¬ A ∈ avoid

/-- `Elements.Tacit.exists_point_between` (Points 3), hand-translated. The theorem's unchanged type is
`∀ {B C : Elements.Point} {L : Elements.Line}, Elements.OnLine B L → Elements.OnLine C L →
Ne B C → ∀ (avoid : List Elements.Point), Exists fun (A : Elements.Point) => And
(Elements.OnLine A L) (And (Elements.Between B A C) (Not (Membership.mem avoid A)))`. -/
def exists_point_between : Prop :=
  ∀ {B C : S.Point} {L : S.Line}, S.OnLine B L → S.OnLine C L → B ≠ C →
    ∀ (avoid : List S.Point), ∃ A : S.Point, S.OnLine A L ∧ S.Between B A C ∧ ¬ A ∈ avoid

/-- `Elements.Postulate2` (with Points 4), hand-translated. The lock prints it as `∀ {B C :
Elements.Point} {L : Elements.Line}, Elements.OnLine B L → Elements.OnLine C L → Ne B C →
∀ (avoid : List Elements.Point), Exists fun (A : Elements.Point) => And (Elements.OnLine A L)
(And (Elements.Between B C A) (Not (Membership.mem avoid A)))`. -/
def Postulate2 : Prop :=
  ∀ {B C : S.Point} {L : S.Line}, S.OnLine B L → S.OnLine C L → B ≠ C →
    ∀ (avoid : List S.Point), ∃ A : S.Point, S.OnLine A L ∧ S.Between B C A ∧ ¬ A ∈ avoid

end Hand

end Model
