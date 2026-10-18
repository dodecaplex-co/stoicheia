import Elements.Foundations.DefinitionsIII

/-!
# Stage 3, staged: arcs and segments

Statements before proofs (brief 0006, stage 3; the spike of brief 0005, "Placement",
Step 0). These definitions are destined for `Elements/Foundations/DefinitionsIII.lean`,
the coordinator's file, and join `Certificate/axioms.lock` when a frozen statement uses
them. None of them is an assumption; they are only definitions.

Euclid's segment (Definition III.6) is "the figure contained by a straight line and a
circumference of a circle". Here a segment is named, as Heath names it, by its circle, the
two ends of its base and a point naming its side: `⟨AEB, A, B, E⟩` is the segment AEB of
the circle AEB on the straight line AB, on E's side. Its arc is the circumference from A
to B on that side, ends included; the segment is the part of the circle, inside or on
it, that lies on that side of AB or on AB itself.

Its kind (less than a semicircle, a semicircle, greater) is decided by where the centre
lies: beyond the base, on it, or on the arc's side, as III.25 decides it.

Two segments are congruent, as Euclid's III.24 has one "coincide" with the other, when one
map of the plane's points carries the ends to the ends, the segment onto the segment and
the arc onto the arc, keeping every distance.
-/

namespace Elements

/-- **An arc of a circle** (Definitions III.6 and III.9): the circumference of the circle
`circle` from `B` to `C`, on the side of the straight line `BC` where `K` is. `K` only names
the side; it need not be on the circle. The segment on this arc is the figure contained by
the straight line `BC` and this circumference. -/
structure Arc where
  circle : Circle
  B : Point
  C : Point
  K : Point

/-- The arc is drawn: its circle has a centre, its two ends are on the circle, and the
point naming its side is off the straight line joining them (so the ends differ). -/
def Arc.Drawn (a : Arc) : Prop :=
  (∃ O : Point, Centre O a.circle) ∧ OnCircle a.B a.circle ∧ OnCircle a.C a.circle ∧
    ¬ Collinear a.B a.C a.K

/-- `P` lies on `K`'s side of the straight line `BC`, or on that straight line: a closed
half-plane. -/
def OnSideOrLine (P K B C : Point) : Prop :=
  SameSideOf P K B C ∨ Collinear B C P

/-- `P` is a point of the arc: on its circle, and on its side of the base or on the base
(where the only points of the circle are the two ends). -/
def OnArc (P : Point) (a : Arc) : Prop :=
  OnCircle P a.circle ∧ OnSideOrLine P a.K a.B a.C

/-- `P` is a point of the segment: inside the circle or on it, and on the arc's side of the
base or on the base (where the only such points make up the base itself). -/
def InSegment (P : Point) (a : Arc) : Prop :=
  (InsideCircle P a.circle ∨ OnCircle P a.circle) ∧ OnSideOrLine P a.K a.B a.C

/-- The arc is less than a semicircle: the centre lies beyond the base, on the other side
of it from the arc. -/
def Arc.Less (a : Arc) : Prop :=
  ∃ O : Point, Centre O a.circle ∧ OppositeSidesOf O a.K a.B a.C

/-- The arc is a semicircle: the centre lies on the base. -/
def Arc.Semicircle (a : Arc) : Prop :=
  ∃ O : Point, Centre O a.circle ∧ Collinear a.B a.C O

/-- The arc is greater than a semicircle: the centre lies on the arc's side of the base. -/
def Arc.Greater (a : Arc) : Prop :=
  ∃ O : Point, Centre O a.circle ∧ SameSideOf O a.K a.B a.C

/-- The two arcs are of the same kind: both less than semicircles, both semicircles, or both
greater. -/
def Arc.SameKind (a b : Arc) : Prop :=
  (a.Less ∧ b.Less) ∨ (a.Semicircle ∧ b.Semicircle) ∨ (a.Greater ∧ b.Greater)

/-- The measure of the arc: the circumference `BKC` of its circle (twice the angle standing
on it). It carries no radius. -/
noncomputable def Arc.measure (a : Arc) : Angle :=
  circumference a.circle a.B a.K a.C

/-- The map `f` places the figure `S` on the figure `T`: it carries every point of `S` into
`T`, every point of `T` comes from some point of `S`, and it keeps the distance between any
two points of `S`. -/
def Places (f : Point → Point) (S T : Point → Prop) : Prop :=
  (∀ P, S P → T (f P)) ∧ (∀ Q, T Q → ∃ P, S P ∧ f P = Q) ∧
    ∀ P Q, S P → S Q → ‖(f P) (f Q)‖ = ‖P Q‖

/-- **Congruent segments** (Common Notion 4, "things which coincide with one another are
equal to one another", as III.24 uses it): one map carries the ends of the first base to
the ends of the second, in order, places the first segment on the second, and places the
first arc on the second. -/
def Arc.Congruent (a b : Arc) : Prop :=
  ∃ f : Point → Point, f a.B = b.B ∧ f a.C = b.C ∧
    Places f (InSegment · a) (InSegment · b) ∧ Places f (OnArc · a) (OnArc · b)

end Elements
