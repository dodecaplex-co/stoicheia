import Elements.Foundations.DefinitionsII

/-!
# The Definitions of Book III

> 1. Equal circles are those the diameters of which are equal, or the radii of which
>    are equal.
> 2. A straight line is said to touch a circle which, meeting the circle and being
>    produced, does not cut the circle.
> 3. Circles are said to touch one another which, meeting one another, do not cut one
>    another.
> 4. In a circle straight lines are said to be equally distant from the centre when the
>    perpendiculars drawn to them from the centre are equal.
> 5. And that straight line is said to be at a greater distance on which the greater
>    perpendicular falls.
> 6. A segment of a circle is the figure contained by a straight line and a circumference
>    of a circle.
> 7. An angle of a segment is that contained by a straight line and a circumference of a
>    circle.
> 8. An angle in a segment is the angle which, when a point is taken on the circumference
>    of the segment and straight lines are joined from it to the extremities of the
>    straight line which is the base of the segment, is contained by the straight lines
>    so joined.
> 9. And, when the straight lines containing the angle cut off a circumference, the angle
>    is said to stand upon that circumference.
> 10. A sector of a circle is the figure which, when an angle is constructed at the centre
>     of the circle, is contained by the straight lines containing the angle and the
>     circumference cut off by them.
> 11. Similar segments of circles are those which admit equal angles, or in which the
>     angles are equal to one another.

Book III is about circles, and most of its words need no Lean word of their own:

* Definitions 4 and 5 compare perpendiculars, `‖E F‖ = ‖E G‖` and `‖E H‖ < ‖E K‖`,
  for the feet `F`, `G`, `H`, `K` of perpendiculars from the centre `E` (III.14, III.15).
* A segment (Definition 6) is a circle `α`, a straight line `AB` in it, and the
  circumference on one side of `AB`; "the segment AEB" names that side by a point `E` of
  its circumference.
* The angle in a segment (Definition 8) is the angle `AEB`, for a point `E` of its
  circumference; similar segments (Definition 11) are those whose angles `AEB`, `CFD` are
  equal.
* The angle of a segment (Definition 7) is "contained by a straight line and a
  circumference": a mixed angle, which our angles, each made by two straight lines, are
  not. No proof uses it. III.16 and III.31 speak of such angles in their last clauses,
  and there Lean states the rectilineal facts that Euclid proves them by.
* No proposition of Book III uses a sector (Definition 10).

The others are here: equal circles; a straight line touching a circle; circles touching
one another, inside or outside; and a circumference, compared with a circumference.

**Circumferences.** Euclid compares circumferences only in one circle, or in equal
circles: "in equal circles equal angles stand on equal circumferences" (III.26). Lean
measures a circumference by the angle that stands on it at the circumference
(Definition 9), taken twice: the circumference `BKC` is `∠ B A C + ∠ B A C`, for a point
`A` of the circle on the other side of `BC` from `K`. That is the angle it subtends at the
centre when it is less than a semicircle (III.20); a semicircle is two right angles, and
the whole circle four. In one circle, or in equal circles, two circumferences are equal
exactly when these angles are, and that is all Euclid ever asks of them; the propositions
that compare circumferences say "in equal circles", as he does.

`circumference` chooses one such angle (`Classical.epsilon`), as `rect` chooses one
area. That every point `A` gives the same angle is III.21, the angles in the same
segment being equal, and the facts about circumferences that Euclid takes for granted
are proved once from III.20–III.22 (`Elements/BookIII/Circumferences.lean`).

None of these is an assumption; they are only definitions.
-/

namespace Elements

/-- **Definition III.1.** Equal circles: "those ... the radii of which are equal". Some
radius of `α`, from its centre `G` to a point `P` on it, is equal to some radius of `β`,
from its centre `H` to a point `Q` on it. -/
def EqualCircles (α β : Circle) : Prop :=
  ∃ G H P Q : Point, Centre G α ∧ Centre H β ∧ OnCircle P α ∧ OnCircle Q β ∧ ‖G P‖ = ‖H Q‖

/-- **Definition III.2.** The straight line `AB` touches the circle `α`: it meets the
circle and, produced either way, does not meet it at two points (`LineMeetsCircle`). -/
def Touches (A B : Point) (α : Circle) : Prop :=
  A ≠ B ∧ ∀ L : Line, OnLine A L → OnLine B L →
    (∃ P : Point, OnLine P L ∧ OnCircle P α) ∧ ¬ LineMeetsCircle L α

/-- **Definition III.3**, contact within. The circles `α` and `β` touch one another
internally at `C`, `β` within `α`: they meet at `C`, they are two circles, and `β` does
not cut `α`, for no point of `β` falls outside `α`. -/
def TouchesInternally (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ α ≠ β ∧ ∀ P : Point, OnCircle P β → ¬ OutsideCircle P α

/-- **Definition III.3**, contact without. The circles `α` and `β` touch one another
externally at `C`: they meet at `C`, and neither cuts the other, for no point is within
both. -/
def TouchesExternally (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ ∀ P : Point, InsideCircle P α → ¬ InsideCircle P β

/-- **Definition III.3.** The circles `α` and `β` touch one another at `C`, internally,
one within the other, or externally. -/
def CirclesTouch (α β : Circle) (C : Point) : Prop :=
  TouchesInternally α β C ∨ TouchesInternally β α C ∨ TouchesExternally α β C

/-- **Definitions III.6 and III.9.** The circumference `BKC` of the circle `α`: the part
of `α` from `B` to `C` on the side of the straight line `BC` where `K` is. It is measured
by the angle that stands on it at the circumference, taken twice: `∠ B A C + ∠ B A C`,
for a point `A` of `α` on the other side of `BC`. Lean chooses one such angle; that every
such point gives the same is III.21 (`Circumference.eq`). -/
noncomputable def circumference (α : Circle) (B K C : Point) : Angle :=
  Classical.epsilon fun x =>
    ∃ A : Point, OnCircle A α ∧ OppositeSidesOf A K B C ∧ x = ∠ B A C + ∠ B A C

/-- **Definition III.9.** The circumference on which the angle `BAC` stands: the part of
the circle `α` that the straight lines `AB`, `AC` cut off, from `B` to `C` on the side of
`BC` away from `A`. It is the circumference `BKC` for any `K` on that side
(`standing_eq_circumference`). -/
noncomputable def standing (α : Circle) (B A C : Point) : Angle :=
  Classical.epsilon fun x =>
    ∃ X : Point, OnCircle X α ∧ SameSideOf X A B C ∧ x = ∠ B X C + ∠ B X C

end Elements
