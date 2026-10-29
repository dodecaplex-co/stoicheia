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
  Every straight line has its foot (`Foot`, the last word here), so that a diameter is at
  no distance from the centre.
* A segment (Definition 6) is a circle `α`, a straight line `AB` in it, and the
  circumference on one side of `AB`; "the segment AEB" names that side by a point `E` of
  its circumference. The segment as a figure, with its points, is an `Arc` (below).
  III.25's construction core is given only A, C, a point P naming the side, the segment's
  points as a predicate S, the noncollinearity of A, C, P, and the fact that a ray from
  within AC towards P's side meets S. `Prop25.complete` proves that the circle constructed
  from those data is the circle from which the segment came. The companion
  `Prop25.of_circle` keeps the earlier, circle-backed statement, which is handed the whole
  circle.
* The angle in a segment (Definition 8) is the angle `AEB`, for a point `E` of its
  circumference; similar segments (Definition 11) are those whose angles `AEB`, `CFD` are
  equal.
* The angle of a segment (Definition 7) is "contained by a straight line and a
  circumference": a mixed angle, which our angles, each made by two straight lines, are
  not. It has words of its own, below, which the companions of III.16 and III.31 use and
  no proposition's own proof does.
* No proposition of Book III uses a sector (Definition 10).

The others are here: equal circles; a straight line touching a circle; circles touching
one another, inside or outside, read of the whole circles and, as Heath prefers, at the
point of contact; circles cutting one another; a circumference, compared
with a circumference; the angle at the centre standing on a circumference, of any size; and
the angles of III.16 and III.31, contained by a straight line and a circumference.

**Mixed angles.** III.16 compares the angle of the semicircle, and the remaining angle
between the circumference and the straight line that touches it, with any acute
rectilineal angle; III.31 compares the angles of the greater and the less segment with a
right angle. Here an angle is read as the region it opens near its vertex. A rectilineal
angle BAC has the region `WithinAngle B A C`, the points between its arms. A mixed angle
(`MixedAngle`) is recorded by its vertex, its straight arm, its circle and the side of the
circumference that bounds it; its region is the points on that side within the circle,
for the angle of a segment, or without it, between the circumference and a straight line
touching it, for the angle of contact. "Near the vertex" is said with circles about it,
as Euclid would draw them, and no numbers. A mixed angle exceeds a rectilineal angle
placed at its vertex when, near the vertex, the rectilineal region lies within the mixed
one and what is left over holds whole small circles (`MixedAngle.Exceeds`); it falls short
of it the other way about (`MixedAngle.FallsShort`). The words compare the angles as they
are placed. Euclid's comparison has the rectilineal angle along the mixed angle's
straight arm, on its side; the theorems that use the words place it so, and show that the
mixed angle is one Euclid draws (`MixedAngle.WellFormed`). No addition, multiple or ratio
of mixed angles is defined, and no motion of one.

**Circumferences.** Euclid compares circumferences only in one circle, or in equal
circles: "in equal circles equal angles stand on equal circumferences" (III.26). Lean
measures a circumference by the angle that stands on it at the circumference
(Definition 9), taken twice: the circumference `BKC` is `∠ B A C + ∠ B A C`, for a point
`A` of the circle on the other side of `BC` from `K`. That is the angle it subtends at the
centre when it is less than a semicircle (III.20); a semicircle is two right angles, and
the whole circle four. Our angles are less than two right angles, so the angle at the
centre standing on a circumference, `angleAtCentre`, is a word of its own, read as Euclid
draws it in III.20's first figure: it may be two right angles or more, a reading made after
Heath's notes and not Euclid's, and every circumference is its angle at the centre
(III.20's companion `Prop20.circumference`).

The measure carries no radius. In one circle, or in equal circles, two circumferences
are equal exactly when their measures are, and that is all Euclid ever asks of them; in
unequal circles equal measures do not make equal circumferences. So the propositions
that compare circumferences say "in equal circles", as he does, though not all of them
need it as stated. III.27 and III.29 take circumferences that coincide (`Arc.Congruent`,
below), and those lie in equal circles already, so their statements do not need the equal
circles, and their proofs keep them along Euclid's route. III.27's companion
`Prop27.of_measure`, for circumferences equal in measure, holds for any two circles: equal
measures give equal angles whatever the radii. III.26, III.28 and III.29's companion
`Prop29.of_measure` need them: III.26 and III.28 conclude that the circumferences are
congruent as well as equal in measure, which in unequal circles neither equal angles nor
equal straight lines give, and in III.28 and in `Prop29.of_measure` the measures are tied
to straight lines in the circles. III.24 proves Euclid's
equal segments: laid one on the other, they coincide (`Arc.Congruent`); its companion
`Prop24.equalCircles` proves the circles equal and the measures equal, by the radii.

`circumference` chooses one such angle (`Classical.epsilon`), as `rect` chooses one
area. That every point `A` gives the same angle is III.21, the angles in the same
segment being equal, and the facts about circumferences that Euclid takes for granted
are proved once from III.20–III.22 (`Elements/BookIII/Circumferences.lean`).

**Segments and arcs.** Euclid's segment (Definition 6) is "the figure contained by a
straight line and a circumference of a circle". Here a segment is named, as Heath names
it, by its circle, the two ends of its base and a point naming its side: `⟨AEB, A, B, E⟩`
is the segment AEB of the circle AEB on the straight line AB, on E's side (`Arc`). Its arc
is the circumference from A to B on that side, ends included (`OnArc`); the segment is the
part of the circle, inside or on it, that lies on that side of AB or on AB itself
(`InSegment`). Its kind, less than a semicircle, a semicircle or greater, is decided by
where the centre lies: beyond the base, on it, or on the arc's side, as III.25 decides it
(`Arc.Less`, `Arc.Semicircle`, `Arc.Greater`). Its measure is the circumference on it
(`Arc.measure`). Similar segments (Definitions 8 and 11) are read, as above, by equal
angles at points of their arcs.

Two segments are congruent, as Euclid's III.24 has one "coincide" with the other, when one
map of the plane's points carries the ends to the ends, the segment onto the segment and
the arc onto the arc, keeping every distance between points of the segment
(`Arc.Congruent`). No magnitude of a segment is defined, and no area of one: "equal"
segments, and "equal" circumferences in III.26 and III.28, are read through Common Notion
4 ("things which coincide with one another are equal to one another") as segments, or
circumferences, that coincide. `Elements/BookIII/Arcs.lean` says what the measure and the
congruence come to for drawn segments (`Arc.Drawn`): in equal circles, the
circumferences of drawn segments are equal in measure exactly when they are cut off by
equal straight lines and of one kind; and two drawn segments are congruent exactly when
their circles are equal and their circumferences equal in measure.

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

/-- **Definition III.3**, contact within: they meet at `C`, `β` has passed within `α`, for a
point of `β` is within `α`, and no point of `β` falls outside `α`. -/
def TouchesInternally (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ (∃ P : Point, OnCircle P β ∧ InsideCircle P α) ∧
    ∀ P : Point, OnCircle P β → ¬ OutsideCircle P α

/-- **Definition III.3**, contact without. The circles `α` and `β` touch one another
externally at `C`: they meet at `C`, and neither cuts the other, for no point is within
both. -/
def TouchesExternally (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ ∀ P : Point, InsideCircle P α → ¬ InsideCircle P β

/-- **Definition III.3.** The circles `α` and `β` touch one another at `C`, internally,
one within the other, or externally. -/
def CirclesTouch (α β : Circle) (C : Point) : Prop :=
  TouchesInternally α β C ∨ TouchesInternally β α C ∨ TouchesExternally α β C

/-- **Near C, every point has the property `p`.** Every point within some circle about C
has it. This says "near the point" with a circle about it, as Euclid would draw one (Post.
3), and with no numbers, as `LocallyWithin`, below, says "near the vertex". It is
`Surrounds p C`, its arguments in the other order. -/
def Touching.Near (C : Point) (p : Point → Prop) : Prop :=
  ∃ γ : Circle, Centre C γ ∧ ∀ P : Point, InsideCircle P γ → p P

/-- **Definition III.3**, contact within, read at the point, as Heath prefers. The circles
`α` and `β` touch one another internally at C, `β` within `α`: they meet at C, they are two
circles, and near C no point of `β` falls outside `α`. The whole-circle definition,
`TouchesInternally`, asks it of every point of `β`. -/
def TouchesInternallyAt (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ α ≠ β ∧
    Touching.Near C (fun P => OnCircle P β → ¬ OutsideCircle P α)

/-- **Definition III.3**, contact without, read at the point. The circles `α` and `β` touch
one another externally at C: they meet at C, and near C no point is within both. The
whole-circle definition, `TouchesExternally`, asks it of every point. -/
def TouchesExternallyAt (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧
    Touching.Near C (fun P => InsideCircle P α → ¬ InsideCircle P β)

/-- **Definition III.3**, read at the point. The circles `α` and `β` touch one another at C,
internally, one within the other, or externally. -/
def CirclesTouchAt (α β : Circle) (C : Point) : Prop :=
  TouchesInternallyAt α β C ∨ TouchesInternallyAt β α C ∨ TouchesExternallyAt α β C

/-! ### Definition III.7: the angle of a segment, and the angle of contact -/

/-- **Within the angle BAC.** The region of the rectilineal angle BAC: the points on C's
side of the straight line AB and on B's side of AC. For a true angle it is the open region
between the two arms, which are not in it; a straight angle has none. -/
def WithinAngle (B A C : Point) (P : Point) : Prop :=
  SameSideOf P C A B ∧ SameSideOf P B A C

/-- **A mixed angle** (Definition III.7), contained by a straight line and a circumference:
its vertex A, a point of the circle `α`, its straight arm, and the side of the
circumference that bounds it.

* `ofSegment A B α S`, **the angle of a segment**: the straight line AB and the
  circumference on S's side of it. Its region is within the circle. A comparison places a
  rectilineal angle along the ray from A through B, so B names the ray that runs into the
  circle: the other end of the straight line in the circle, or, for the angle of the
  semicircle in III.16, a point of the diameter beyond the centre.
* `ofContact A E α B`, **the angle of contact**: III.16's remaining angle, the horn-like
  angle, between a straight line AE touching the circle at A and the circumference on E's
  side of a straight line AB into the circle. Its region is without the circle.

The kinds may be formed from any points; `MixedAngle.WellFormed` says when they give the
angle Euclid draws. -/
inductive MixedAngle where
  | ofSegment (A B : Point) (α : Circle) (S : Point)
  | ofContact (A E : Point) (α : Circle) (B : Point)

namespace MixedAngle

/-- The vertex of a mixed angle: the point of the circle where its straight arm starts. -/
def vertex : MixedAngle → Point
  | ofSegment A _ _ _ => A
  | ofContact A _ _ _ => A

/-- **The region of a mixed angle.** For the angle of a segment, the points within the
circle on S's side of AB; for the angle of contact, the points without the circle and
within the angle EAB. Far from the vertex the regions run on, but only their parts near it
enter a comparison. -/
def region : MixedAngle → Point → Prop
  | ofSegment A B α S => fun P => SameSideOf P S A B ∧ InsideCircle P α
  | ofContact A E α B => fun P => WithinAngle E A B P ∧ OutsideCircle P α

/-- **A mixed angle as Euclid draws it.** For the angle of a segment: A is on the circle,
the ray from A through B passes within it, and S is off the straight line AB. For the angle
of contact: A is on the circle, the straight line AE touches it (Definition III.2), the ray
from A through B passes within it, and B is off AE. -/
def WellFormed : MixedAngle → Prop
  | ofSegment A B α S =>
      OnCircle A α ∧ (∃ P : Point, OnRay P A B ∧ InsideCircle P α) ∧ ¬ Collinear A B S
  | ofContact A E α B =>
      OnCircle A α ∧ Touches A E α ∧ (∃ P : Point, OnRay P A B ∧ InsideCircle P α) ∧
        ¬ Collinear A E B

end MixedAngle

/-- **Near A, the region `R` lies within the region `S`.** Some circle about A holds no
point of `R` that is not a point of `S`. -/
def LocallyWithin (A : Point) (R S : Point → Prop) : Prop :=
  ∃ γ : Circle, Centre A γ ∧ ∀ P : Point, InsideCircle P γ → R P → S P

/-- **The region `R` comes as near A as we please.** Every circle about A holds a point of
`R`. -/
def NearVertex (A : Point) (R : Point → Prop) : Prop :=
  ∀ γ : Circle, Centre A γ → ∃ P : Point, InsideCircle P γ ∧ R P

/-- **The region `R` holds a whole circle about P.** Some circle about P holds only points of
`R`: P is a point of `R`, and not on its edge. -/
def Surrounds (R : Point → Prop) (P : Point) : Prop :=
  ∃ δ : Circle, Centre P δ ∧ ∀ Q : Point, InsideCircle Q δ → R Q

/-- **The region `R` comes as near A as we please, and not by its edge alone.** Every circle
about A holds a point about which some circle holds only points of `R`. -/
def NearVertexOpen (A : Point) (R : Point → Prop) : Prop :=
  ∀ γ : Circle, Centre A γ → ∃ P : Point, InsideCircle P γ ∧ Surrounds R P

/-- **The angle with region `R` is less than the angle with region `S`, at A.** Near A, `R`
lies within `S`, and the points of `S` outside `R` hold whole small circles as near A as we
please; points alone would let an arm or a slit count as an excess. -/
def LocallyLess (A : Point) (R S : Point → Prop) : Prop :=
  LocallyWithin A R S ∧ NearVertexOpen A (fun P => S P ∧ ¬ R P)

/-- **The angles with regions `R` and `S` are equal, at A.** Near A, each lies within the
other. -/
def LocallyEqual (A : Point) (R S : Point → Prop) : Prop :=
  LocallyWithin A R S ∧ LocallyWithin A S R

namespace MixedAngle

/-- **The mixed angle `m` is greater than the rectilineal angle BXC**, X the vertex of `m`:
BXC is a true angle (B, X, C not on one straight line), and, placed at that vertex, it is
locally less than `m`. It compares their sizes as Euclid does when B is on the straight arm
of `m` and C on its region's side, as III.16 and III.31 place the rectilineal angle; the
word itself asks neither that, nor that `m` be well formed. -/
def Exceeds (m : MixedAngle) (B C : Point) : Prop :=
  ¬ Collinear B m.vertex C ∧ LocallyLess m.vertex (WithinAngle B m.vertex C) m.region

/-- **The mixed angle `m` is less than the rectilineal angle BXC**, X the vertex of `m`: BXC
is a true angle, `m` comes as near its vertex as we please, so that it is something, and
`m` is locally less than BXC placed at its vertex. As with `Exceeds`, it compares sizes
when the rectilineal angle is placed along the straight arm of `m`, on its side. -/
def FallsShort (m : MixedAngle) (B C : Point) : Prop :=
  ¬ Collinear B m.vertex C ∧ NearVertexOpen m.vertex m.region ∧
    LocallyLess m.vertex m.region (WithinAngle B m.vertex C)

end MixedAngle

/-- **Definition III.3**, circles that cut one another: they meet at two points, and each
passes within the other, for a point of `α` is within `β`, and a point of `β` within `α`. -/
def CirclesCut (α β : Circle) : Prop :=
  CirclesMeet α β ∧ (∃ P : Point, OnCircle P α ∧ InsideCircle P β) ∧
    ∃ P : Point, OnCircle P β ∧ InsideCircle P α

/-- **Definitions III.6 and III.9.** The circumference `BKC` of the circle `α`: the part
of `α` from `B` to `C` on the side of the straight line `BC` where `K` is. It is measured
by the angle that stands on it at the circumference, taken twice: `∠ B A C + ∠ B A C`,
for a point `A` of `α` on the other side of `BC`. Lean chooses one such angle; that every
such point gives the same is III.21 (`Circumference.eq`). The measure carries no radius,
so equal measures are equal circumferences only in one circle or in equal circles. -/
noncomputable def circumference (α : Circle) (B K C : Point) : Angle :=
  Classical.epsilon fun x =>
    ∃ A : Point, OnCircle A α ∧ OppositeSidesOf A K B C ∧ x = ∠ B A C + ∠ B A C

/-- **The angle at the centre standing on the circumference BKC.** Let E be the centre
of the circle α, and AEF a diameter whose ends lie on opposite sides of BC, F on the side
of K. The diameter divides the angle at the centre standing on the circumference BKC into
the angles BEF and FEC, as in Euclid's first figure for III.20, and the angle at the
centre is the two together. When E lies beyond BC, on K's side, it is what is left when
the angle BEC is taken from four right angles (`angleAtCentre.reflex`), and so greater
than two right angles (`angleAtCentre.reflex_gt`). Lean chooses one such diameter
(`Classical.epsilon`), as `circumference` chooses one angle; `angleAtCentre.diameter`
shows that every such diameter gives the same angle. -/
noncomputable def angleAtCentre (α : Circle) (B K C : Point) : Angle :=
  Classical.epsilon fun x => ∃ E A F : Point, Centre E α ∧ OnCircle A α ∧ OnCircle F α ∧
    Between A E F ∧ OppositeSidesOf A K B C ∧ SameSideOf F K B C ∧ x = ∠ B E F + ∠ F E C

/-- **Definition III.9.** The circumference on which the angle `BAC` stands: the part of
the circle `α` that the straight lines `AB`, `AC` cut off, from `B` to `C` on the side of
`BC` away from `A`. It is the circumference `BKC` for any `K` on that side
(`standing_eq_circumference`). -/
noncomputable def standing (α : Circle) (B A C : Point) : Angle :=
  Classical.epsilon fun x =>
    ∃ X : Point, OnCircle X α ∧ SameSideOf X A B C ∧ x = ∠ B X C + ∠ B X C

/-- **An arc of a circle** (Definition III.6): the circumference of the circle
`circle` from `B` to `C`, on the side of the straight line `BC` where `K` is. `K` only names
the side; it need not be on the circle. The segment on this arc is the figure contained by
the straight line `BC` and this circumference. -/
structure Arc where
  circle : Circle
  B : Point
  C : Point
  K : Point

/-- The arc is drawn: its two ends are on the circle, and the point naming its side is off
the straight line joining them (so the ends differ). -/
def Arc.Drawn (a : Arc) : Prop :=
  OnCircle a.B a.circle ∧ OnCircle a.C a.circle ∧ ¬ Collinear a.B a.C a.K

/-- `P` lies on `K`'s side of the straight line `BC`, or on that straight line: a closed
half-plane, for `B ≠ C`, as in a drawn arc. (When `B` and `C` are one point, every point
is on a straight line with them, and so every point counts.) -/
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

/-- The measure of the arc: the circumference `BKC` of its circle, twice the angle that
stands on it (Definition III.9). It carries no radius. -/
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

/-- **Definitions III.4 and III.5.** The foot of the perpendicular drawn from E to the
straight line AB. F is on the straight line AB; if E is not on it, every other point
P of the straight line makes the angle EFP right; and if E is on it, the foot is E
itself. If A and B are one point, every point is on a straight line with them, so the
foot is E. EF is then the distance of AB from E (Definitions III.4 and III.5,
extended: it is nothing when AB passes through E, a case Euclid's definitions do not
take). Every straight line has one foot (`Foot.exists`, `Foot.unique`, by I.12 and I.17). -/
def Foot (E A B F : Point) : Prop :=
  Collinear A B F ∧ (Collinear A B E → F = E) ∧
    (¬ Collinear A B E → ∀ P : Point, Collinear A B P → P ≠ F → ∠ E F P = ∟)

end Elements
