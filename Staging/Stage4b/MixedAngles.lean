import Elements.Figure.Basics
import Elements.Figure.Circles
import Elements.BookI.Prop08
import Elements.BookI.Prop11
import Elements.BookI.Prop12
import Elements.BookI.Prop13
import Elements.BookI.Prop17
import Elements.BookI.Prop19
import Elements.BookI.Prop20
import Elements.BookI.Prop23
import Elements.BookIII.Prop16
import Elements.BookIII.Prop31

/-!
# Staging: a prototype of mixed angles

Issue #56, for III.16 and III.31. Euclid's Definition III.7 speaks of "an angle of a
segment", contained by a straight line and a circumference, and III.16 and III.31 compare
such angles with rectilineal ones: the angle of the semicircle is greater, and the remaining
angle less, than any acute rectilineal angle (III.16); the angle of the greater segment is
greater, and that of the less segment less, than a right angle (III.31). Our angles are
magnitudes made by two straight lines, so today both propositions leave those clauses out
(the tag `mixed-angles-omitted`).

This file tries the representation of Astra's answer on issue #51: a mixed angle is a
geometric object, recorded by its vertex, its straight arm, its circle, and the branch and
side of the circumference that bound it, and two angles at one vertex are compared by
containment of their regions near that vertex. There is no new magnitude, and no axiom.

* **Regions.** A region is a predicate on points. The region of the rectilineal angle BAC
  is `WithinAngle B A C`: the points on C's side of AB and on B's side of AC. The region of
  a mixed angle is `MixedAngle.region`.
* **Near the vertex.** "Near A" is said with a circle about A, as Euclid would draw it, and
  with no numbers: `LocallyWithin A R S` says that some circle about A holds no point of `R`
  outside `S`; `NearVertexOpen A R` says that every circle about A, however small, holds a
  point about which some circle holds only points of `R` (`Surrounds`).
* **Less.** `LocallyLess A R S`: near A, `R` lies within `S`, and the part of `S` outside
  `R` holds whole small circles as near A as we please. A straight ray that enters a circle
  soon leaves it again, so containment of whole regions would be the wrong comparison: only
  the neighbourhood of the vertex counts. Asking for whole circles, not single points, keeps
  an arm or a slit from counting as an excess: a line holds no circle
  (`not_locallyLess_arm`, `not_locallyLess_slit`).
* **Through the object.** `MixedAngle.Exceeds` and `MixedAngle.FallsShort` compare a mixed
  angle with a true rectilineal angle placed at the mixed angle's own vertex, and each
  certifies that both angles are something: the rectilineal angle is not straight, and the
  mixed angle comes as near its vertex as we please.

Astra asked for checks on the interpretation before anything is called full, and they are
proved here in that order: (a) for rectilineal angles with a common arm the comparison is
the ordinary order of angles, and it is a strict order; (b) it does not depend on the points
that name the arms, and equal angles placed on one side of one arm give one region; in
III.16's figure, where AE is at right angles to the diameter AB, the angle of contact is the
same near its vertex whatever straight line from A into the circle names its branch (for a
touching straight line in general this is not proved here); (c) the horn-like angle of
III.16, the angle of the semicircle and the angle of the less segment of III.31 are not
empty: each holds whole small circles as near its vertex as we please, though no straight
ray from the vertex runs within the horn. Then (d) the comparisons of III.16 and III.31
themselves, for every acute or right rectilineal angle placed at the vertex, and Heath's
"remaining angle" as what is left of the right angle. `MixedAngle.WellFormed` says when the
named points give the angle Euclid draws, and the four angles compared are shown to have it.

Last, placement at another vertex. The angle of a segment exceeds a rectilineal angle CAR,
placed along its straight line AC on the segment's side, exactly when the angle CAR is less
than the angle CAT, where AT is drawn at right angles to the radius at A on that side
(`Segment.exceeds_iff`, `Segment.fallsShort_iff`). So take two equal circles, a straight line
in each, the two equal and neither through its centre, and a segment on each, the two of one
kind (both greater, or both less); place equal rectilineal angles along the two straight
lines, each on its segment's side: the angles of the segments compare alike with them
(`Segment.congruent`, by I.8). The segments must be of one kind: the greater segment's angle
exceeds a right angle and the less segment's falls short of it (III.31). In any two circles,
whatever their radii, the angles of the semicircles compare alike with equal rectilineal
angles placed along the diameters on their sides (`Prop16.semicircle_congruent`), and the
angles of contact with rectilineal angles placed along the touching straight lines on
corresponding sides (`Prop16.horn_congruent`). This is placement of the rectilineal angle; a
mixed angle itself is never moved.

These proofs test a representation before it is adopted, as WORKFLOW, section 2, asks of a
new foundation ("Prototype each new foundation"), and nothing in `Elements/` uses them. They
are in `Staging/` so that `lake build Staging` checks them. The coordinator approved the
prototype on 18 October 2026 and decided that they stay here until issue #57 decides their
move into `Elements/` (`docs/briefs/0002-decisions.md`). The account is
`docs/reports/mixed-angles-prototype.md`.
-/

namespace Elements.MixedAngles

open Tacit

/-! ## The definitions -/

/-- **Within the angle BAC.** The region of the rectilineal angle BAC: the points on C's side
of the straight line AB and on B's side of the straight line AC. For a true angle (B, A, C
not on one straight line) it is the open region between the two rays, which is less than two
right angles; its arms are not in it. For a straight angle it is empty, which is why
`MixedAngle.Exceeds` and `MixedAngle.FallsShort` ask for a true angle. -/
def WithinAngle (B A C : Point) (P : Point) : Prop :=
  SameSideOf P C A B ∧ SameSideOf P B A C

/-- **A mixed angle**, an angle "contained by a straight line and a circumference"
(Definition III.7, and III.16). It is recorded by its vertex A, its straight arm, its circle
`α`, which passes through A, and the branch and side of the circumference that bound it.
Euclid uses two kinds, one for each side of the circumference.

* `ofSegment A B α S`: **the angle of a segment** (Definition III.7), contained by the
  straight line AB and the circumference on S's side of AB. Its branch is the one on S's
  side, and its side is within the circle. Its region depends only on the straight line AB:
  any other point of that straight line names the same region
  (`MixedAngle.ofSegment_congr_collinear`). But a comparison places a rectilineal angle along
  the ray from A through B, so B must name the ray that runs into the circle: the other end
  of the straight line in the circle, or, for the angle of the semicircle in III.16, a point
  of the diameter beyond the centre (the diameter produced if need be).
* `ofContact A E α B`: **the angle of contact**, contained by a straight line AE that touches
  `α` at A and the circumference: III.16's "remaining angle", the horn-like angle of Proclus.
  Its straight arm is the ray from A through E; its branch is the one on E's side of a
  straight line AB that passes within the circle; its side is without the circle. In
  III.16's figure, where AE is at right angles to a diameter, which such straight line names
  the branch does not matter near A (`Prop16.horn_locallyEqual`); for a touching straight
  line in general that is not yet proved.

Nothing about the kinds is assumed when they are formed. `MixedAngle.WellFormed` says what
Euclid's figure asks, and the angles that III.16 and III.31 compare are shown to have it
(`Prop16.semicircle_wellFormed`, `Prop16.horn_wellFormed`, `Prop31.greater_wellFormed`,
`Prop31.less_wellFormed`). -/
inductive MixedAngle where
  | ofSegment (A B : Point) (α : Circle) (S : Point)
  | ofContact (A E : Point) (α : Circle) (B : Point)

namespace MixedAngle

/-- The vertex of a mixed angle: the point of the circle where its straight arm starts. -/
def vertex : MixedAngle → Point
  | ofSegment A _ _ _ => A
  | ofContact A _ _ _ => A

/-- **The region of a mixed angle.** For the angle of a segment, the points within the
circle on S's side of AB: near A they lie between the ray AB and the branch of the
circumference on that side. For the angle of contact, the points without the circle and
within the angle EAB: near A they lie between the ray AE and the branch of the circumference
on E's side. Far from A the regions run on (a segment is the whole of it), but only their
parts near the vertex enter a comparison. -/
def region : MixedAngle → Point → Prop
  | ofSegment A B α S => fun P => SameSideOf P S A B ∧ InsideCircle P α
  | ofContact A E α B => fun P => WithinAngle E A B P ∧ OutsideCircle P α

/-- **A mixed angle as Euclid draws it.** For the angle of a segment, A is on the circle,
the ray from A through B passes within it (so AB is not a touching straight line, and B
names the ray into the circle), and S is off the straight line AB. For the angle of contact,
A is on the circle, the straight line AE touches it (Definition III.2), the ray from A
through B passes within it, and B is off AE. The comparisons below do not ask for it, since
their theorems state the figure; a statement that quantifies over mixed angles should. -/
def WellFormed : MixedAngle → Prop
  | ofSegment A B α S =>
      OnCircle A α ∧ (∃ P : Point, OnRay P A B ∧ InsideCircle P α) ∧ ¬ Collinear A B S
  | ofContact A E α B =>
      OnCircle A α ∧ Touches A E α ∧ (∃ P : Point, OnRay P A B ∧ InsideCircle P α) ∧
        ¬ Collinear A E B

end MixedAngle

/-- **Near A, the region `R` lies within the region `S`.** Some circle about A holds no point
of `R` that is not a point of `S`. -/
def LocallyWithin (A : Point) (R S : Point → Prop) : Prop :=
  ∃ γ : Circle, Centre A γ ∧ ∀ P : Point, InsideCircle P γ → R P → S P

/-- **The region `R` comes as near A as we please.** Every circle about A holds a point of
`R`. -/
def NearVertex (A : Point) (R : Point → Prop) : Prop :=
  ∀ γ : Circle, Centre A γ → ∃ P : Point, InsideCircle P γ ∧ R P

/-- **The region `R` holds a whole circle about P.** Some circle about P holds only points of
`R`: P is a point of `R` and not on its edge. -/
def Surrounds (R : Point → Prop) (P : Point) : Prop :=
  ∃ δ : Circle, Centre P δ ∧ ∀ Q : Point, InsideCircle Q δ → R Q

/-- **The region `R` comes as near A as we please, and not by its edge alone.** Every circle
about A holds a point about which some circle holds only points of `R`. -/
def NearVertexOpen (A : Point) (R : Point → Prop) : Prop :=
  ∀ γ : Circle, Centre A γ → ∃ P : Point, InsideCircle P γ ∧ Surrounds R P

/-- **The angle with region `R` is less than the angle with region `S`, at A.** Near A, `R`
lies within `S`; and the points of `S` outside `R` hold whole small circles as near A as we
please. Points alone would not do: an arm or a slit, added to an angle, would then count as
an excess. -/
def LocallyLess (A : Point) (R S : Point → Prop) : Prop :=
  LocallyWithin A R S ∧ NearVertexOpen A (fun P => S P ∧ ¬ R P)

/-- **The angles with regions `R` and `S` are equal, at A.** Near A, each lies within the
other. -/
def LocallyEqual (A : Point) (R S : Point → Prop) : Prop :=
  LocallyWithin A R S ∧ LocallyWithin A S R

namespace MixedAngle

/-- **The mixed angle `m` is greater than the rectilineal angle BXC**, where X is the vertex
of `m`: BXC is a true angle (B, X, C not on one straight line), and, placed at that vertex,
it is locally less than `m`. The vertex is the mixed angle's own, so the comparison cannot be
made at another point. The first condition does work here: the region of a straight angle is
empty, so without it every mixed angle that is something would exceed a straight angle. That
`m` itself is something follows from the excess (`Exceeds.nearVertexOpen`). As III.16 and
III.31 compare, B is on the straight arm of `m` and C on its region's side; the definition
does not ask for that, and `FallsShort` is used the same way. -/
def Exceeds (m : MixedAngle) (B C : Point) : Prop :=
  ¬ Collinear B m.vertex C ∧ LocallyLess m.vertex (WithinAngle B m.vertex C) m.region

/-- **The mixed angle `m` is less than the rectilineal angle BXC**, where X is the vertex of
`m`: BXC is a true angle, `m` comes as near its vertex as we please, and `m` is locally less
than BXC placed at its vertex. Without the second condition an empty region would fall short
of every true angle. The first condition follows from the third, for the region of a
straight angle is empty and holds no circle of excess (`not_collinear_of_locallyLess`); it
is kept so that `Exceeds` and `FallsShort` both say that BXC is a true angle, and a proof
that has `FallsShort` has that fact to hand. -/
def FallsShort (m : MixedAngle) (B C : Point) : Prop :=
  ¬ Collinear B m.vertex C ∧ NearVertexOpen m.vertex m.region ∧
    LocallyLess m.vertex m.region (WithinAngle B m.vertex C)

end MixedAngle

/-! ## Small facts the checks need

These are Book Zero's kind of fact, proved from the foundations and Book Zero, with I.12,
I.17, I.19 and I.20 for the facts about circles about a point.

Two of them overlap statements that brief 0006 stages. `foot_nearest` takes the foot of the
perpendicular as I.12 gives it: a point N of BC such that every other point X of BC makes
the angle ANX right. For A off BC that is the staged `Foot A B C N`
(`Staging/Stage4/Foot.lean`). It is not stated through `Foot`, which is not yet approved and
whose existence and uniqueness are still stubs; on adoption it can take `Foot` as its
hypothesis and go with `Foot.exists` and `Foot.unique` to `Elements/BookIII/Squares.lean`.
`len_lt_of_add_lt` is I.20 with its degenerate case, which `Staging/Stage3/Degenerate.lean`
states as an equality, `Prop20.collinear_iff`, now proved there. It keeps its proof here from
`between_cases`, which needs nothing from the stage 3 files; on adoption it goes beside
`Prop20.collinear_iff` in `Elements/BookI/HelpersTriangles.lean`, which brief 0006 adds. -/

variable {A B C D E F P Q : Point} {α γ : Circle}

/-- A point off the straight line AB is on its own side of it. -/
theorem sameSideOf_self (h : Triangle A B C) : SameSideOf C C A B :=
  ⟨h.ne₁₂, fun _ hA hB => same_side_refl (h.off_line hA hB)⟩

/-- A point of the straight line AB (named as collinear with A and B) lies on every straight
line through A and B. -/
theorem onLine_of_collinear {L : Line} (hAB : A ≠ B) (h : Collinear A B C) (hA : OnLine A L)
    (hB : OnLine B L) : OnLine C L := by
  obtain ⟨M, hAM, hBM, hCM⟩ := h
  exact line_unique hAB hAM hBM hA hB ▸ hCM

/-- **The straight line AX named by another of its points.** If Y is on the straight line AX,
every point of the straight line AX is on the straight line AY. -/
theorem Collinear.change_point {X Y : Point} (hAX : A ≠ X) (hX : Collinear A X Y)
    (h : Collinear A X P) : Collinear A Y P := by
  obtain ⟨N, hA_N, hX_N, hP_N⟩ := h
  exact ⟨N, hA_N, onLine_of_collinear hAX hX hA_N hX_N, hP_N⟩

/-- The straight line AB′, for another point B′ of the straight line AB, is the straight line
AB: sides of the one are sides of the other. -/
theorem sameSideOf_congr_collinear {B' : Point} (hAB : A ≠ B) (hB'A : B' ≠ A)
    (hcol : Collinear A B B') : SameSideOf P Q A B' ↔ SameSideOf P Q A B := by
  obtain ⟨L, hA, hB_L⟩ := Postulate1 A B hAB
  have hB'L : OnLine B' L := onLine_of_collinear hAB hcol hA hB_L
  exact ⟨fun h => SameSideOf.of_line hAB hA hB_L (h.sameSide hA hB'L),
    fun h => SameSideOf.of_line hB'A.symm hA hB'L (h.sameSide hA hB_L)⟩

/-- The straight line AB′, for B′ on the ray from A through B, is the straight line AB. -/
theorem sameSideOf_congr_line {B' : Point} (hB : OnRay B' A B) :
    SameSideOf P Q A B' ↔ SameSideOf P Q A B :=
  sameSideOf_congr_collinear hB.1 hB.2.1 hB.2.2.1

/-- C's side of the straight line AB is the side of every point C′ on the ray from A through
C. -/
theorem sameSideOf_congr_point {C' : Point} (hC : OnRay C' A C) :
    SameSideOf P C' A B ↔ SameSideOf P C A B := by
  constructor
  · intro h
    have hC' : SameSideOf C' C' A B := sameSideOf_self h.symm.triangle
    exact h.trans (SameSideOf.of_onRay hC.symm hC').symm
  · intro h
    have hC'' : SameSideOf C C A B := sameSideOf_self h.symm.triangle
    exact h.trans (SameSideOf.of_onRay hC hC'').symm

/-- **Two points of one ray.** If P and Q are on the ray from A through B, P is on the ray
from A through Q. -/
theorem OnRay.of_sameRay (hP : OnRay P A B) (hQ : OnRay Q A B) : OnRay P A Q := by
  obtain ⟨L, hA, hB, hPL⟩ := hP.2.2.1
  have hQL : OnLine Q L := hQ.onLine hA hB
  exact ⟨hQ.2.1.symm, hP.2.1, ⟨L, hA, hQL, hPL⟩, fun h => hP.not_between hQ h⟩

/-- A point between a point Y of the straight line AB and a point W on Q's side of it is on
Q's side too (System E, Pasch 2). -/
theorem SameSideOf.of_between_line {Y W : Point} (hY : Collinear A B Y)
    (hW : SameSideOf W Q A B) (h : Between Y P W) : SameSideOf P Q A B := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B hW.1
  have hY_L : OnLine Y L := onLine_of_collinear hW.1 hY hA hB
  have hW_L : ¬ OnLine W L := not_on_line_of_same_side (hW.sameSide hA hB)
  have hP_L : ¬ OnLine P L := fun hP => hW_L (on_line_of_between h hY_L hP)
  exact (SameSideOf.of_line hW.1 hA hB (pasch2 h hY_L hP_L)).trans hW

/-- Every point is the centre of some circle [Post. 3]. -/
theorem exists_centre (A : Point) : ∃ γ : Circle, Centre A γ := by
  obtain ⟨B, hB⟩ := exists_point [A]
  have hAB : A ≠ B := fun h => hB (h ▸ List.mem_singleton_self A)
  obtain ⟨γ, hγ, -⟩ := Postulate3 A B hAB
  exact ⟨γ, hγ⟩

/-- Every ray from the centre of a circle has points within the circle: between the centre
and the point where the ray meets the circumference. -/
theorem exists_onRay_inside (hγ : Centre A γ) (hAC : A ≠ C) :
    ∃ Y : Point, OnRay Y A C ∧ InsideCircle Y γ := by
  obtain ⟨K, hK, -⟩ := exists_point_on_circle γ []
  have hAK : A ≠ K := (ne_of_centre_of_on hγ hK).symm
  obtain ⟨G, hG, hAG⟩ := OnRay.exists_len_eq hAK hAC
  have hGγ : OnCircle G γ := on_circle_of_len_eq hγ hK hAG
  obtain ⟨L, hA, hG_L⟩ := Postulate1 A G hG.2.1.symm
  obtain ⟨Y, -, hAYG, -⟩ := exists_point_between hA hG_L hG.2.1.symm []
  exact ⟨Y, OnRay.of_sameRay (OnRay.of_between hAYG) hG.symm,
    inside_of_between (Or.inl (centre_inside hγ)) (Or.inr hGγ) hAYG⟩

/-- Of two circles about one point, one lies within the other: some circle about A holds only
points within both. -/
theorem exists_inside_both {γ₁ γ₂ : Circle} (hγ₁ : Centre A γ₁) (hγ₂ : Centre A γ₂) :
    ∃ γ : Circle, Centre A γ ∧
      ∀ P : Point, InsideCircle P γ → InsideCircle P γ₁ ∧ InsideCircle P γ₂ := by
  obtain ⟨K₁, hK₁, -⟩ := exists_point_on_circle γ₁ []
  obtain ⟨K₂, hK₂, -⟩ := exists_point_on_circle γ₂ []
  rcases lt_trichotomy ‖A K₁‖ ‖A K₂‖ with h | h | h
  · exact ⟨γ₁, hγ₁, fun P hP =>
      ⟨hP, inside_of_len_lt hγ₂ hK₂ (lt_trans (len_lt_of_inside hγ₁ hK₁ hP) h)⟩⟩
  · have e : γ₁ = γ₂ := circle_eq hγ₁ hγ₂ hK₁ hK₂ h
    subst e
    exact ⟨γ₁, hγ₁, fun P hP => ⟨hP, hP⟩⟩
  · exact ⟨γ₂, hγ₂, fun P hP =>
      ⟨inside_of_len_lt hγ₁ hK₁ (lt_trans (len_lt_of_inside hγ₂ hK₂ hP) h), hP⟩⟩

/-- **The perpendicular is the least straight line to a straight line.** If N is the foot of
the perpendicular from A to the straight line BC, every other point X of BC is farther from
A: the angle at N is right, so the angle at X is less [I. 17], and the greater side is
opposite it [I. 19]. -/
theorem foot_nearest {N : Point} (hBC : B ≠ C) (hA : ¬ Collinear B C A)
    (hN : Collinear B C N) (hright : ∀ X : Point, Collinear B C X → X ≠ N → ∠ A N X = ∟) :
    ∀ X : Point, Collinear B C X → X = N ∨ ‖A N‖ < ‖A X‖ := by
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hBC
  have hA_L : ¬ OnLine A L := fun h => hA ⟨L, hB_L, hC_L, h⟩
  have hN_L : OnLine N L := onLine_of_collinear hBC hN hB_L hC_L
  intro X hX
  by_cases hXN : X = N
  · exact Or.inl hXN
  · right
    have hX_L : OnLine X L := onLine_of_collinear hBC hX hB_L hC_L
    have hANX : Triangle A N X := (Triangle.of_line hN_L hX_L (Ne.symm hXN) hA_L).cab
    have hANX' : ∠ A N X = ∟ := hright X hX hXN
    have h17 := (BookI.Prop17 hANX).1
    rw [hANX'] at h17
    have hNXA : ∠ N X A < ∠ A N X := by
      rw [hANX']; exact Magnitude.lt_of_add_lt_add_left h17
    exact BookI.Prop19 hANX hNXA

/-- **Two sides of a triangle are greater than the third**, said so that it holds when the
three points are not a triangle too: if OP and PQ together are less than a length `x`, so is
OQ. For a triangle this is I.20; for three points of one straight line, one lies between the
other two (System E, Between 6), and the whole is the sum of its parts or less than it. -/
theorem len_lt_of_add_lt {O : Point} {x : Length} (h : ‖O P‖ + ‖P Q‖ < x) : ‖O Q‖ < x := by
  by_cases hOP : O = P
  · subst hOP
    rw [len_self, add_comm, add_zero] at h
    exact h
  by_cases hPQ : P = Q
  · subst hPQ
    rw [len_self, add_zero] at h
    exact h
  by_cases hOQ : O = Q
  · subst hOQ
    rw [len_self]
    rcases lt_trichotomy 0 x with h0 | h0 | h0
    · exact h0
    · subst h0; exact absurd h (not_lt_zero _)
    · exact absurd h0 (not_lt_zero _)
  by_cases hcol : Collinear O P Q
  · obtain ⟨L, hO, hP, hQ⟩ := hcol
    rcases between_cases hOP hPQ hOQ hO hP hQ with hb | hb | hb
    · rw [len_add_of_between hb] at h; exact h
    · have h₁ : ‖O Q‖ < ‖P Q‖ := by
        rw [len_symm O Q, len_symm P Q]; exact len_lt_of_between (between_symm hb)
      have h₂ : ‖P Q‖ < ‖O P‖ + ‖P Q‖ := by
        rw [add_comm]; exact CommonNotion5 (len_pos hOP)
      exact lt_trans h₁ (lt_trans h₂ h)
    · exact lt_trans (len_lt_of_between hb) (lt_trans (CommonNotion5 (len_pos hPQ)) h)
  · have hOPQ : Triangle O P Q := hcol
    exact lt_trans (BookI.Prop20 hOPQ.bac).1 h

/-! ## Whole circles about a point

A point on one side of a straight line, within a circle or without it, has a whole circle
about it on the same side, within, or without. The radius is the distance to the foot of the
perpendicular [I. 12], or to the circumference along the straight line through the centre;
the other points are farther (`foot_nearest`, `len_lt_of_add_lt`). -/

/-- The common part of two regions holds a whole circle about P if each does. -/
theorem Surrounds.and {R S : Point → Prop} (hR : Surrounds R P) (hS : Surrounds S P) :
    Surrounds (fun Q => R Q ∧ S Q) P := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hR
  obtain ⟨δ₂, hδ₂, h₂⟩ := hS
  obtain ⟨δ, hδ, h⟩ := exists_inside_both hδ₁ hδ₂
  exact ⟨δ, hδ, fun Q hQ => ⟨h₁ Q (h Q hQ).1, h₂ Q (h Q hQ).2⟩⟩

/-- **A straight line holds no circle.** No circle about any point holds only points of the
straight line AC: the ray from its centre towards a point off AC has points within it
(`exists_off_line`, `exists_onRay_inside`). -/
theorem Surrounds.not_line (hAC : A ≠ C) : ¬ Surrounds (fun Q => Collinear A C Q) P := by
  rintro ⟨δ, hδ, h⟩
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  have hP_L : OnLine P L := onLine_of_collinear hAC (h P (centre_inside hδ)) hA_L hC_L
  obtain ⟨W, hW, -⟩ := exists_off_line hAC []
  have hW_L : ¬ OnLine W L := hW.off_line hA_L hC_L
  have hPW : P ≠ W := fun e => hW_L (e ▸ hP_L)
  obtain ⟨Y, hY, hYδ⟩ := exists_onRay_inside hδ hPW
  have hY_L : OnLine Y L := onLine_of_collinear hAC (h Y hYδ) hA_L hC_L
  obtain ⟨M, hP_M, hW_M, hY_M⟩ := hY.2.2.1
  have e : L = M := line_unique hY.2.1.symm hP_L hY_L hP_M hY_M
  exact hW_L (e ▸ hW_M)

/-- **A point on one side of a straight line has a whole circle about it on that side.** The
circle about P through N, the foot of the perpendicular from P to AB [I. 12]: a point within
it nearer P than N is, on AB or beyond it, would put a point of AB nearer P than N is
(System E, Intersection 1), against `foot_nearest`. -/
theorem surrounds_sameSideOf (h : SameSideOf P C A B) :
    Surrounds (fun Q => SameSideOf Q C A B) P := by
  have hAB : A ≠ B := h.1
  have hABP : Triangle A B P := h.triangle
  obtain ⟨N, hN, hright⟩ := BookI.Prop12 hAB hABP
  have hnear := foot_nearest hAB hABP hN hright
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hP_L : ¬ OnLine P L := hABP.off_line hA_L hB_L
  have hPN : P ≠ N := fun e => hP_L (e ▸ onLine_of_collinear hAB hN hA_L hB_L)
  obtain ⟨δ, hδ, hNδ⟩ := Postulate3 P N hPN
  refine ⟨δ, hδ, fun Q hQ => ?_⟩
  have hPQ : ‖P Q‖ < ‖P N‖ := len_lt_of_inside hδ hNδ hQ
  have hnot : ∀ X : Point, OnLine X L → ‖P X‖ < ‖P N‖ → False := fun X hX hlt => by
    rcases hnear X ⟨L, hA_L, hB_L, hX⟩ with e | h'
    · rw [e] at hlt; exact lt_irrefl _ hlt
    · exact lt_irrefl _ (lt_trans hlt h')
  have hQ_L : ¬ OnLine Q L := fun hQL => hnot Q hQL hPQ
  refine (SameSideOf.of_line hAB hA_L hB_L ?_ : SameSideOf Q P A B).trans h
  refine Classical.byContradiction fun hs => ?_
  obtain ⟨X, hX_L, hQXP⟩ := OppositeSides.exists_between ⟨hQ_L, hP_L, hs⟩
  exact hnot X hX_L (lt_trans (len_lt_of_between (between_symm hQXP)) hPQ)

/-- **A point within a circle has a whole circle about it within the circle.** If P is not
the centre O, the circle about P through K, where OP produced beyond P meets the
circumference (System E, Intersections 5): a point Q within it is nearer O than K is, since
OQ is less than OP, PQ together, and these less than OP, PK together, which make OK
(`len_lt_of_add_lt`). -/
theorem surrounds_inside {O : Point} (hO : Centre O α) (hP : InsideCircle P α) :
    Surrounds (fun Q => InsideCircle Q α) P := by
  by_cases hPO : P = O
  · subst hPO
    exact ⟨α, hO, fun Q hQ => hQ⟩
  obtain ⟨L, hP_L, hO_L⟩ := Postulate1 P O hPO
  obtain ⟨K, hK, -, hKPO⟩ := line_circle_beyond hP hP_L hO_L (Ne.symm hPO)
  have hPK : P ≠ K := fun e => inside_not_on (e ▸ hP) hK
  obtain ⟨δ, hδ, hKδ⟩ := Postulate3 P K hPK
  refine ⟨δ, hδ, fun Q hQ => inside_of_len_lt hO hK (len_lt_of_add_lt (P := P) ?_)⟩
  have hsum : ‖O P‖ + ‖P K‖ = ‖O K‖ := len_add_of_between (between_symm hKPO)
  rw [← hsum, add_comm ‖O P‖, add_comm ‖O P‖]
  exact add_lt_add_right _ (len_lt_of_inside hδ hKδ hQ)

/-- **A point without a circle has a whole circle about it without the circle.** The circle
about P through K, where the straight line from the centre O to P crosses the circumference
(System E, Intersections 4): were a point Q within it no farther from O than K is, OQ, QP
together would be less than OK, KP together, which make OP, against `len_lt_of_add_lt`. -/
theorem surrounds_outside {O : Point} (hO : Centre O α) (hP : OutsideCircle P α) :
    Surrounds (fun Q => OutsideCircle Q α) P := by
  have hPO : P ≠ O := fun e => hP.1 (e ▸ centre_inside hO)
  obtain ⟨L, hO_L, hP_L⟩ := Postulate1 O P (Ne.symm hPO)
  obtain ⟨K, hK, -, hOKP⟩ := line_circle_between (centre_inside hO) hO_L hP hP_L
  have hPK : P ≠ K := fun e => hP.2 (e ▸ hK)
  obtain ⟨δ, hδ, hKδ⟩ := Postulate3 P K hPK
  refine ⟨δ, hδ, fun Q hQ => outside_of_len_gt hO hK ?_⟩
  have hQP : ‖Q P‖ < ‖K P‖ := by
    rw [len_symm Q P, len_symm K P]; exact len_lt_of_inside hδ hKδ hQ
  have hsum : ‖O K‖ + ‖K P‖ = ‖O P‖ := len_add_of_between hOKP
  rcases lt_trichotomy ‖O K‖ ‖O Q‖ with h | h | h
  · exact h
  · exfalso
    have hlt : ‖O Q‖ + ‖Q P‖ < ‖O P‖ := by
      rw [← hsum, h, add_comm ‖O Q‖, add_comm ‖O Q‖]; exact add_lt_add_right _ hQP
    exact lt_irrefl _ (len_lt_of_add_lt hlt)
  · exfalso
    have h₂ : ‖O K‖ + ‖Q P‖ < ‖O K‖ + ‖K P‖ := by
      rw [add_comm ‖O K‖, add_comm ‖O K‖]; exact add_lt_add_right _ hQP
    have hlt : ‖O Q‖ + ‖Q P‖ < ‖O P‖ := by
      rw [← hsum]; exact lt_trans (add_lt_add_right _ h) h₂
    exact lt_irrefl _ (len_lt_of_add_lt hlt)

namespace NearVertexOpen

/-- Whole circles as near A as we please give points as near A as we please: the centres. -/
theorem nearVertex {T : Point → Prop} (h : NearVertexOpen A T) : NearVertex A T := by
  intro γ hγ
  obtain ⟨P, hPγ, δ, hδ, hT⟩ := h γ hγ
  exact ⟨P, hPγ, hT P (centre_inside hδ)⟩

/-- For a region that holds a whole circle about each of its points, points as near A as we
please give whole circles as near A as we please. -/
theorem of_nearVertex {T : Point → Prop} (hT : ∀ P, T P → Surrounds T P)
    (h : NearVertex A T) : NearVertexOpen A T := by
  intro γ hγ
  obtain ⟨P, hPγ, hP⟩ := h γ hγ
  exact ⟨P, hPγ, hT P hP⟩

/-- A larger region comes as near as the smaller. -/
theorem mono {T U : Point → Prop} (h : NearVertexOpen A T) (hTU : ∀ Q, T Q → U Q) :
    NearVertexOpen A U := by
  intro γ hγ
  obtain ⟨P, hPγ, δ, hδ, hT⟩ := h γ hγ
  exact ⟨P, hPγ, δ, hδ, fun Q hQ => hTU Q (hT Q hQ)⟩

/-- **Only the neighbourhood of A counts.** If, within some circle `γ₀` about A, the points
of `T` are points of `U`, then whole circles of `T` as near A as we please give whole circles
of `U`: each is shrunk to lie within `γ₀` (`surrounds_inside`). -/
theorem mono_near {T U : Point → Prop} {γ₀ : Circle} (h : NearVertexOpen A T)
    (hγ₀ : Centre A γ₀) (hTU : ∀ Q, InsideCircle Q γ₀ → T Q → U Q) : NearVertexOpen A U := by
  intro γ hγ
  obtain ⟨γ', hγ', hboth⟩ := exists_inside_both hγ hγ₀
  obtain ⟨P, hPγ', δ, hδ, hT⟩ := h γ' hγ'
  obtain ⟨δ₁, hδ₁, hin⟩ := surrounds_inside hγ₀ (hboth P hPγ').2
  obtain ⟨δ', hδ', hδδ⟩ := exists_inside_both hδ hδ₁
  exact ⟨P, (hboth P hPγ').1, δ', hδ', fun Q hQ =>
    hTU Q (hin Q (hδδ Q hQ).2) (hT Q (hδδ Q hQ).1)⟩

end NearVertexOpen

/-! ## Rectilineal angles as regions -/

namespace WithinAngle

/-- The region of the angle BAC is the region of the angle CAB. -/
theorem comm : WithinAngle B A C P ↔ WithinAngle C A B P :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **The naming points do not matter.** If B′ is on the ray from A through B, and C′ on the
ray from A through C, the angle B′AC′ has the region of the angle BAC. -/
theorem congr {B' C' : Point} (hB : OnRay B' A B) (hC : OnRay C' A C) :
    WithinAngle B' A C' P ↔ WithinAngle B A C P :=
  and_congr ((sameSideOf_congr_line hB).trans (sameSideOf_congr_point hC))
    ((sameSideOf_congr_line hC).trans (sameSideOf_congr_point hB))

/-- **Equal angles placed alike have one region.** If D and C are on the same side of the
straight line AB, and the angle BAD is equal to the angle BAC, the two angles have one
region: D is on the ray from A through C (`onRay_of_angle_eq`). -/
theorem eq_of_angle_eq (hDC : SameSideOf D C A B) (h : ∠ B A D = ∠ B A C) :
    WithinAngle B A D P ↔ WithinAngle B A C P :=
  congr (OnRay.self hDC.1) (onRay_of_angle_eq hDC h)

/-- **The part along AB.** A point within the angle BAD, where D is within the angle BAC, is
within the angle BAC (System E, Triple incidence 3). -/
theorem mono_left (hD : WithinAngle B A C D) (hP : WithinAngle B A D P) :
    WithinAngle B A C P := by
  have hAB : A ≠ B := hD.1.1
  have hAC : A ≠ C := hD.2.1
  have hAD : A ≠ D := hP.2.1
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  obtain ⟨M, hA_M, hD_M⟩ := Postulate1 A D hAD
  obtain ⟨N, hA_N, hB_N⟩ := Postulate1 A B hAB
  have hDB_L : SameSide D B L := hD.2.sameSide hA_L hC_L
  have hDP_L : SameSide D P L :=
    triple_incidence3 hA_L hA_M hA_N hC_L hD_M hB_N hDB_L
      (same_side_symm (hD.1.sameSide hA_N hB_N)) (same_side_symm (hP.2.sameSide hA_M hD_M))
      (same_side_symm (hP.1.sameSide hA_N hB_N))
  exact ⟨hP.1.trans hD.1, SameSideOf.of_line hAC hA_L hC_L (same_side_trans hDP_L hDB_L)⟩

/-- **The part along AC.** A point within the angle DAC, where D is within the angle BAC, is
within the angle BAC. -/
theorem mono_right (hD : WithinAngle B A C D) (hP : WithinAngle D A C P) :
    WithinAngle B A C P :=
  comm.2 (mono_left (comm.1 hD) (comm.1 hP))

/-- If D is within the angle BAC, the straight line AD separates B from C (System E, Triple
incidence 1). -/
theorem not_sameSideOf (hD : WithinAngle B A C D) : ¬ SameSideOf B C A D := by
  intro h
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hD.1.1
  obtain ⟨M, hA_M, hD_M⟩ := Postulate1 A D h.1
  obtain ⟨N, hA_N, hC_N⟩ := Postulate1 A C hD.2.1
  exact triple_incidence1 hA_L hA_M hA_N hB_L hD_M hC_N (hD.1.sameSide hA_L hB_L)
    (same_side_symm (hD.2.sameSide hA_N hC_N)) (h.sameSide hA_M hD_M)

/-- A point between a point of the ray AU and a point of the ray AV is within the angle UAV
(System E, Pasch 2). -/
theorem of_between {U V Y W : Point} (hUAV : Triangle U A V) (hY : OnRay Y A U)
    (hW : OnRay W A V) (h : Between Y P W) : WithinAngle U A V P :=
  ⟨SameSideOf.of_between_line hY.2.2.1
      (SameSideOf.of_onRay hW (sameSideOf_self hUAV.bac)) h,
    SameSideOf.of_between_line hW.2.2.1
      (SameSideOf.of_onRay hY (sameSideOf_self hUAV.bac.acb)) (between_symm h)⟩

/-- Every circle about the vertex of an angle holds a point within the angle: take a point of
each arm within the circle, and a point between them. -/
theorem exists_near {U V : Point} (hUAV : Triangle U A V) (hγ : Centre A γ) :
    ∃ P : Point, InsideCircle P γ ∧ WithinAngle U A V P := by
  obtain ⟨Y, hY, hYγ⟩ := exists_onRay_inside hγ hUAV.ne₁₂.symm
  obtain ⟨W, hW, hWγ⟩ := exists_onRay_inside hγ hUAV.ne₂₃
  have hYW : Y ≠ W := by
    rintro rfl
    obtain ⟨L, hA_L, hU_L⟩ := Postulate1 A U hUAV.ne₁₂.symm
    obtain ⟨M, hA_M, hV_M⟩ := Postulate1 A V hUAV.ne₂₃
    have e : L = M :=
      line_unique hY.2.1.symm hA_L (hY.onLine hA_L hU_L) hA_M (hW.onLine hA_M hV_M)
    exact hUAV.off_line hU_L hA_L (e ▸ hV_M)
  obtain ⟨L, hY_L, hW_L⟩ := Postulate1 Y W hYW
  obtain ⟨P, -, hYPW, -⟩ := exists_point_between hY_L hW_L hYW []
  exact ⟨P, inside_of_between (Or.inl hYγ) (Or.inl hWγ) hYPW, of_between hUAV hY hW hYPW⟩

/-- **The region of an angle has no edge points.** A point within the angle BAC has a whole
circle about it within the angle (`surrounds_sameSideOf`, twice). -/
theorem surrounds (h : WithinAngle B A C P) : Surrounds (WithinAngle B A C) P :=
  (surrounds_sameSideOf h.1).and (surrounds_sameSideOf h.2)

/-- Every circle about the vertex of an angle holds a whole circle within the angle. -/
theorem nearVertexOpen {U V : Point} (hUAV : Triangle U A V) :
    NearVertexOpen A (WithinAngle U A V) :=
  NearVertexOpen.of_nearVertex (fun _ hP => hP.surrounds) (fun _ hγ => exists_near hUAV hγ)

end WithinAngle

/-- On one side of the straight line AB, the less angle lies within the greater: if D and C
are on the same side of AB, and the angle BAD is less than the angle BAC, then D is on B's
side of AC. Were D on AC, the angles would be equal; were it on the other side, C would be
within the angle BAD (System E, Triple incidence 2), and the angle BAC a part of the angle
BAD [C.N. 5]. -/
theorem sameSideOf_of_angle_lt (hDC : SameSideOf D C A B) (h : ∠ B A D < ∠ B A C) :
    SameSideOf D B A C := by
  have hAB : A ≠ B := hDC.1
  have hABC : Triangle A B C := hDC.symm.triangle
  have hABD : Triangle A B D := hDC.triangle
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hABC.ne₁₃
  by_cases hD_M : OnLine D M
  · have hray : OnRay D A C := OnRay.of_sameSideOf hDC ⟨M, hA_M, hC_M, hD_M⟩ hABD.ne₁₃.symm
    rw [angle_onRay_right hray hAB.symm] at h
    exact absurd h (lt_irrefl _)
  by_cases hs : SameSide B D M
  · exact SameSideOf.of_line hABC.ne₁₃ hA_M hC_M (same_side_symm hs)
  · exfalso
    obtain ⟨N, hA_N, hD_N⟩ := Postulate1 A D hABD.ne₁₃
    have hBC_N : SameSide B C N :=
      triple_incidence2 hA_L hA_M hA_N hB_L hC_M hD_N (same_side_symm (hDC.sameSide hA_L hB_L))
        hs hD_M hAB.symm
    have hC_N : ¬ OnLine C N := not_on_line_of_same_side (same_side_symm hBC_N)
    have hadd : ∠ B A D = ∠ B A C + ∠ C A D :=
      angle_add_of_within hDC.symm
        (SameSideOf.of_line hABD.ne₁₃ hA_N hD_N (same_side_symm hBC_N))
    have hpos : 0 < ∠ C A D := (Triangle.of_line hA_N hD_N hABD.ne₁₃ hC_N).cab.angle_pos
    have hlt := CommonNotion5 (a := ∠ B A C) hpos
    rw [← hadd] at hlt
    exact lt_irrefl _ (lt_trans h hlt)

/-- **Within an angle on one side, by the size of the angles.** If R and T are on one side of
the straight line AC, R is on C's side of AT, that is, within the angle CAT, exactly when the
angle CAR is less than the angle CAT (`angle_add_of_within`, `sameSideOf_of_angle_lt`). -/
theorem WithinAngle.iff_angle_lt {R T : Point} (hRT : SameSideOf R T A C) :
    SameSideOf R C A T ↔ ∠ C A R < ∠ C A T := by
  constructor
  · intro hRC
    have hadd : ∠ C A T = ∠ C A R + ∠ R A T := angle_add_of_within hRT hRC
    have hlt := CommonNotion5 (a := ∠ C A R) hRC.triangle.cab.angle_pos
    rw [← hadd] at hlt
    exact hlt
  · exact sameSideOf_of_angle_lt hRT

/-- Across the straight line XY from a point W: a point Z off XY that is not on the side of
W's fellow V (on W's side) is on the other side from W. -/
theorem oppositeSidesOf_of_not_sameSideOf {X Y Z W V : Point} (hZ : Triangle X Y Z)
    (hWV : SameSideOf W V X Y) (hn : ¬ SameSideOf Z V X Y) : OppositeSidesOf Z W X Y := by
  obtain ⟨L, hX_L, hY_L⟩ := Postulate1 X Y hZ.ne₁₂
  exact OppositeSidesOf.of_line hZ.ne₁₂ hX_L hY_L ⟨hZ.off_line hX_L hY_L,
    not_on_line_of_same_side (hWV.sameSide hX_L hY_L),
    fun h => hn ((SameSideOf.of_line hZ.ne₁₂ hX_L hY_L h).trans hWV)⟩

/-- **The angle CAT holds every angle CAR beyond it.** Let R and T be on one side of the
straight line AC, and R not on C's side of AT: then R is on the ray AT, and the two angles
have one region; or R is across AT from C, the straight line RC crosses AT at a point X of
the ray AT within the angle CAR (System E, Intersection 1, Pasch 2), and the angle CAX lies
within the angle CAR (`WithinAngle.mono_left`). -/
theorem WithinAngle.of_not_sameSideOf {R T : Point} (hRT : SameSideOf R T A C)
    (hRC : ¬ SameSideOf R C A T) : ∀ P : Point, WithinAngle C A T P → WithinAngle C A R P := by
  have hACT : Triangle A C T := hRT.symm.triangle
  have hACR : Triangle A C R := hRT.triangle
  have hAT : A ≠ T := hACT.ne₁₃
  obtain ⟨L, hA_L, hT_L⟩ := Postulate1 A T hAT
  have hC_L : ¬ OnLine C L := hACT.acb.off_line hA_L hT_L
  have hRA : R ≠ A := hACR.ne₁₃.symm
  by_cases hR_L : OnLine R L
  · have hray : OnRay R A T := OnRay.of_sameSideOf hRT ⟨L, hA_L, hT_L, hR_L⟩ hRA
    intro P hP
    exact (WithinAngle.congr (OnRay.self hACT.ne₁₂) hray).2 hP
  · have hs : ¬ SameSide R C L := fun h => hRC (SameSideOf.of_line hAT hA_L hT_L h)
    obtain ⟨X, hX_L, hRXC⟩ := OppositeSides.exists_between ⟨hR_L, hC_L, hs⟩
    have hCAR : Triangle C A R := hACR.bac
    have hXw : WithinAngle C A R X :=
      WithinAngle.of_between hCAR (OnRay.self hCAR.ne₁₂.symm) (OnRay.self hCAR.ne₂₃)
        (between_symm hRXC)
    have hXA : X ≠ A := hXw.1.triangle.ne₁₃.symm
    have hXray : OnRay X A T :=
      OnRay.of_sameSideOf (hXw.1.trans hRT) ⟨L, hA_L, hT_L, hX_L⟩ hXA
    intro P hP
    exact WithinAngle.mono_left hXw ((WithinAngle.congr (OnRay.self hACT.ne₁₂) hXray).2 hP)

/-- If the angle with region `S` lies within the angle with region `R` near A, then `S`
cannot have points outside `R` as near A as we please. -/
theorem not_locallyWithin {R S : Point → Prop} (hW : LocallyWithin A S R)
    (hN : NearVertex A (fun P => S P ∧ ¬ R P)) : False := by
  obtain ⟨γ, hγ, h⟩ := hW
  obtain ⟨P, hP, hS, hR⟩ := hN γ hγ
  exact hR (h P hP hS)

/-- **The comparison depends only on the regions.** Regions with the same points compare
alike. -/
theorem locallyLess_congr {R R' S S' : Point → Prop} (hR : ∀ P, R P ↔ R' P)
    (hS : ∀ P, S P ↔ S' P) : LocallyLess A R S ↔ LocallyLess A R' S' := by
  have e₁ : R = R' := funext fun P => propext (hR P)
  have e₂ : S = S' := funext fun P => propext (hS P)
  subst e₁; subst e₂
  exact Iff.rfl

/-! ## Check (a): for rectilineal angles, the comparison is the order of angles -/

/-- **The less angle is locally less.** If D and C are on the same side of AB, and the angle
BAD is less than the angle BAC, then near A the region of BAD lies within that of BAC (indeed
everywhere), and every circle about A holds a whole circle within the angle DAC, which is
within BAC and has no point within BAD. -/
theorem WithinAngle.locallyLess_of_lt (hDC : SameSideOf D C A B) (h : ∠ B A D < ∠ B A C) :
    LocallyLess A (WithinAngle B A D) (WithinAngle B A C) := by
  have hD : WithinAngle B A C D := ⟨hDC, sameSideOf_of_angle_lt hDC h⟩
  obtain ⟨γ₀, hγ₀⟩ := exists_centre A
  refine ⟨⟨γ₀, hγ₀, fun P _ hP => WithinAngle.mono_left hD hP⟩, ?_⟩
  exact (WithinAngle.nearVertexOpen hD.2.triangle.cab).mono fun P hP =>
    ⟨WithinAngle.mono_right hD hP, fun h' => hD.not_sameSideOf (h'.2.symm.trans hP.1)⟩

/-- **Locally less is less.** For two rectilineal angles BAD, BAC with the common arm AB and
D, C on the same side of it, the angle BAD is locally less than the angle BAC exactly when it
is less as an angle. -/
theorem WithinAngle.locallyLess_iff (hDC : SameSideOf D C A B) :
    LocallyLess A (WithinAngle B A D) (WithinAngle B A C) ↔ ∠ B A D < ∠ B A C := by
  refine ⟨fun hL => ?_, WithinAngle.locallyLess_of_lt hDC⟩
  rcases lt_trichotomy (∠ B A D) (∠ B A C) with h | h | h
  · exact h
  · exfalso
    obtain ⟨γ, hγ⟩ := exists_centre A
    obtain ⟨P, -, hC, hD⟩ := hL.2.nearVertex γ hγ
    exact hD ((WithinAngle.eq_of_angle_eq hDC h).2 hC)
  · exact (not_locallyWithin hL.1 (WithinAngle.locallyLess_of_lt hDC.symm h).2.nearVertex).elim

/-- **Locally equal is equal.** For two rectilineal angles BAD, BAC with the common arm AB
and D, C on the same side of it, the angles are locally equal exactly when they are equal as
angles. -/
theorem WithinAngle.locallyEqual_iff (hDC : SameSideOf D C A B) :
    LocallyEqual A (WithinAngle B A D) (WithinAngle B A C) ↔ ∠ B A D = ∠ B A C := by
  constructor
  · intro hE
    rcases lt_trichotomy (∠ B A D) (∠ B A C) with h | h | h
    · exact (not_locallyWithin hE.2 (WithinAngle.locallyLess_of_lt hDC h).2.nearVertex).elim
    · exact h
    · exact (not_locallyWithin hE.1
        (WithinAngle.locallyLess_of_lt hDC.symm h).2.nearVertex).elim
  · intro h
    obtain ⟨γ, hγ⟩ := exists_centre A
    exact ⟨⟨γ, hγ, fun P _ hP => (WithinAngle.eq_of_angle_eq (P := P) hDC h).1 hP⟩,
      ⟨γ, hγ, fun P _ hP => (WithinAngle.eq_of_angle_eq (P := P) hDC h).2 hP⟩⟩

/-- **An arm adds nothing.** A true angle is not locally less than itself with one arm added:
the added points lie on a straight line, which holds no circle (`Surrounds.not_line`). -/
theorem not_locallyLess_arm (h : Triangle B A C) :
    ¬ LocallyLess A (WithinAngle B A C) (fun P => WithinAngle B A C P ∨ OnRay P A C) := by
  intro hL
  obtain ⟨γ, hγ⟩ := exists_centre A
  obtain ⟨P, -, δ, hδ, hT⟩ := hL.2 γ hγ
  exact Surrounds.not_line h.ne₂₃ (P := P)
    ⟨δ, hδ, fun Q hQ => ((hT Q hQ).1.resolve_left (hT Q hQ).2).2.2.1⟩

/-- **A slit takes nothing away.** An angle with the ray AD taken out, for D within it, is
not locally less than the angle: what is taken out lies on a straight line. -/
theorem not_locallyLess_slit (hD : WithinAngle B A C D) :
    ¬ LocallyLess A (fun P => WithinAngle B A C P ∧ ¬ OnRay P A D) (WithinAngle B A C) := by
  intro hL
  obtain ⟨γ, hγ⟩ := exists_centre A
  obtain ⟨P, -, δ, hδ, hT⟩ := hL.2 γ hγ
  have hray : ∀ Q, InsideCircle Q δ → OnRay Q A D := fun Q hQ =>
    Classical.byContradiction fun hn => (hT Q hQ).2 ⟨(hT Q hQ).1, hn⟩
  exact Surrounds.not_line hD.1.triangle.ne₁₃ (P := P) ⟨δ, hδ, fun Q hQ => (hray Q hQ).2.2.1⟩

/-! ## Check (a): the comparison is a strict order

The page reads "the angle of the semicircle lies strictly between every acute angle and the
right angle", which chains comparisons; these laws allow it. -/

/-- Near A, every region lies within itself. -/
theorem LocallyWithin.refl (A : Point) (R : Point → Prop) : LocallyWithin A R R := by
  obtain ⟨γ, hγ⟩ := exists_centre A
  exact ⟨γ, hγ, fun _ _ h => h⟩

/-- Lying within, near A, passes along. -/
theorem LocallyWithin.trans {R S T : Point → Prop} (h₁ : LocallyWithin A R S)
    (h₂ : LocallyWithin A S T) : LocallyWithin A R T := by
  obtain ⟨γ₁, hγ₁, f₁⟩ := h₁
  obtain ⟨γ₂, hγ₂, f₂⟩ := h₂
  obtain ⟨γ, hγ, h⟩ := exists_inside_both hγ₁ hγ₂
  exact ⟨γ, hγ, fun P hP hR => f₂ P (h P hP).2 (f₁ P (h P hP).1 hR)⟩

/-- Regions with the same points are locally equal. -/
theorem LocallyEqual.of_iff {R S : Point → Prop} (h : ∀ P, R P ↔ S P) : LocallyEqual A R S := by
  obtain ⟨γ, hγ⟩ := exists_centre A
  exact ⟨⟨γ, hγ, fun P _ hP => (h P).1 hP⟩, ⟨γ, hγ, fun P _ hP => (h P).2 hP⟩⟩

/-- Every angle is locally equal to itself. -/
theorem LocallyEqual.refl (A : Point) (R : Point → Prop) : LocallyEqual A R R :=
  ⟨LocallyWithin.refl A R, LocallyWithin.refl A R⟩

/-- Local equality is symmetric. -/
theorem LocallyEqual.symm {R S : Point → Prop} (h : LocallyEqual A R S) : LocallyEqual A S R :=
  ⟨h.2, h.1⟩

/-- Local equality passes along. -/
theorem LocallyEqual.trans {R S T : Point → Prop} (h₁ : LocallyEqual A R S)
    (h₂ : LocallyEqual A S T) : LocallyEqual A R T :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- No angle is locally less than itself. -/
theorem LocallyLess.irrefl {R : Point → Prop} : ¬ LocallyLess A R R := by
  intro h
  obtain ⟨γ, hγ⟩ := exists_centre A
  obtain ⟨P, -, hP, hn⟩ := h.2.nearVertex γ hγ
  exact hn hP

/-- Of two angles, not each is locally less than the other. -/
theorem LocallyLess.asymm {R S : Point → Prop} (h₁ : LocallyLess A R S)
    (h₂ : LocallyLess A S R) : False :=
  not_locallyWithin h₂.1 h₁.2.nearVertex

/-- **Less than a less is less.** Near A, `R` lies within `S` and `S` within `T`; the whole
circles of `T` outside `S`, shrunk to the circle where `R` lies within `S`, are outside `R`
(`NearVertexOpen.mono_near`). -/
theorem LocallyLess.trans {R S T : Point → Prop} (h₁ : LocallyLess A R S)
    (h₂ : LocallyLess A S T) : LocallyLess A R T := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  obtain ⟨γ₁, hγ₁, f₁⟩ := h₁.1
  exact h₂.2.mono_near hγ₁ fun Q hQ hT => ⟨hT.1, fun hR => hT.2 (f₁ Q hQ hR)⟩

/-- **Equal angles compare alike, on the left.** If `R` and `R'` are locally equal, and `R` is
locally less than `S`, so is `R'`. -/
theorem LocallyLess.congr_left {R R' S : Point → Prop} (hE : LocallyEqual A R R')
    (h : LocallyLess A R S) : LocallyLess A R' S := by
  refine ⟨hE.2.trans h.1, ?_⟩
  obtain ⟨γ₁, hγ₁, f₁⟩ := hE.2
  exact h.2.mono_near hγ₁ fun Q hQ hT => ⟨hT.1, fun hR' => hT.2 (f₁ Q hQ hR')⟩

/-- **Equal angles compare alike, on the right.** If `S` and `S'` are locally equal, and `R` is
locally less than `S`, it is locally less than `S'`. -/
theorem LocallyLess.congr_right {R S S' : Point → Prop} (hE : LocallyEqual A S S')
    (h : LocallyLess A R S) : LocallyLess A R S' := by
  refine ⟨h.1.trans hE.1, ?_⟩
  obtain ⟨γ₁, hγ₁, f₁⟩ := hE.1
  exact h.2.mono_near hγ₁ fun Q hQ hT => ⟨f₁ Q hQ hT.1, hT.2⟩

namespace MixedAngle

/-- **What exceeds a rectilineal angle is something.** If `m` exceeds an angle placed at its
vertex, `m` comes as near its vertex as we please: the excess is part of it. -/
theorem Exceeds.nearVertexOpen {m : MixedAngle} (h : m.Exceeds B C) :
    NearVertexOpen m.vertex m.region :=
  h.2.2.mono fun _ hP => hP.1

/-- **No mixed angle exceeds a straight angle.** If the vertex of `m` is between B and C, `m`
does not exceed the angle BXC: it is not a true angle. -/
theorem not_exceeds_straight {m : MixedAngle} (h : Between B m.vertex C) : ¬ m.Exceeds B C := by
  intro hm
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C (ne_of_between_ends h)
  exact hm.1 ⟨L, hB_L, on_line_of_between_ends h hB_L hC_L, hC_L⟩

/-- **No mixed angle falls short of a straight angle**, for the same reason. -/
theorem not_fallsShort_straight {m : MixedAngle} (h : Between B m.vertex C) :
    ¬ m.FallsShort B C := by
  intro hm
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C (ne_of_between_ends h)
  exact hm.1 ⟨L, hB_L, on_line_of_between_ends h hB_L hC_L, hC_L⟩

/-- **What a mixed angle is locally less than is a true angle.** If `m` is locally less than
the angle BXC placed at its vertex X, then B, X and C are not on one straight line: the
excess holds points within the angle BXC, and a straight angle has none. So the first
condition of `FallsShort` follows from its third. -/
theorem not_collinear_of_locallyLess {m : MixedAngle}
    (h : LocallyLess m.vertex m.region (WithinAngle B m.vertex C)) :
    ¬ Collinear B m.vertex C := by
  obtain ⟨γ, hγ⟩ := exists_centre m.vertex
  obtain ⟨P, -, hP, -⟩ := h.2.nearVertex γ hγ
  exact hP.1.symm.triangle.bac

end MixedAngle

/-! ## Check (b): the naming points do not matter -/

namespace MixedAngle

@[simp] theorem region_ofSegment {S : Point} :
    (ofSegment A B α S).region P ↔ SameSideOf P S A B ∧ InsideCircle P α := Iff.rfl

@[simp] theorem region_ofContact :
    (ofContact A E α B).region P ↔ WithinAngle E A B P ∧ OutsideCircle P α := Iff.rfl

/-- **The naming points of the angle of a segment do not matter.** Naming the straight arm
by another point B′ of the straight line AB, or the side by another point S′ on S's side,
gives the same region. (A comparison still reads the ray from A through the naming point, so
B′ on the ray AB names the same angle; see `MixedAngle`.) -/
theorem ofSegment_congr_collinear {B' S S' : Point} (hAB : A ≠ B) (hB'A : B' ≠ A)
    (hB : Collinear A B B') (hS : SameSideOf S' S A B) :
    (ofSegment A B' α S').region P ↔ (ofSegment A B α S).region P := by
  simp only [region_ofSegment]
  exact and_congr ((sameSideOf_congr_collinear hAB hB'A hB).trans
    ⟨fun h => h.trans hS, fun h => h.trans hS.symm⟩) Iff.rfl

/-- The same, for B′ on the ray AB. -/
theorem ofSegment_congr {B' S S' : Point} (hB : OnRay B' A B) (hS : SameSideOf S' S A B) :
    (ofSegment A B' α S').region P ↔ (ofSegment A B α S).region P :=
  ofSegment_congr_collinear hB.1 hB.2.1 hB.2.2.1 hS

/-- **The naming points of the angle of contact do not matter.** Naming the straight arm by
another point E′ of the ray AE, or the branch by another point B′ of the ray AB, gives the
same region. In III.16's figure, another straight line from A into the circle gives the same
angle near A (`Prop16.horn_locallyEqual`). -/
theorem ofContact_congr {E' B' : Point} (hE : OnRay E' A E) (hB : OnRay B' A B) :
    (ofContact A E' α B').region P ↔ (ofContact A E α B).region P := by
  simp only [region_ofContact]
  exact and_congr (WithinAngle.congr hE hB) Iff.rfl

end MixedAngle

/-- **Equal angles placed alike compare alike.** Compared with any region `S`, a rectilineal
angle placed along AB depends only on its size: if D and C are on the same side of AB and
the angles BAD, BAC are equal, BAD is locally less than `S` exactly when BAC is, and `S`
locally less than BAD exactly when it is less than BAC. -/
theorem WithinAngle.locallyLess_placement {S : Point → Prop} (hDC : SameSideOf D C A B)
    (h : ∠ B A D = ∠ B A C) :
    (LocallyLess A (WithinAngle B A D) S ↔ LocallyLess A (WithinAngle B A C) S) ∧
      (LocallyLess A S (WithinAngle B A D) ↔ LocallyLess A S (WithinAngle B A C)) :=
  ⟨locallyLess_congr (fun _ => WithinAngle.eq_of_angle_eq hDC h) (fun _ => Iff.rfl),
    locallyLess_congr (fun _ => Iff.rfl) (fun _ => WithinAngle.eq_of_angle_eq hDC h)⟩

/-! ## Near the vertex, a rectilineal angle in a circle is within it -/

/-- **An angle between two straight lines in a circle lies within it near its vertex.** If A,
B and C are on or within the circle `α`, and BAC is a true angle, some circle about A holds
no point of the angle BAC, nor of its arms, that is not within `α`.

The circle about A passes through N, the foot of the perpendicular from A to BC [I. 12];
every other point X of the straight line BC is farther from A (`foot_nearest`). A point P of
the angle within that circle lies on a ray from A that crosses BC at some X (the crossbar,
`crossbar`), nearer A than X, and so between A and a point within `α` (Circle 2, proved from Circle 3). -/
theorem near_inside_of_angle (hA : InsideCircle A α ∨ OnCircle A α)
    (hB : InsideCircle B α ∨ OnCircle B α) (hC : InsideCircle C α ∨ OnCircle C α)
    (hBAC : Triangle B A C) :
    LocallyWithin A (fun P => WithinAngle B A C P ∨ OnRay P A B ∨ OnRay P A C)
      (fun P => InsideCircle P α) := by
  have hBC : B ≠ C := hBAC.ne₁₃
  have hA_BC : ¬ Collinear B C A := fun ⟨L, hB_L, hC_L, hA_L⟩ => hBAC ⟨L, hB_L, hA_L, hC_L⟩
  obtain ⟨N, hN, hright⟩ := BookI.Prop12 hBC hA_BC
  obtain ⟨L, hB_L, hC_L⟩ := Postulate1 B C hBC
  have hA_L : ¬ OnLine A L := fun h => hA_BC ⟨L, hB_L, hC_L, h⟩
  have hN_L : OnLine N L := onLine_of_collinear hBC hN hB_L hC_L
  have hAN : A ≠ N := fun e => hA_L (e ▸ hN_L)
  have hfar := foot_nearest hBC hA_BC hN hright
  obtain ⟨γ, hγ, hNγ⟩ := Postulate3 A N hAN
  refine ⟨γ, hγ, fun P hPγ hP => ?_⟩
  have hAP : ‖A P‖ < ‖A N‖ := len_lt_of_inside hγ hNγ hPγ
  have hnear : ∀ X : Point, OnLine X L → OnRay P A X → Between A P X := by
    intro X hX hPX
    have hlt : ‖A P‖ < ‖A X‖ := by
      rcases hfar X ⟨L, hB_L, hC_L, hX⟩ with e | h
      · rw [e]; exact hAP
      · exact lt_trans hAP h
    exact OnRay.between_of_len_lt hPX (OnRay.self hPX.1) hlt
  rcases hP with hW | hPB | hPC
  · obtain ⟨X, hBXC, hXP⟩ := crossbar hW.1 hW.2
    have hXα : InsideCircle X α := inside_of_between hB hC hBXC
    exact inside_of_between hA (Or.inl hXα)
      (hnear X (on_line_of_between_ends hBXC hB_L hC_L) hXP.symm)
  · exact inside_of_between hA hB (hnear B hB_L hPB)
  · exact inside_of_between hA hC (hnear C hC_L hPC)

/-- **Points on either side of the circumference, near the vertex.** Let UAV be a true angle,
with the points of the ray AU near A within the circle `α`, and every point of the ray AV
without it. Then every circle about A holds a point within the angle UAV and within `α`, and
another within the angle and without `α`: on the straight line from a point Y of AU to a
point W of AV, both near A, on either side of the point where it crosses the circumference
(System E, Intersections 4 and Circle 3, which also proves Circle 2). -/
theorem exists_near_across {U V : Point} (hUAV : Triangle U A V)
    (hU : LocallyWithin A (fun P => OnRay P A U) (fun P => InsideCircle P α))
    (hV : ∀ P : Point, OnRay P A V → OutsideCircle P α) (hγ : Centre A γ) :
    (∃ P : Point, InsideCircle P γ ∧ WithinAngle U A V P ∧ InsideCircle P α) ∧
      (∃ P : Point, InsideCircle P γ ∧ WithinAngle U A V P ∧ OutsideCircle P α) := by
  obtain ⟨γ₀, hγ₀, hU'⟩ := hU
  obtain ⟨γ', hγ', hboth⟩ := exists_inside_both hγ hγ₀
  obtain ⟨Y, hY, hYγ'⟩ := exists_onRay_inside hγ' hUAV.ne₁₂.symm
  obtain ⟨W, hW, hWγ'⟩ := exists_onRay_inside hγ' hUAV.ne₂₃
  have hYα : InsideCircle Y α := hU' Y (hboth Y hYγ').2 hY
  have hWα : OutsideCircle W α := hV W hW
  have hYW : Y ≠ W := fun e => hWα.1 (e ▸ hYα)
  obtain ⟨L, hY_L, hW_L⟩ := Postulate1 Y W hYW
  obtain ⟨X, hXα, hX_L, hYXW⟩ := line_circle_between hYα hY_L hWα hW_L
  obtain ⟨P₁, -, hYP₁X, -⟩ := exists_point_between hY_L hX_L (ne_of_between hYXW) []
  have hYP₁W : Between Y P₁ W := between_of_between_left hYXW hYP₁X
  obtain ⟨P₂, -, hXP₂W, -⟩ :=
    exists_point_between hX_L hW_L (ne_of_between (between_symm hYXW)).symm []
  have hYP₂W : Between Y P₂ W :=
    between_symm (between_of_between_left (between_symm hYXW) (between_symm hXP₂W))
  have hinγ : ∀ P : Point, Between Y P W → InsideCircle P γ := fun P h =>
    (hboth P (inside_of_between (Or.inl hYγ') (Or.inl hWγ') h)).1
  exact ⟨⟨P₁, hinγ P₁ hYP₁W, WithinAngle.of_between hUAV hY hW hYP₁W,
      inside_of_between (Or.inl hYα) (Or.inr hXα) hYP₁X⟩,
    ⟨P₂, hinγ P₂ hYP₂W, WithinAngle.of_between hUAV hY hW hYP₂W,
      outside_of_between (Or.inl hYα) (fun h => inside_not_on h hXα) (between_cut hYXW hXP₂W)⟩⟩

/-- **Whole circles on either side of the circumference, near the vertex.** In the figure of
`exists_near_across`, for a circle `α` about O, every circle about A holds a whole circle
within the angle UAV and within `α`, and another within the angle and without `α`
(`WithinAngle.surrounds`, `surrounds_inside`, `surrounds_outside`). -/
theorem near_across {O U V : Point} (hO : Centre O α) (hUAV : Triangle U A V)
    (hU : LocallyWithin A (fun P => OnRay P A U) (fun P => InsideCircle P α))
    (hV : ∀ P : Point, OnRay P A V → OutsideCircle P α) :
    NearVertexOpen A (fun P => WithinAngle U A V P ∧ InsideCircle P α) ∧
      NearVertexOpen A (fun P => WithinAngle U A V P ∧ OutsideCircle P α) :=
  ⟨NearVertexOpen.of_nearVertex (fun _ hP => hP.1.surrounds.and (surrounds_inside hO hP.2))
      (fun _ hγ => (exists_near_across hUAV hU hV hγ).1),
    NearVertexOpen.of_nearVertex (fun _ hP => hP.1.surrounds.and (surrounds_outside hO hP.2))
      (fun _ hγ => (exists_near_across hUAV hU hV hγ).2)⟩

/-- The points of a ray from a point A of a circle towards a point B on or within it, near A,
are within the circle: some circle about A holds no point of the ray that is not between A
and B. -/
theorem near_inside_of_ray (hA : OnCircle A α) (hB : InsideCircle B α ∨ OnCircle B α)
    (hAB : A ≠ B) : LocallyWithin A (fun P => OnRay P A B) (fun P => InsideCircle P α) := by
  obtain ⟨γ₀, hγ₀, hBγ₀⟩ := Postulate3 A B hAB
  exact ⟨γ₀, hγ₀, fun P hP hPB => inside_of_between (Or.inr hA) hB
    (OnRay.between_of_len_lt hPB (OnRay.self hAB) (len_lt_of_inside hγ₀ hBγ₀ hP))⟩

/-- The ray AC, near A, is within the circle if some point K of it is on or within the
circle: the ray AC is the ray AK. -/
theorem near_inside_of_onRay {K : Point} (hA : OnCircle A α) (hK : OnRay K A C)
    (hKα : InsideCircle K α ∨ OnCircle K α) :
    LocallyWithin A (fun P => OnRay P A C) (fun P => InsideCircle P α) := by
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside_of_ray hA hKα hK.2.1.symm
  exact ⟨γ₀, hγ₀, fun P hP hPC => hnear P hP (OnRay.of_sameRay hPC hK)⟩

/-! ## III.16's two parts, and the circle on one side of a touching straight line -/

namespace Prop16

/-- **III.16's first part**, for the circle `α` at A: every point of the straight line AE but
A is without the circle. -/
def Outside (A E : Point) (α : Circle) : Prop :=
  ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P α

/-- **III.16's second part**, for the circle `α` at A: every other straight line AF through A
falls within the circle, at some point G. -/
def FallsWithin (A E : Point) (α : Circle) : Prop :=
  ∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G α

/-- The straight line AE of III.16's first part has two ends: were E the point A, every
straight line through A would be AE, and a point K within the circle would be without it. -/
theorem Outside.ne {K : Point} (hA : OnCircle A α) (hK : InsideCircle K α)
    (hAE_out : Outside A E α) : A ≠ E := by
  intro e
  subst e
  have hAK : A ≠ K := fun e => inside_not_on (e ▸ hK) hA
  obtain ⟨L, hA_L, hK_L⟩ := Postulate1 A K hAK
  exact (hAE_out K ⟨L, hA_L, hA_L, hK_L⟩ hAK.symm).1 hK

/-- The points of the ray AE are without the circle: III.16's first part. -/
theorem outside_of_onRay (hAE_out : Outside A E α) :
    ∀ P : Point, OnRay P A E → OutsideCircle P α :=
  fun P hP => hAE_out P hP.2.2.1 hP.2.1

/-- **The circle lies on one side of the straight line AE.** Under III.16's first part, every
point within the circle, or on it other than A, is on the side of AE of any point K within
the circle: a point on AE, or across it, would put a point of AE within the circle, on the
way to K (System E, Intersection 1 and Circle 3, through Circle 2). -/
theorem sameSideOf_of_inside {K : Point} (hA : OnCircle A α) (hAE_out : Outside A E α)
    (hK : InsideCircle K α) (hQ : InsideCircle Q α ∨ OnCircle Q α) (hQA : Q ≠ A) :
    SameSideOf Q K A E := by
  have hAE : A ≠ E := hAE_out.ne hA hK
  obtain ⟨L, hA_L, hE_L⟩ := Postulate1 A E hAE
  have hoff : ∀ X : Point, InsideCircle X α → ¬ OnLine X L := fun X hX hX_L =>
    (hAE_out X ⟨L, hA_L, hE_L, hX_L⟩ (fun e => inside_not_on (e ▸ hX) hA)).1 hX
  have hQ_L : ¬ OnLine Q L := by
    intro hQ_L
    have hout := hAE_out Q ⟨L, hA_L, hE_L, hQ_L⟩ hQA
    rcases hQ with h | h
    · exact hout.1 h
    · exact hout.2 h
  refine SameSideOf.of_line hAE hA_L hE_L ?_
  refine Classical.byContradiction fun hs => ?_
  obtain ⟨X, hX_L, hQXK⟩ := OppositeSides.exists_between ⟨hQ_L, hoff K hK, hs⟩
  exact hoff X (inside_of_between hQ (Or.inl hK) hQXK) hX_L

end Prop16

/-! ## Placement at another vertex: the angle of a segment, by the tangent

Let AT be drawn from A at right angles to the radius, on the side of the segment; III.16 says
it falls without the circle and that every other straight line through A falls within it.
The angle of the segment then exceeds exactly the rectilineal angles CAR (placed along AC, on
its side) within the angle CAT, and falls short of exactly the others. So a congruent
placement, which keeps the angle CAT, keeps every comparison. -/

namespace Segment

/-- **The angle of a segment exceeds exactly the angles within the angle CAT.** Let A be on
the circle `α` about O, the ray AC run into the circle (some point K of it on or within the
circle), AT satisfy III.16's two parts, and T and R be on S's side of AC. Then the angle of
the segment exceeds the angle CAR exactly when R is within the angle CAT, on C's side of AT.

If it is, the straight line AR falls within the circle at a point G of the ray AR, on the
circle's side of AT; near A the angle CAR, which is the angle KAG, lies within the circle
(`near_inside_of_angle`), and every circle about A holds whole circles within the angle RAT
and within the circle, which are in the segment's angle and not in CAR (`near_across`). If it
is not, the angle CAT lies within the angle CAR (`WithinAngle.of_not_sameSideOf`), and every
circle about A holds points within the angle CAT and without the circle, which the angle of
the segment would have to hold. -/
theorem exceeds_iff {C K O R S T : Point} (hO : Centre O α) (hA : OnCircle A α)
    (hK : OnRay K A C) (hKα : InsideCircle K α ∨ OnCircle K α)
    (hAT_out : Prop16.Outside A T α) (hAT_in : Prop16.FallsWithin A T α)
    (hTS : SameSideOf T S A C) (hRS : SameSideOf R S A C) :
    (MixedAngle.ofSegment A C α S).Exceeds C R ↔ SameSideOf R C A T := by
  have hAK : A ≠ K := hK.2.1.symm
  have hRT : SameSideOf R T A C := hRS.trans hTS.symm
  have hCAT : Triangle C A T := hTS.triangle.bac
  have hacross := near_across hO hCAT (near_inside_of_onRay hA hK hKα)
    (Prop16.outside_of_onRay hAT_out)
  constructor
  · intro hEx
    refine Classical.byContradiction fun hRC => ?_
    obtain ⟨γ, hγ, hW⟩ := hEx.2.1
    obtain ⟨P, hPγ, hPw, hPout⟩ := hacross.2.nearVertex γ hγ
    exact hPout.1
      (MixedAngle.region_ofSegment.1 (hW P hPγ (WithinAngle.of_not_sameSideOf hRT hRC P hPw))).2
  · intro hRC
    have hRw : WithinAngle C A T R := ⟨hRT, hRC⟩
    have hKO : SameSideOf K O A T :=
      Prop16.sameSideOf_of_inside hA hAT_out (centre_inside hO) hKα hAK.symm
    have hCO : SameSideOf C O A T := SameSideOf.of_onRay hK.symm hKO
    obtain ⟨G, hG, hGα⟩ := hAT_in R hRC.triangle
    have hGA : G ≠ A := fun e => inside_not_on (e ▸ hGα) hA
    have hGO : SameSideOf G O A T :=
      Prop16.sameSideOf_of_inside hA hAT_out (centre_inside hO) (Or.inl hGα) hGA
    have hGray : OnRay G A R :=
      OnRay.of_sameSideOf ((hGO.trans hCO.symm).trans hRC.symm) hG hGA
    have hGR : SameSideOf G R A C := SameSideOf.of_onRay hGray (sameSideOf_self hRS.triangle)
    have hGAK : Triangle G A K := ((sameSideOf_congr_line hK).2 hGR).triangle.cab
    obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside_of_angle (Or.inr hA) (Or.inl hGα) hKα hGAK
    refine ⟨hRS.triangle.bac, ⟨γ₀, hγ₀, fun P hPγ hP => ?_⟩, ?_⟩
    · exact MixedAngle.region_ofSegment.2 ⟨hP.1.trans hRS,
        hnear P hPγ (Or.inl (WithinAngle.comm.1 ((WithinAngle.congr hK hGray).2 hP)))⟩
    · refine (near_across hO hRC.triangle.cab (near_inside_of_onRay hA hGray (Or.inl hGα))
        (Prop16.outside_of_onRay hAT_out)).1.mono fun P hP => ?_
      obtain ⟨hPw, hPα⟩ := hP
      refine ⟨MixedAngle.region_ofSegment.2
        ⟨(WithinAngle.mono_right hRw hPw).1.trans hTS, hPα⟩, fun h' => ?_⟩
      exact hRw.not_sameSideOf (h'.2.symm.trans hPw.1)

/-- **The angle of a segment is not nothing.** In the figure of `exceeds_iff`, every circle
about A holds a whole circle within the angle CAT and within the circle, which is in the
segment's angle (`near_across`). -/
theorem nearVertexOpen {C K O S T : Point} (hO : Centre O α) (hA : OnCircle A α)
    (hK : OnRay K A C) (hKα : InsideCircle K α ∨ OnCircle K α)
    (hAT_out : Prop16.Outside A T α) (hTS : SameSideOf T S A C) :
    NearVertexOpen A (MixedAngle.ofSegment A C α S).region :=
  (near_across hO hTS.triangle.bac (near_inside_of_onRay hA hK hKα)
    (Prop16.outside_of_onRay hAT_out)).1.mono fun _ hP =>
      MixedAngle.region_ofSegment.2 ⟨hP.1.1.trans hTS, hP.2⟩

/-- **The angle of a segment falls short of exactly the angles not within the angle CAT.** In
the figure of `exceeds_iff`, the angle of the segment falls short of the angle CAR exactly
when R is not on C's side of AT: on AT, or beyond it. Then the whole segment lies within the
angle CAT, which lies within the angle CAR, and the points within the angle CAT and without
the circle are the excess. Were R on C's side, the segment's angle would exceed CAR. -/
theorem fallsShort_iff {C K O R S T : Point} (hO : Centre O α) (hA : OnCircle A α)
    (hK : OnRay K A C) (hKα : InsideCircle K α ∨ OnCircle K α)
    (hAT_out : Prop16.Outside A T α) (hAT_in : Prop16.FallsWithin A T α)
    (hTS : SameSideOf T S A C) (hRS : SameSideOf R S A C) :
    (MixedAngle.ofSegment A C α S).FallsShort C R ↔ ¬ SameSideOf R C A T := by
  constructor
  · intro hFS hRC
    exact LocallyLess.asymm ((exceeds_iff hO hA hK hKα hAT_out hAT_in hTS hRS).2 hRC).2 hFS.2.2
  · intro hRC
    have hRT : SameSideOf R T A C := hRS.trans hTS.symm
    have hsub := WithinAngle.of_not_sameSideOf hRT hRC
    have hKO : SameSideOf K O A T :=
      Prop16.sameSideOf_of_inside hA hAT_out (centre_inside hO) hKα hK.2.1
    have hCO : SameSideOf C O A T := SameSideOf.of_onRay hK.symm hKO
    have hacross := near_across hO hTS.triangle.bac (near_inside_of_onRay hA hK hKα)
      (Prop16.outside_of_onRay hAT_out)
    obtain ⟨γ₀, hγ₀⟩ := exists_centre A
    refine ⟨hRS.triangle.bac, nearVertexOpen hO hA hK hKα hAT_out hTS,
      ⟨γ₀, hγ₀, fun P _ hP => ?_⟩, hacross.2.mono fun P hP =>
        ⟨hsub P hP.1, fun h' => hP.2.1 (MixedAngle.region_ofSegment.1 h').2⟩⟩
    obtain ⟨hPS, hPα⟩ := MixedAngle.region_ofSegment.1 hP
    exact hsub P ⟨hPS.trans hTS.symm,
      (Prop16.sameSideOf_of_inside hA hAT_out (centre_inside hO) (Or.inl hPα)
        (fun e => inside_not_on (e ▸ hPα) hA)).trans hCO.symm⟩

/-- **The tangent's two parts.** A straight line AT at right angles to the radius OA satisfies
III.16's two parts: OA is produced beyond O to B, and the angle BAT is the angle OAT
(`BookIII.Prop16`). -/
theorem tangent_parts {O T : Point} (hO : Centre O α) (hA : OnCircle A α)
    (hT : ¬ Collinear A O T) (hOAT : ∠ O A T = ∟) :
    Prop16.Outside A T α ∧ Prop16.FallsWithin A T α := by
  have hAOT : Triangle A O T := hT
  obtain ⟨B, hAOB⟩ := produce hAOT.ne₁₂
  have hBray : OnRay B A O := OnRay.of_beyond hAOB
  have hBAT : ∠ B A T = ∟ := by
    rw [angle_onRay_left hBray hAOT.ne₁₃.symm]; exact hOAT
  have hABT : ¬ Collinear A B T := ((sameSideOf_congr_line hBray).2 (sameSideOf_self hAOT)).triangle
  exact BookIII.Prop16 hO hA hAOB hABT hBAT

/-- **The straight line at right angles to the radius, on the segment's side.** Let AC be a
straight line in a circle about O, not through the centre, and S a point off AC. A straight
line AT can be drawn at right angles to OA, with T on S's side of AC: the perpendicular at A
[I. 11], produced beyond A if it falls on the other side (I.13, `adjacent_eq_of_right`). It is
not AC itself, for every point of it but A is without the circle (`tangent_parts`), and C is
on it. -/
theorem exists_tangent {C O S : Point} (hO : Centre O α) (hA : OnCircle A α)
    (hC : OnCircle C α) (hACO : ¬ Collinear A C O) (hS : ¬ Collinear A C S) :
    ∃ T : Point, ¬ Collinear A O T ∧ ∠ O A T = ∟ ∧ SameSideOf T S A C := by
  have hACO' : Triangle A C O := hACO
  have hACS : Triangle A C S := hS
  have hAO : A ≠ O := hACO'.ne₁₃
  have hAC : A ≠ C := hACO'.ne₁₂
  obtain ⟨N, hA_N, hO_N⟩ := Postulate1 A O hAO
  obtain ⟨F, hFC, hright⟩ := BookI.Prop11 hAO ⟨N, hA_N, hO_N, hA_N⟩ hACO'.acb
  have hOAF : ∠ O A F = ∟ := hright O ⟨N, hA_N, hO_N, hO_N⟩ hAO.symm
  have hAOF : Triangle A O F := hFC.triangle
  have hAF : A ≠ F := hAOF.ne₁₃
  /- F is off AC: were it on AC, C would be a point of AF other than A, without the circle. -/
  have hACF : Triangle A C F := by
    rintro ⟨L, hA_L, hC_L, hF_L⟩
    exact (((tangent_parts hO hA hAOF hOAF).1 C ⟨L, hA_L, hF_L, hC_L⟩ hAC.symm).2) hC
  by_cases hFS : SameSideOf F S A C
  · exact ⟨F, hAOF, hOAF, hFS⟩
  /- Otherwise FA is produced beyond A to T, on S's side, and the angle OAT is right too. -/
  obtain ⟨T, hFAT⟩ := produce hAF.symm
  have hFT : OppositeSidesOf F T A C := (OppositeSidesOf.of_between hACF.bac hFAT).swap
  have hFS' : OppositeSidesOf F S A C :=
    oppositeSidesOf_of_not_sameSideOf hACF (sameSideOf_self hACS) hFS
  have hTS : SameSideOf T S A C := (OppositeSidesOf.sameSideOf hFS' hFT).symm
  obtain ⟨M, hF_M, hA_M⟩ := Postulate1 F A hAF.symm
  have hT_M : OnLine T M := on_line_of_between hFAT hF_M hA_M
  have hO_M : ¬ OnLine O M := fun h => hAOF ⟨M, hA_M, h, hF_M⟩
  have hFAO : ∠ F A O = ∟ := by rw [angle_symm hAF.symm hAO.symm]; exact hOAF
  have hOAT : ∠ O A T = ∟ := (adjacent_eq_of_right hF_M hT_M hFAT hO_M hFAO).symm.trans hFAO
  exact ⟨T, fun ⟨L, hA_L, hO_L, hT_L⟩ =>
    hO_M (line_unique (ne_of_between (between_symm hFAT)).symm hA_L hT_L hA_M hT_M ▸ hO_L),
    hOAT, hTS⟩

/-- **The angle with the tangent, the centre on the segment's side.** If the centre O is on T's
side of AC, O is within the angle CAT (the circle is on O's side of AT), and the angle CAT is
the angle OAC and a right angle. -/
theorem angle_tangent_of_sameSideOf {C O T : Point} (hO : Centre O α) (hA : OnCircle A α)
    (hC : OnCircle C α) (hAC : A ≠ C) (hAT_out : Prop16.Outside A T α) (hOAT : ∠ O A T = ∟)
    (hOT : SameSideOf O T A C) : ∠ C A T = ∠ O A C + ∟ := by
  have hCO : SameSideOf C O A T :=
    Prop16.sameSideOf_of_inside hA hAT_out (centre_inside hO) (Or.inr hC) hAC.symm
  rw [angle_add_of_within hOT hCO.symm, hOAT, angle_symm hAC.symm (ne_of_centre_of_on hO hA).symm]

/-- **The angle with the tangent, the centre on the other side.** If the centre O is across
AC from T, TA is produced beyond A to T₁, which is on O's side; the angle CAT₁ is the angle
OAC and a right angle (`angle_tangent_of_sameSideOf`), and with the angle CAT it makes two
right angles [I. 13]. -/
theorem angle_tangent_of_oppositeSidesOf {C O T : Point} (hO : Centre O α) (hA : OnCircle A α)
    (hC : OnCircle C α) (hAC : A ≠ C) (hAT_out : Prop16.Outside A T α) (hOAT : ∠ O A T = ∟)
    (hOT : OppositeSidesOf O T A C) : ∠ C A T + (∠ O A C + ∟) = ∟ + ∟ := by
  have hAT : A ≠ T := hAT_out.ne hA (centre_inside hO)
  have hOA : O ≠ A := (ne_of_centre_of_on hO hA).symm
  obtain ⟨T₁, hTAT₁⟩ := produce hAT.symm
  have hAT₁ : A ≠ T₁ := ne_of_between (between_symm hTAT₁) |>.symm
  obtain ⟨L, hT_L, hA_L⟩ := Postulate1 T A hAT.symm
  have hT₁_L : OnLine T₁ L := on_line_of_between hTAT₁ hT_L hA_L
  have hoffL : ∀ X : Point, (InsideCircle X α ∨ OnCircle X α) → X ≠ A → ¬ OnLine X L :=
    fun X hX hXA hX_L => by
      have hout := hAT_out X ⟨L, hA_L, hT_L, hX_L⟩ hXA
      rcases hX with h | h
      · exact hout.1 h
      · exact hout.2 h
  have hACT : Triangle A C T := hOT.symm.triangle
  have hTT₁ : OppositeSidesOf T T₁ A C := (OppositeSidesOf.of_between hACT.bac hTAT₁).swap
  have hOT₁ : SameSideOf O T₁ A C := OppositeSidesOf.sameSideOf hOT.symm hTT₁
  have hAT₁_out : Prop16.Outside A T₁ α := fun P hP hPA =>
    hAT_out P ⟨L, hA_L, hT_L, onLine_of_collinear hAT₁ hP hA_L hT₁_L⟩ hPA
  have hTAO : ∠ T A O = ∟ := by rw [angle_symm hAT.symm hOA]; exact hOAT
  have hOAT₁ : ∠ O A T₁ = ∟ :=
    (adjacent_eq_of_right hT_L hT₁_L hTAT₁ (hoffL O (Or.inl (centre_inside hO)) hOA)
      hTAO).symm.trans hTAO
  have h₁ := angle_tangent_of_sameSideOf hO hA hC hAC hAT₁_out hOAT₁ hOT₁
  have hC_L : ¬ OnLine C L := hoffL C (Or.inr hC) hAC.symm
  have h₁₃ := BookI.Prop13 hTAT₁ (fun ⟨M, hT_M, hT₁_M, hC_M⟩ =>
    hC_L (line_unique (ne_of_between_ends hTAT₁) hT_M hT₁_M hT_L hT₁_L ▸ hC_M))
  rw [← h₁, angle_symm hAC.symm hAT.symm]
  exact h₁₃

/-- **Placement at another vertex, for the angle of a segment.** Take two circles `α`, `α'`
equal to one another, about O and O′, with straight lines AC and A′C′ in them, equal to one
another, and neither through its centre. Let the segment on S's side of AC and the segment on
S′'s side of A′C′ be of one kind: the centre on the segment's side in both, or in neither.
Then a rectilineal angle CAR placed along AC on S's side and an equal angle C′A′R′ placed
along A′C′ on S′'s side are compared alike: the angle of the one segment exceeds, or falls
short of, the one exactly when the angle of the other segment exceeds, or falls short of, the
other. The segments must be of one kind: on one straight line in one circle, the angle of
the greater segment exceeds a right angle, and the angle of the less segment falls short of
it (III.31).

Let AT, A′T′ be drawn at right angles to the radii, on the segments' sides
(`exists_tangent`). By `exceeds_iff` and `fallsShort_iff`, each comparison is decided by
whether the angle CAR is less than the angle CAT. The triangles OAC, O′A′C′ have their sides
equal, so the angles OAC, O′A′C′ are equal [I. 8], and so are the angles CAT, C′A′T′
(`angle_tangent_of_sameSideOf`, `angle_tangent_of_oppositeSidesOf`, C.N. 3). No figure is
moved but the triangles of I.8. -/
theorem congruent {C O R S A' C' O' R' S' : Point} {α' : Circle}
    (hO : Centre O α) (hA : OnCircle A α) (hC : OnCircle C α) (hACO : ¬ Collinear A C O)
    (hO' : Centre O' α') (hA' : OnCircle A' α') (hC' : OnCircle C' α')
    (hA'C'O' : ¬ Collinear A' C' O') (hαα' : EqualCircles α α') (hAC : ‖A C‖ = ‖A' C'‖)
    (hkind : SameSideOf O S A C ↔ SameSideOf O' S' A' C')
    (hRS : SameSideOf R S A C) (hR'S' : SameSideOf R' S' A' C') (hCAR : ∠ C A R = ∠ C' A' R') :
    ((MixedAngle.ofSegment A C α S).Exceeds C R ↔
        (MixedAngle.ofSegment A' C' α' S').Exceeds C' R') ∧
      ((MixedAngle.ofSegment A C α S).FallsShort C R ↔
        (MixedAngle.ofSegment A' C' α' S').FallsShort C' R') := by
  obtain ⟨T, hT, hOAT, hTS⟩ := exists_tangent hO hA hC hACO hRS.symm.triangle
  obtain ⟨T', hT', hO'A'T', hT'S'⟩ := exists_tangent hO' hA' hC' hA'C'O' hR'S'.symm.triangle
  have hACO' : Triangle A C O := hACO
  have hA'C'O'' : Triangle A' C' O' := hA'C'O'
  have hparts := tangent_parts hO hA hT hOAT
  have hparts' := tangent_parts hO' hA' hT' hO'A'T'
  have hOAC : ∠ O A C = ∠ O' A' C' := by
    have hr₁ : ‖A O‖ = ‖A' O'‖ := by
      rw [len_symm A O, len_symm A' O']; exact hαα'.radii hO hO' hA hA'
    exact BookI.Prop8 hACO'.acb hA'C'O''.acb hr₁ hAC (hαα'.radii hO hO' hC hC')
  have hCAT : ∠ C A T = ∠ C' A' T' := by
    by_cases hOS : SameSideOf O S A C
    · rw [angle_tangent_of_sameSideOf hO hA hC hACO'.ne₁₂ hparts.1 hOAT (hOS.trans hTS.symm),
        angle_tangent_of_sameSideOf hO' hA' hC' hA'C'O''.ne₁₂ hparts'.1 hO'A'T'
          ((hkind.1 hOS).trans hT'S'.symm), hOAC]
    · have hOS' : ¬ SameSideOf O' S' A' C' := fun h => hOS (hkind.2 h)
      have e₁ := angle_tangent_of_oppositeSidesOf hO hA hC hACO'.ne₁₂ hparts.1 hOAT
        (oppositeSidesOf_of_not_sameSideOf hACO' hTS hOS)
      have e₂ := angle_tangent_of_oppositeSidesOf hO' hA' hC' hA'C'O''.ne₁₂ hparts'.1 hO'A'T'
        (oppositeSidesOf_of_not_sameSideOf hA'C'O'' hT'S' hOS')
      rw [hOAC] at e₁
      exact CommonNotion3 (e₁.trans e₂.symm) rfl
  have hAC₁ : A ≠ C := hACO'.ne₁₂
  have hA'C'₁ : A' ≠ C' := hA'C'O''.ne₁₂
  rw [exceeds_iff hO hA (OnRay.self hAC₁) (Or.inr hC) hparts.1 hparts.2 hTS hRS,
    exceeds_iff hO' hA' (OnRay.self hA'C'₁) (Or.inr hC') hparts'.1 hparts'.2 hT'S' hR'S',
    fallsShort_iff hO hA (OnRay.self hAC₁) (Or.inr hC) hparts.1 hparts.2 hTS hRS,
    fallsShort_iff hO' hA' (OnRay.self hA'C'₁) (Or.inr hC') hparts'.1 hparts'.2 hT'S' hR'S',
    WithinAngle.iff_angle_lt (hRS.trans hTS.symm),
    WithinAngle.iff_angle_lt (hR'S'.trans hT'S'.symm), hCAR, hCAT]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Segment

/-! ## Check (c) and the comparisons of III.16

Heath's letters: the circle ABC about D as centre, with AB a diameter, and AE drawn from A at
right angles to AB. The angle of the semicircle is `MixedAngle.ofSegment A B ABC E`,
contained by the straight line BA and the circumference on E's side, which is Heath's CHA;
the remaining angle is `MixedAngle.ofContact A E ABC B`, contained by that circumference and
the straight line AE.

The steps take III.16's two parts as hypotheses (`Prop16.Outside A E ABC` and
`Prop16.FallsWithin A E ABC`), and do not cite III.16. So a restatement of III.16 with the
comparisons can prove its two parts first and then these, in its own file, with the steps
before it. The forms for any acute angle (`semicircle_gt_acute`, `horn_lt_acute`),
`horn_wellFormed`, and the placement theorems at the end cite `BookIII.Prop16` or its
porism, and so go after III.16; the forms and the placement theorems are companions. -/

namespace Prop16

/-- The points within the circle are on B's side of AE: on the centre's side
(`sameSideOf_of_inside`), which is B's, since D is between A and B. -/
theorem inside_sameSideOf {A B D E Q : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Outside A E ABC) (hQ : InsideCircle Q ABC) : SameSideOf Q B A E :=
  (sameSideOf_of_inside hA hAE_out (centre_inside hD) (Or.inl hQ)
    (fun e => inside_not_on (e ▸ hQ) hA)).trans
    (SameSideOf.of_onRay (OnRay.of_between hADB)
      (sameSideOf_self (show Triangle A B E from hE).acb))

/-- **No straight line between, near A.** For a point F within the angle EAB, some circle
about A holds no point within the angle FAB, nor on the ray AF, that is not within the
circle. This is III.16's second part made local: the straight line AF falls within the circle
at some G (on F's side of A, since the circle lies on B's side of AE), and near A the angle
GAD lies within the circle (`near_inside_of_angle`). -/
theorem near_inside {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Outside A E ABC) (hAE_in : FallsWithin A E ABC) (hF : WithinAngle E A B F) :
    LocallyWithin A (fun P => WithinAngle F A B P ∨ OnRay P A F)
      (fun P => InsideCircle P ABC) := by
  obtain ⟨G, hG, hGα⟩ := hAE_in F hF.1.triangle
  have hGA : G ≠ A := fun e => inside_not_on (e ▸ hGα) hA
  have hGB : SameSideOf G B A E := inside_sameSideOf hD hA hADB hE hAE_out hGα
  have hGray : OnRay G A F := OnRay.of_sameSideOf (hGB.trans hF.1.symm) hG hGA
  have hDray : OnRay D A B := OnRay.of_between hADB
  have hGE : SameSideOf G E A B := SameSideOf.of_onRay hGray hF.2
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hDray.1
  have hD_L : OnLine D L := hDray.onLine hA_L hB_L
  have hG_L : ¬ OnLine G L := not_on_line_of_same_side (hGE.sameSide hA_L hB_L)
  have hGAD : Triangle G A D := (Triangle.of_line hA_L hD_L hDray.2.1.symm hG_L).cab
  obtain ⟨γ, hγ, hnear⟩ :=
    near_inside_of_angle (Or.inr hA) (Or.inl hGα) (Or.inl (centre_inside hD)) hGAD
  refine ⟨γ, hγ, fun P hPγ hP => hnear P hPγ ?_⟩
  rcases hP with hW | hR
  · exact Or.inl ((WithinAngle.congr hGray hDray).2 hW)
  · exact Or.inr (Or.inl (OnRay.of_sameRay hR hGray))

/-- **The horn-like angle is not nothing.** Every circle about A, however small, holds a
whole circle within the remaining angle of III.16: within the angle EAB and without the
circle. (Points of AB near A are within the circle, every point of AE but A is without it,
and the circumference crosses between them: `near_across`.) So the upper bounds below are not
satisfied by an empty region, nor by an edge. -/
theorem horn_nearVertex {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Outside A E ABC) :
    NearVertexOpen A (MixedAngle.ofContact A E ABC B).region :=
  (near_across hD (show Triangle A B E from hE).bac
    (near_inside_of_onRay hA (OnRay.of_between hADB) (Or.inl (centre_inside hD)))
    (outside_of_onRay hAE_out)).2.mono fun _ hP =>
      MixedAngle.region_ofContact.2 ⟨WithinAngle.comm.1 hP.1, hP.2⟩

/-- **The angle of the semicircle is not nothing.** Every circle about A holds a whole circle
within the angle BAE and within the circle, which is in the angle of the semicircle
(`near_across`). -/
theorem semicircle_nearVertex {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Outside A E ABC) :
    NearVertexOpen A (MixedAngle.ofSegment A B ABC E).region :=
  (near_across hD (show Triangle A B E from hE).bac
    (near_inside_of_onRay hA (OnRay.of_between hADB) (Or.inl (centre_inside hD)))
    (outside_of_onRay hAE_out)).1.mono fun _ hP =>
      MixedAngle.region_ofSegment.2 ⟨hP.1.1, hP.2⟩

/-- **No straight ray runs within the horn.** For every point F within the angle EAB, the
points of the ray AF near A are not in the remaining angle: they are within the circle. So
the horn is not the region of any rectilineal angle, though it holds whole circles as near A
as we please (`horn_nearVertex`). -/
theorem horn_no_ray {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Outside A E ABC) (hAE_in : FallsWithin A E ABC) (hF : WithinAngle E A B F) :
    LocallyWithin A (fun P => OnRay P A F)
      (fun P => ¬ (MixedAngle.ofContact A E ABC B).region P) := by
  obtain ⟨γ, hγ, hnear⟩ := near_inside hD hA hADB hE hAE_out hAE_in hF
  exact ⟨γ, hγ, fun P hPγ hPF hP =>
    (MixedAngle.region_ofContact.1 hP).2.1 (hnear P hPγ (Or.inr hPF))⟩

/-- **The horn lies within every angle EAF near A.** For a point F within the angle EAB, near
A a point of the remaining angle cannot be on AF or beyond it, for there the points are
within the circle (`near_inside`). -/
theorem horn_within {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Outside A E ABC) (hAE_in : FallsWithin A E ABC) (hFw : WithinAngle E A B F) :
    LocallyWithin A (MixedAngle.ofContact A E ABC B).region (WithinAngle E A F) := by
  have hF : SameSideOf F B A E := hFw.1
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE hAE_out hAE_in hFw
  refine ⟨γ₀, hγ₀, fun P hPγ hP => ?_⟩
  obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
  have hPF : SameSideOf P F A E := hW.1.trans hF.symm
  refine ⟨hPF, ?_⟩
  have hAF : A ≠ F := hF.triangle.ne₁₃
  obtain ⟨M, hA_M, hF_M⟩ := Postulate1 A F hAF
  have hE_M : ¬ OnLine E M := fun h => hF.triangle ⟨M, hA_M, h, hF_M⟩
  have hB_M : ¬ OnLine B M := fun h => hFw.2.triangle ⟨M, hA_M, h, hF_M⟩
  have hPA : P ≠ A := hW.1.triangle.ne₁₃.symm
  by_cases hP_M : OnLine P M
  · exact absurd (hnear P hPγ (Or.inr (OnRay.of_sameSideOf hPF ⟨M, hA_M, hF_M, hP_M⟩ hPA)))
      hout.1
  have hEB_M : ¬ SameSide E B M := fun h =>
    hFw.not_sameSideOf (SameSideOf.of_line hAF hA_M hF_M h)
  rcases same_side_or hE_M hB_M hP_M hEB_M with h | h
  · exact SameSideOf.of_line hAF hA_M hF_M (same_side_symm h)
  · exact absurd (hnear P hPγ (Or.inl ⟨SameSideOf.of_line hAF hA_M hF_M (same_side_symm h),
      hW.2.trans hFw.2.symm⟩)) hout.1

/-- **The angle of contact does not depend on the straight line that names its branch**, in
III.16's figure, where AE is at right angles to the diameter AB. For any point B′ on B's side
of AE, that is, any straight line AB′ from A into the circle, the angle of contact named by
B′ is locally equal to the one named by the diameter. If B′ is on the ray AB, the regions are
the same (`ofContact_congr`). If it is within the angle EAB, the one region lies within the
other, and the rest, between AB′ and AB, is within the circle near A (`horn_within`). If it
is on the other side of AB, the same holds with AE produced beyond A to E′, which is at right
angles to AB as well: the rest, between AB and AB′, is within the circle near A
(`near_inside`, for E′). -/
theorem horn_locallyEqual {A B B' D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Outside A E ABC) (hAE_in : FallsWithin A E ABC) (hB' : SameSideOf B' B A E) :
    LocallyEqual A (MixedAngle.ofContact A E ABC B).region
      (MixedAngle.ofContact A E ABC B').region := by
  have hABE : Triangle A B E := hE
  have hAB : A ≠ B := hABE.ne₁₂
  have hAE : A ≠ E := hABE.ne₁₃
  have hB'A : B' ≠ A := hB'.triangle.ne₁₃.symm
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hE_L : ¬ OnLine E L := hABE.off_line hA_L hB_L
  by_cases hB'_L : OnLine B' L
  · /- B′ on the ray AB. -/
    have hray : OnRay B' A B := OnRay.of_sameSideOf hB' ⟨L, hA_L, hB_L, hB'_L⟩ hB'A
    exact LocallyEqual.of_iff fun P =>
      (MixedAngle.ofContact_congr (P := P) (α := ABC) (OnRay.self hAE) hray).symm
  by_cases hs : SameSide B' E L
  · /- B′ within the angle EAB. -/
    have hFw : WithinAngle E A B B' := ⟨hB', SameSideOf.of_line hAB hA_L hB_L hs⟩
    obtain ⟨γ₀, hγ₀⟩ := exists_centre A
    obtain ⟨γ, hγ, hW⟩ := horn_within hD hA hADB hE hAE_out hAE_in hFw
    exact ⟨⟨γ, hγ, fun P hPγ hP => MixedAngle.region_ofContact.2
        ⟨hW P hPγ hP, (MixedAngle.region_ofContact.1 hP).2⟩⟩,
      ⟨γ₀, hγ₀, fun P _ hP => MixedAngle.region_ofContact.2
        ⟨WithinAngle.mono_left hFw (MixedAngle.region_ofContact.1 hP).1,
          (MixedAngle.region_ofContact.1 hP).2⟩⟩⟩
  /- B′ on the other side of AB from E: AE is produced beyond A to E′. -/
  have hopp : OppositeSidesOf B' E A B :=
    OppositeSidesOf.of_line hAB hA_L hB_L ⟨hB'_L, hE_L, hs⟩
  obtain ⟨E', hEAE'⟩ := produce hAE.symm
  have hEE'_AB : OppositeSidesOf E E' A B := (OppositeSidesOf.of_between hABE.bac hEAE').swap
  have hB'E' : SameSideOf B' E' A B := OppositeSidesOf.sameSideOf hopp.symm hEE'_AB
  have hABE' : ¬ Collinear A B E' := hB'E'.symm.triangle
  have hAE' : A ≠ E' := (ne_of_between (between_symm hEAE')).symm
  obtain ⟨M, hE_M, hA_M⟩ := Postulate1 E A hAE.symm
  have hE'_M : OnLine E' M := on_line_of_between hEAE' hE_M hA_M
  have hcol : Collinear A E E' := ⟨M, hA_M, hE_M, hE'_M⟩
  have hcol' : Collinear A E' E := ⟨M, hA_M, hE'_M, hE_M⟩
  /- III.16's two parts hold for AE′, which is the straight line AE. -/
  have hAE'_out : Outside A E' ABC :=
    fun P hP hPA => hAE_out P (Collinear.change_point hAE' hcol' hP) hPA
  have hAE'_in : FallsWithin A E' ABC :=
    fun F hF => hAE_in F fun h => hF (Collinear.change_point hAE hcol h)
  have hFw' : WithinAngle E' A B B' :=
    ⟨(sameSideOf_congr_collinear hAE hAE'.symm hcol).2 hB', hB'E'⟩
  obtain ⟨γ₁, hγ₁, hnear₁⟩ := near_inside hD hA hADB hABE' hAE'_out hAE'_in hFw'
  have hDray : OnRay D A B := OnRay.of_between hADB
  obtain ⟨γ₂, hγ₂, hnear₂⟩ := near_inside_of_ray hA (Or.inl (centre_inside hD)) hDray.2.1.symm
  obtain ⟨γ, hγ, hboth⟩ := exists_inside_both hγ₁ hγ₂
  /- E and B are on one side of AB′: AB′ separates E′ from B, and E from E′. -/
  have hAB'B : Triangle A B' B := by
    rintro ⟨N, hA_N, hB'_N, hB_N⟩
    exact hB'_L (onLine_of_collinear hAB ⟨N, hA_N, hB_N, hB'_N⟩ hA_L hB_L)
  have hEE'_AB' : OppositeSidesOf E E' A B' :=
    (OppositeSidesOf.of_between hB'.triangle.cab hEAE').swap
  have hE'B : OppositeSidesOf E' B A B' := by
    obtain ⟨N, hA_N, hB'_N⟩ := Postulate1 A B' hB'A.symm
    exact OppositeSidesOf.of_line hB'A.symm hA_N hB'_N
      ⟨(hEE'_AB'.oppositeSides hA_N hB'_N).2.1, hAB'B.off_line hA_N hB'_N,
        fun h => hFw'.not_sameSideOf (SameSideOf.of_line hB'A.symm hA_N hB'_N h)⟩
  have hEB : SameSideOf E B A B' := OppositeSidesOf.sameSideOf hEE'_AB'.symm hE'B
  have hBin : WithinAngle E A B' B := ⟨hB'.symm, hEB.symm⟩
  refine ⟨⟨γ, hγ, fun P _ hP => ?_⟩, ⟨γ, hγ, fun P hPγ hP => ?_⟩⟩
  · obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
    exact MixedAngle.region_ofContact.2 ⟨WithinAngle.mono_left hBin hW, hout⟩
  · obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
    have hPB : SameSideOf P B A E := hW.1.trans hB'
    have hPA : P ≠ A := hW.1.triangle.ne₁₃.symm
    refine MixedAngle.region_ofContact.2 ⟨⟨hPB, ?_⟩, hout⟩
    by_cases hP_L : OnLine P L
    · exact absurd (hnear₂ P (hboth P hPγ).2
        (OnRay.of_sameRay (OnRay.of_sameSideOf hPB ⟨L, hA_L, hB_L, hP_L⟩ hPA) hDray)) hout.1
    by_cases hsP : SameSide P E L
    · exact SameSideOf.of_line hAB hA_L hB_L hsP
    · exfalso
      have hPE : OppositeSidesOf E P A B :=
        OppositeSidesOf.of_line hAB hA_L hB_L ⟨hE_L, hP_L, fun h => hsP (same_side_symm h)⟩
      have hPB' : SameSideOf P B' A B := OppositeSidesOf.sameSideOf hPE hopp.symm
      exact hout.1 (hnear₁ P (hboth P hPγ).1 (Or.inl ⟨hW.2.trans hEB, hPB'⟩))

/-- **Heath's "remaining angle".** Within the right angle BAE, every point is in the angle of
the semicircle, or in the remaining angle, or on the circumference; and every point of those
is within the right angle. The three parts have no point in common, for no point is both
within and on a circle, and a point without it is neither (`OutsideCircle`). So the remaining
angle is what is left of the right angle BAE when the angle of the semicircle is taken away,
with the circumference between them. -/
theorem remaining {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Outside A E ABC) (P : Point) :
    WithinAngle B A E P ↔ (MixedAngle.ofSegment A B ABC E).region P ∨
      (MixedAngle.ofContact A E ABC B).region P ∨ (OnCircle P ABC ∧ WithinAngle B A E P) := by
  constructor
  · intro hW
    by_cases hin : InsideCircle P ABC
    · exact Or.inl (MixedAngle.region_ofSegment.2 ⟨hW.1, hin⟩)
    by_cases hon : OnCircle P ABC
    · exact Or.inr (Or.inr ⟨hon, hW⟩)
    exact Or.inr (Or.inl (MixedAngle.region_ofContact.2 ⟨WithinAngle.comm.1 hW, hin, hon⟩))
  · rintro (h | h | h)
    · obtain ⟨hPE, hPα⟩ := MixedAngle.region_ofSegment.1 h
      exact ⟨hPE, inside_sameSideOf hD hA hADB hE hAE_out hPα⟩
    · exact WithinAngle.comm.1 (MixedAngle.region_ofContact.1 h).1
    · exact h.2

/-- **III.16: the angle of the semicircle is greater than any acute rectilineal angle.** For
every point F on E's side of the diameter AB with the angle BAF acute, the angle of the
semicircle exceeds the angle BAF: near A the angle BAF lies within the circle
(`near_inside`), and every circle about A holds whole circles within the circle and within
the angle FAE, which are in the semicircle's angle and not in BAF. -/
theorem semicircle_gt {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hAE_out : Outside A E ABC) (hAE_in : FallsWithin A E ABC)
    (hF : SameSideOf F E A B) (hBAF : ∠ B A F < ∟) :
    (MixedAngle.ofSegment A B ABC E).Exceeds B F := by
  refine ⟨hF.triangle.bac, ?_⟩
  show LocallyLess A (WithinAngle B A F) (MixedAngle.ofSegment A B ABC E).region
  have hlt : ∠ B A F < ∠ B A E := by rw [hBAE]; exact hBAF
  have hFw : WithinAngle E A B F := ⟨sameSideOf_of_angle_lt hF hlt, hF⟩
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE hAE_out hAE_in hFw
  refine ⟨⟨γ₀, hγ₀, fun P hPγ hP => MixedAngle.region_ofSegment.2
    ⟨hP.1.trans hF, hnear P hPγ (Or.inl (WithinAngle.comm.1 hP))⟩⟩, ?_⟩
  refine (near_across hD hFw.1.triangle.cab ⟨γ₀, hγ₀, fun P hP hPF => hnear P hP (Or.inr hPF)⟩
    (outside_of_onRay hAE_out)).1.mono fun P hP => ?_
  obtain ⟨hPw, hPα⟩ := hP
  refine ⟨MixedAngle.region_ofSegment.2
    ⟨(WithinAngle.mono_left hFw (WithinAngle.comm.1 hPw)).2, hPα⟩, fun h' => ?_⟩
  exact hFw.not_sameSideOf (hPw.1.symm.trans h'.2)

/-- **III.16: the remaining angle is less than any acute rectilineal angle.** For every point
F on the circle's side of AE with the angle EAF acute, the remaining angle, between AE and
the circumference, falls short of the angle EAF: it comes as near A as we please
(`horn_nearVertex`); near A it lies within the angle EAF (`horn_within`); and every circle
about A holds whole circles within the angle EAF and within the circle, which are not in the
horn. -/
theorem horn_lt {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hAE_out : Outside A E ABC) (hAE_in : FallsWithin A E ABC)
    (hF : SameSideOf F B A E) (hEAF : ∠ E A F < ∟) :
    (MixedAngle.ofContact A E ABC B).FallsShort E F := by
  refine ⟨hF.triangle.bac, horn_nearVertex hD hA hADB hE hAE_out, ?_⟩
  show LocallyLess A (MixedAngle.ofContact A E ABC B).region (WithinAngle E A F)
  have hABE : Triangle A B E := hE
  have hlt : ∠ E A F < ∠ E A B := by
    rw [angle_symm hABE.ne₁₃.symm hABE.ne₁₂.symm, hBAE]; exact hEAF
  have hFw : WithinAngle E A B F := ⟨hF, sameSideOf_of_angle_lt hF hlt⟩
  refine ⟨horn_within hD hA hADB hE hAE_out hAE_in hFw, ?_⟩
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE hAE_out hAE_in hFw
  exact (near_across hD hFw.1.triangle.cab ⟨γ₀, hγ₀, fun P hP hPF => hnear P hP (Or.inr hPF)⟩
    (outside_of_onRay hAE_out)).1.mono fun P hP =>
      ⟨WithinAngle.comm.1 hP.1, fun h' => (MixedAngle.region_ofContact.1 h').2.1 hP.2⟩

/-- **The angle of the semicircle is less than a right angle.** The angle of the semicircle
comes as near A as we please (`semicircle_nearVertex`) and lies within the right angle BAE
(the whole circle is on B's side of AE), and every circle about A holds whole circles of the
horn, which are within BAE and not in the semicircle's angle. With `semicircle_gt` and
`LocallyLess.trans`, the angle of the semicircle lies strictly between every acute angle and
a right angle. -/
theorem semicircle_lt_right {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hAE_out : Outside A E ABC) :
    (MixedAngle.ofSegment A B ABC E).FallsShort B E := by
  refine ⟨(show Triangle A B E from hE).bac, semicircle_nearVertex hD hA hADB hE hAE_out, ?_⟩
  show LocallyLess A (MixedAngle.ofSegment A B ABC E).region (WithinAngle B A E)
  obtain ⟨γ₀, hγ₀⟩ := exists_centre A
  refine ⟨⟨γ₀, hγ₀, fun P _ hP => ?_⟩,
    (horn_nearVertex hD hA hADB hE hAE_out).mono fun P hP => ?_⟩
  · obtain ⟨hPE, hPα⟩ := MixedAngle.region_ofSegment.1 hP
    exact ⟨hPE, inside_sameSideOf hD hA hADB hE hAE_out hPα⟩
  · obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
    exact ⟨WithinAngle.comm.1 hW, fun h' => hout.1 (MixedAngle.region_ofSegment.1 h').2⟩

/-- **III.16, for any acute rectilineal angle.** Every acute rectilineal angle XYZ can be
placed at A along AB, on E's side [I. 23], and there the angle of the semicircle exceeds it.
(Placed so, it has one region whatever the placement: `WithinAngle.locallyLess_placement`.) -/
theorem semicircle_gt_acute {A B D E X Y Z : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hXYZ : Triangle X Y Z) (hacute : ∠ X Y Z < ∟) :
    ∃ F : Point, SameSideOf F E A B ∧ ∠ B A F = ∠ X Y Z ∧
      (MixedAngle.ofSegment A B ABC E).Exceeds B F := by
  have hABE : Triangle A B E := hE
  have h := BookIII.Prop16 hD hA hADB hE hBAE
  obtain ⟨F, G, hG, hF, hFAG⟩ := BookI.Prop23 hABE.ne₁₂ hXYZ hE
  have hFA : F ≠ A := hF.triangle.ne₁₃.symm
  have hBAF : ∠ B A F = ∠ X Y Z := by
    rw [angle_symm hABE.ne₁₂.symm hFA, ← angle_onRay_right hG hFA, hFAG]
  exact ⟨F, hF, hBAF, semicircle_gt hD hA hADB hE hBAE h.1 h.2 hF (hBAF ▸ hacute)⟩

/-- **III.16, the remaining angle, for any acute rectilineal angle.** Every acute rectilineal
angle XYZ can be placed at A along AE, towards the circle [I. 23], and there the remaining
angle falls short of it. -/
theorem horn_lt_acute {A B D E X Y Z : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hXYZ : Triangle X Y Z) (hacute : ∠ X Y Z < ∟) :
    ∃ F : Point, SameSideOf F B A E ∧ ∠ E A F = ∠ X Y Z ∧
      (MixedAngle.ofContact A E ABC B).FallsShort E F := by
  have hABE : Triangle A B E := hE
  have h := BookIII.Prop16 hD hA hADB hE hBAE
  obtain ⟨F, G, hG, hF, hFAG⟩ := BookI.Prop23 hABE.ne₁₃ hXYZ hABE.acb
  have hFA : F ≠ A := hF.triangle.ne₁₃.symm
  have hEAF : ∠ E A F = ∠ X Y Z := by
    rw [angle_symm hABE.ne₁₃.symm hFA, ← angle_onRay_right hG hFA, hFAG]
  exact ⟨F, hF, hEAF, horn_lt hD hA hADB hE hBAE h.1 h.2 hF (hEAF ▸ hacute)⟩

/-- **The angle of the semicircle as Euclid draws it.** A is on the circle, the ray AB passes
within it at the centre D, and E is off AB. -/
theorem semicircle_wellFormed {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E) :
    (MixedAngle.ofSegment A B ABC E).WellFormed :=
  ⟨hA, ⟨D, OnRay.of_between hADB, centre_inside hD⟩, hE⟩

/-- **The angle of contact as Euclid draws it.** A is on the circle; AE, at right angles to
the diameter, touches it (III.16's porism); the ray AB passes within it at the centre D; and
B is off AE. -/
theorem horn_wellFormed {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) : (MixedAngle.ofContact A E ABC B).WellFormed := by
  have hABE : Triangle A B E := hE
  have hDray : OnRay D A B := OnRay.of_between hADB
  have hDAE : ∠ D A E = ∟ := by
    rw [angle_onRay_left hDray hABE.ne₁₃.symm]; exact hBAE
  have hDAE' : Triangle D A E := by
    obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hABE.ne₁₂
    have hD_L : OnLine D L := on_line_of_between_ends hADB hA_L hB_L
    exact (Triangle.of_line hA_L hD_L (ne_of_between hADB) (hABE.off_line hA_L hB_L)).bac
  exact ⟨hA, BookIII.Prop16.porism hD hA hDAE' hDAE, ⟨D, hDray, centre_inside hD⟩, hABE.acb⟩

/-! ### Placement at another vertex, for III.16's angles -/

/-- **The angle of the semicircle exceeds exactly the acute angles.** For F on E's side of
the diameter AB, the angle of the semicircle exceeds the angle BAF exactly when it is acute
(`Segment.exceeds_iff`, with AE as the tangent and the centre D on the ray AB). A companion:
it takes III.16's two parts from `BookIII.Prop16`. -/
theorem semicircle_exceeds_iff {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hF : SameSideOf F E A B) :
    (MixedAngle.ofSegment A B ABC E).Exceeds B F ↔ ∠ B A F < ∟ := by
  have h := BookIII.Prop16 hD hA hADB hE hBAE
  rw [Segment.exceeds_iff hD hA (OnRay.of_between hADB) (Or.inl (centre_inside hD)) h.1 h.2
    (sameSideOf_self (show Triangle A B E from hE)) hF, WithinAngle.iff_angle_lt hF, hBAE]

/-- **The angle of the semicircle falls short of exactly the angles that are not acute.** -/
theorem semicircle_fallsShort_iff {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hF : SameSideOf F E A B) :
    (MixedAngle.ofSegment A B ABC E).FallsShort B F ↔ ¬ ∠ B A F < ∟ := by
  have h := BookIII.Prop16 hD hA hADB hE hBAE
  rw [Segment.fallsShort_iff hD hA (OnRay.of_between hADB) (Or.inl (centre_inside hD)) h.1 h.2
    (sameSideOf_self (show Triangle A B E from hE)) hF, WithinAngle.iff_angle_lt hF, hBAE]

/-- **Placement at another vertex, for the angle of the semicircle.** In any two circles, with
any radii, the angles of the semicircles compare alike with equal rectilineal angles placed
along their diameters on their sides: each is decided by whether the angle is acute. -/
theorem semicircle_congruent {A B D E F A' B' D' E' F' : Point} {ABC A'B'C' : Circle}
    (hD : Centre D ABC) (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) (hF : SameSideOf F E A B)
    (hD' : Centre D' A'B'C') (hA' : OnCircle A' A'B'C') (hA'D'B' : Between A' D' B')
    (hE' : ¬ Collinear A' B' E') (hB'A'E' : ∠ B' A' E' = ∟) (hF' : SameSideOf F' E' A' B')
    (hBAF : ∠ B A F = ∠ B' A' F') :
    ((MixedAngle.ofSegment A B ABC E).Exceeds B F ↔
        (MixedAngle.ofSegment A' B' A'B'C' E').Exceeds B' F') ∧
      ((MixedAngle.ofSegment A B ABC E).FallsShort B F ↔
        (MixedAngle.ofSegment A' B' A'B'C' E').FallsShort B' F') := by
  rw [semicircle_exceeds_iff hD hA hADB hE hBAE hF,
    semicircle_exceeds_iff hD' hA' hA'D'B' hE' hB'A'E' hF',
    semicircle_fallsShort_iff hD hA hADB hE hBAE hF,
    semicircle_fallsShort_iff hD' hA' hA'D'B' hE' hB'A'E' hF', hBAF]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **The angle of contact falls short of exactly the angles on the circle's side of AE.**
Every true angle EAF with F on B's side of AE, acute or not: for an acute one this is
`horn_lt`; otherwise the angle EAB lies within the angle EAF (`WithinAngle.of_not_sameSideOf`),
the horn within the angle EAB, and the points within the angle EAB and within the circle are
the excess. And if F is not on B's side, the horn, which comes as near A as we please, has
points on B's side that are not within the angle EAF. -/
theorem horn_fallsShort_iff {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) :
    (MixedAngle.ofContact A E ABC B).FallsShort E F ↔ SameSideOf F B A E := by
  have hABE : Triangle A B E := hE
  have h := BookIII.Prop16 hD hA hADB hE hBAE
  constructor
  · intro hFS
    refine Classical.byContradiction fun hFB => ?_
    obtain ⟨γ, hγ, hW⟩ := hFS.2.2.1
    obtain ⟨P, hPγ, hP⟩ := hFS.2.1.nearVertex γ hγ
    exact hFB ((hW P hPγ hP).1.symm.trans (MixedAngle.region_ofContact.1 hP).1.1)
  · intro hFB
    by_cases hFE : SameSideOf F E A B
    · have hlt : ∠ E A F < ∟ := by
        have := (WithinAngle.iff_angle_lt hFB).1 hFE
        rwa [angle_symm hABE.ne₁₃.symm hABE.ne₁₂.symm, hBAE] at this
      exact horn_lt hD hA hADB hE hBAE h.1 h.2 hFB hlt
    · have hsub := WithinAngle.of_not_sameSideOf hFB hFE
      obtain ⟨γ₀, hγ₀⟩ := exists_centre A
      refine ⟨hFB.triangle.bac, horn_nearVertex hD hA hADB hE h.1,
        ⟨γ₀, hγ₀, fun P _ hP => hsub P (MixedAngle.region_ofContact.1 hP).1⟩, ?_⟩
      exact (near_across hD hABE.bac
        (near_inside_of_onRay hA (OnRay.of_between hADB) (Or.inl (centre_inside hD)))
        (outside_of_onRay h.1)).1.mono fun P hP =>
          ⟨hsub P (WithinAngle.comm.1 hP.1), fun h' => (MixedAngle.region_ofContact.1 h').2.1 hP.2⟩

/-- **The angle of contact exceeds no rectilineal angle.** Were it to exceed the true angle
EAF, near A every point within EAF would be without the circle. But if F is within the angle
EAB, the points within the angle FAE and within the circle come as near A as we please
(`near_inside`, `near_across`); if F is on B's side and not within it, so do the points
within the angle BAE and within the circle, which are within the angle EAF; and if F is not
on B's side, the points within EAF near A are not in the horn at all. -/
theorem horn_not_exceeds {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟) : ¬ (MixedAngle.ofContact A E ABC B).Exceeds E F := by
  have hABE : Triangle A B E := hE
  have h := BookIII.Prop16 hD hA hADB hE hBAE
  rintro ⟨hEAF, ⟨γ, hγ, hW⟩, -⟩
  have hin : ∀ P, InsideCircle P γ → WithinAngle E A F P → InsideCircle P ABC → False :=
    fun P hPγ hPw hPα => (MixedAngle.region_ofContact.1 (hW P hPγ hPw)).2.1 hPα
  by_cases hFB : SameSideOf F B A E
  · by_cases hFE : SameSideOf F E A B
    · have hFw : WithinAngle E A B F := ⟨hFB, hFE⟩
      obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE h.1 h.2 hFw
      obtain ⟨P, hPγ, hPw, hPα⟩ :=
        (near_across hD hFw.1.triangle.cab ⟨γ₀, hγ₀, fun P hP hPF => hnear P hP (Or.inr hPF)⟩
          (outside_of_onRay h.1)).1.nearVertex γ hγ
      exact hin P hPγ (WithinAngle.comm.1 hPw) hPα
    · have hsub := WithinAngle.of_not_sameSideOf hFB hFE
      obtain ⟨P, hPγ, hPw, hPα⟩ :=
        (near_across hD hABE.bac
          (near_inside_of_onRay hA (OnRay.of_between hADB) (Or.inl (centre_inside hD)))
          (outside_of_onRay h.1)).1.nearVertex γ hγ
      exact hin P hPγ (hsub P (WithinAngle.comm.1 hPw)) hPα
  · obtain ⟨P, hPγ, hPw⟩ := WithinAngle.exists_near hEAF hγ
    exact hFB (hPw.1.symm.trans (MixedAngle.region_ofContact.1 (hW P hPγ hPw)).1.1)

/-- **Placement at another vertex, for the angle of contact.** In any two circles, the angles
of contact compare alike with true rectilineal angles placed along their touching straight
lines on corresponding sides: each falls short of the angle exactly when it is placed on the
circle's side, and exceeds none. -/
theorem horn_congruent {A B D E F A' B' D' E' F' : Point} {ABC A'B'C' : Circle}
    (hD : Centre D ABC) (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟)
    (hD' : Centre D' A'B'C') (hA' : OnCircle A' A'B'C') (hA'D'B' : Between A' D' B')
    (hE' : ¬ Collinear A' B' E') (hB'A'E' : ∠ B' A' E' = ∟)
    (hside : SameSideOf F B A E ↔ SameSideOf F' B' A' E') :
    ((MixedAngle.ofContact A E ABC B).Exceeds E F ↔
        (MixedAngle.ofContact A' E' A'B'C' B').Exceeds E' F') ∧
      ((MixedAngle.ofContact A E ABC B).FallsShort E F ↔
        (MixedAngle.ofContact A' E' A'B'C' B').FallsShort E' F') := by
  rw [horn_fallsShort_iff hD hA hADB hE hBAE, horn_fallsShort_iff hD' hA' hA'D'B' hE' hB'A'E']
  exact ⟨⟨fun h => (horn_not_exceeds hD hA hADB hE hBAE h).elim,
    fun h => (horn_not_exceeds hD' hA' hA'D'B' hE' hB'A'E' h).elim⟩, hside⟩

end Prop16

/-! ## The comparisons of III.31

Heath's letters: the circle ABCD with diameter BC and centre E, and A on it; BA is carried
through to F. The angle of the greater segment is `MixedAngle.ofSegment A C ABCD B`,
contained by the circumference ABC and the straight line AC; the angle of the less segment is
`MixedAngle.ofSegment A C ABCD D`, for a point D on the other side of AC, contained by the
circumference ADC and the straight line AC. A right angle placed along AC on B's side is the
angle CAB, and on D's side the angle CAF.

The steps take III.31's first part, that the angle BAC is right, as a hypothesis, and do not
cite III.31; the forms for any straight line in the circle, which are companions, supply it
from `BookIII.Prop31`. -/

namespace Prop31

/-- **III.31: the angle of the greater segment is greater than a right angle.** The angle of
the greater segment exceeds every right angle CAR placed along AC on B's side. The angle CAR
is the angle CAB (the angle BAC is right, and on one side one ray makes a given angle), which
near A lies within the circle (`near_inside_of_angle`); and every circle about A holds whole
circles within the circle and within the angle between AB and CA produced beyond A, which are
in the greater segment's angle and not in CAB. -/
theorem greater_gt_right {A B C E R : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hBEC : Between B E C) (hAB : A ≠ B) (hAC : A ≠ C) (hBAC : ∠ B A C = ∟)
    (hR : SameSideOf R B A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C ABCD B).Exceeds C R := by
  refine ⟨hR.triangle.bac, ?_⟩
  show LocallyLess A (WithinAngle C A R) (MixedAngle.ofSegment A C ABCD B).region
  have hABC : Triangle A B C := Triangle.of_onCircle hA hB hC hAB (ne_of_between_ends hBEC) hAC
  have hCAB : ∠ C A B = ∟ := by
    rw [angle_symm hAC.symm hAB.symm]; exact hBAC
  have hRray : OnRay R A B := onRay_of_angle_eq hR (hCAR.trans hCAB.symm)
  refine (locallyLess_congr (fun P => WithinAngle.congr (OnRay.self hAC) hRray)
    (fun _ => Iff.rfl)).2 ?_
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside_of_angle (Or.inr hA) (Or.inr hC) (Or.inr hB) hABC.bac.cba
  refine ⟨⟨γ₀, hγ₀, fun P hPγ hP => MixedAngle.region_ofSegment.2
    ⟨hP.1, hnear P hPγ (Or.inl hP)⟩⟩, ?_⟩
  /- CA produced beyond A to C′: its points are without the circle. -/
  obtain ⟨C', hCAC'⟩ := produce hAC.symm
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  have hC'_L : OnLine C' L := on_line_of_between hCAC' hC_L hA_L
  have hB_L : ¬ OnLine B L := hABC.acb.off_line hA_L hC_L
  have hBAC' : Triangle B A C' :=
    (Triangle.of_line hA_L hC'_L (ne_of_between (between_symm hCAC')).symm hB_L).cab
  have hC'col : Collinear A C C' := ⟨L, hA_L, hC_L, hC'_L⟩
  have hopp : OppositeSidesOf C C' A B :=
    (OppositeSidesOf.of_between hABC.bac hCAC').swap
  obtain ⟨N, hA_N, hB_N⟩ := Postulate1 A B hAB
  refine (near_across hE hBAC' (near_inside_of_ray hA (Or.inr hB) hAB)
    (fun P hP => outside_of_between (Or.inr hC) (fun h => inside_not_on h hA)
      (hP.between hCAC'))).1.mono fun P hP => ?_
  obtain ⟨hPw, hPα⟩ := hP
  refine ⟨MixedAngle.region_ofSegment.2
    ⟨(sameSideOf_congr_collinear hAC hBAC'.ne₂₃.symm hC'col).1 hPw.2, hPα⟩, fun h' => ?_⟩
  exact ((hopp.oppositeSides hA_N hB_N).2.2)
    (same_side_trans (h'.2.sameSide hA_N hB_N) (hPw.1.sameSide hA_N hB_N))

/-- **The angle of the less segment is not nothing.** For a point D on the other side of AC
from B, every circle about A holds a whole circle within the angle of the less segment: BA
produced to F, the points of AC near A are within the circle, those of AF are without it, and
the circumference crosses between them, within the angle CAF, which is on D's side of AC
(`near_across`). So the bound `less_lt_right` is not met by an empty region. -/
theorem less_nearVertex {A B C D E : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hBEC : Between B E C) (hAB : A ≠ B) (hAC : A ≠ C) (hBD : OppositeSidesOf B D A C) :
    NearVertexOpen A (MixedAngle.ofSegment A C ABCD D).region := by
  have hABC : Triangle A B C := Triangle.of_onCircle hA hB hC hAB (ne_of_between_ends hBEC) hAC
  obtain ⟨F, hBAF⟩ := produce hAB.symm
  have hBF : OppositeSidesOf B F A C := (OppositeSidesOf.of_between hABC.cab hBAF).swap
  have hDF : SameSideOf D F A C := OppositeSidesOf.sameSideOf hBD hBF
  exact (near_across hE hBF.symm.triangle.bac (near_inside_of_ray hA (Or.inr hC) hAC)
    (fun P hP => outside_of_between (Or.inr hB) (fun h => inside_not_on h hA)
      (hP.between hBAF))).1.mono fun P hP =>
        MixedAngle.region_ofSegment.2 ⟨hP.1.1.trans hDF.symm, hP.2⟩

/-- **III.31: the angle of the less segment is less than a right angle.** For a point D on
the other side of AC from B, the angle of the less segment falls short of every right angle
CAR placed along AC on D's side. It comes as near A as we please (`less_nearVertex`). The
angle CAR is the angle CAF, BA being produced to F. The less segment lies wholly within the
angle CAF: a point within the circle on F's side of AC, and on AB or beyond it, would give a
point within the circle on the straight line AB outside AB itself (System E, Circle 1, Pasch
2 and 3). And every circle about A holds whole circles within the angle CAF and without the
circle, which are not in the less segment's angle. -/
theorem less_lt_right {A B C D E R : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hBEC : Between B E C) (hAB : A ≠ B) (hAC : A ≠ C) (hBAC : ∠ B A C = ∟)
    (hBD : OppositeSidesOf B D A C) (hR : SameSideOf R D A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C ABCD D).FallsShort C R := by
  refine ⟨hR.triangle.bac, less_nearVertex hE hA hB hC hBEC hAB hAC hBD, ?_⟩
  show LocallyLess A (MixedAngle.ofSegment A C ABCD D).region (WithinAngle C A R)
  have hABC : Triangle A B C := Triangle.of_onCircle hA hB hC hAB (ne_of_between_ends hBEC) hAC
  obtain ⟨F, hBAF⟩ := produce hAB.symm
  obtain ⟨N, hA_N, hB_N⟩ := Postulate1 A B hAB
  have hF_N : OnLine F N := on_line_of_between hBAF hB_N hA_N
  have hC_N : ¬ OnLine C N := hABC.off_line hA_N hB_N
  have hAF : A ≠ F := ne_of_between (between_symm hBAF) |>.symm
  have hBF : OppositeSidesOf B F A C := (OppositeSidesOf.of_between hABC.cab hBAF).swap
  have hDF : SameSideOf D F A C := OppositeSidesOf.sameSideOf hBD hBF
  /- The angle CAF is right, as its adjacent angle BAC is (I.13, `adjacent_eq_of_right`). -/
  have hCAF : ∠ C A F = ∟ := by
    rw [← (adjacent_eq_of_right hB_N hF_N hBAF hC_N hBAC), hBAC]
  have hRray : OnRay R A F := onRay_of_angle_eq (hR.trans hDF) (hCAR.trans hCAF.symm)
  refine (locallyLess_congr (fun _ => Iff.rfl)
    (fun P => WithinAngle.congr (OnRay.self hAC) hRray)).2 ?_
  have hFcol : Collinear A B F := ⟨N, hA_N, hB_N, hF_N⟩
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hAC
  /- No point is on both B's side and D's side of AC. -/
  have hnotB : ∀ T : Point, SameSideOf T D A C → ¬ SameSideOf T B A C := fun T hTD hTB =>
    (hBD.oppositeSides hA_M hC_M).2.2 ((hTB.symm.trans hTD).sameSide hA_M hC_M)
  /- A point T within the circle on the straight line AB lies between A and B (System E,
     Circle 1), and so on B's side of AC (Pasch 2). -/
  have hseg : ∀ T : Point, OnLine T N → InsideCircle T ABCD → SameSideOf T B A C :=
    fun T hT hTα => SameSideOf.of_between_line ⟨M, hA_M, hC_M, hA_M⟩ (sameSideOf_self hABC.acb)
      (between_of_inside_chord hT hA_N hB_N hTα hA hB hAB)
  /- So a point within the circle on D's side of AC is on C's side of AB: were it on AB, it
     would be on B's side of AC; were it on the other side of AB, the straight line from it to
     C would cross AB within the circle (Intersection 1 and Circle 3, through Circle 2), at a point on D's side of
     AC (Pasch 2). -/
  have hside : ∀ P : Point, SameSideOf P D A C → InsideCircle P ABCD → SameSideOf P C A B := by
    intro P hPD hPα
    by_cases hP_N : OnLine P N
    · exact absurd (hseg P hP_N hPα) (hnotB P hPD)
    refine SameSideOf.of_line hAB hA_N hB_N (Classical.byContradiction fun hs => ?_)
    obtain ⟨T, hT_N, hPTC⟩ := OppositeSides.exists_between ⟨hP_N, hC_N, hs⟩
    have hTα : InsideCircle T ABCD := inside_of_between (Or.inl hPα) (Or.inr hC) hPTC
    have hTD : SameSideOf T D A C :=
      SameSideOf.of_between_line ⟨M, hA_M, hC_M, hC_M⟩ hPD (between_symm hPTC)
    exact hnotB T hTD (hseg T hT_N hTα)
  obtain ⟨γ₀, hγ₀⟩ := exists_centre A
  refine ⟨⟨γ₀, hγ₀, fun P _ hP => ?_⟩, ?_⟩
  · obtain ⟨hPD, hPα⟩ := MixedAngle.region_ofSegment.1 hP
    exact ⟨hPD.trans hDF, (sameSideOf_congr_collinear hAB hAF.symm hFcol).2 (hside P hPD hPα)⟩
  · exact (near_across hE hBF.symm.triangle.bac (near_inside_of_ray hA (Or.inr hC) hAC)
      (fun P hP => outside_of_between (Or.inr hB) (fun h => inside_not_on h hA)
        (hP.between hBAF))).2.mono fun P hP =>
          ⟨hP.1, fun h' => hP.2.1 (MixedAngle.region_ofSegment.1 h').2⟩

/-- For a straight line AC in a circle about E that does not pass through the centre, the
diameter through C ends at a point B of the circle, other than A, on the centre's side of AC
(System E, Intersections 5 and Pasch 2). -/
theorem diameter_through {A C E : Point} {α : Circle} (hE : Centre E α)
    (hC : OnCircle C α) (hACE : ¬ Collinear A C E) :
    ∃ B : Point, OnCircle B α ∧ Between B E C ∧ A ≠ B ∧ SameSideOf E B A C := by
  have hCE : C ≠ E := ne_of_centre_of_on hE hC
  obtain ⟨L, hC_L, hE_L⟩ := Postulate1 C E hCE
  obtain ⟨B, hB, hB_L, hBEC⟩ := line_circle_beyond (centre_inside hE) hE_L hC_L hCE
  have hAB : A ≠ B := by
    rintro rfl
    exact hACE ⟨L, hB_L, hC_L, hE_L⟩
  have hACB : Triangle A C B := by
    rintro ⟨M, hA_M, hC_M, hB_M⟩
    have e : L = M := line_unique (ne_of_between_ends hBEC) hB_L hC_L hB_M hC_M
    exact hACE ⟨M, hA_M, hC_M, e ▸ hE_L⟩
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hACB.ne₁₂
  exact ⟨B, hB, hBEC, hAB,
    SameSideOf.of_between_line ⟨M, hA_M, hC_M, hC_M⟩ (sameSideOf_self hACB) (between_symm hBEC)⟩

/-- **III.31, for every straight line in a circle not through the centre.** At either end A of
such a straight line AC, the angle of the greater segment, the one on the centre's side,
exceeds every right angle CAR placed along AC on that side. (Euclid's figure, with B the far
end of the diameter through C: `greater_gt_right`, with III.31's first part.) -/
theorem any_greater_gt_right {A C E R : Point} {α : Circle} (hE : Centre E α)
    (hA : OnCircle A α) (hC : OnCircle C α) (hAC : A ≠ C) (hACE : ¬ Collinear A C E)
    (hR : SameSideOf R E A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C α E).Exceeds C R := by
  obtain ⟨B, hB, hBEC, hAB, hEB⟩ := diameter_through hE hC hACE
  have hBAC := (BookIII.Prop31 hE hA hB hC hBEC hAB hAC).1
  exact ⟨hR.triangle.bac, (locallyLess_congr (fun _ => Iff.rfl)
    (fun _ => MixedAngle.ofSegment_congr (OnRay.self hAC) hEB)).2
    (greater_gt_right hE hA hB hC hBEC hAB hAC hBAC (hR.trans hEB) hCAR).2⟩

/-- **III.31, the less segment, for every straight line in a circle not through the
centre.** At either end A of such a straight line AC, the angle of the less segment, on the
side away from the centre, comes as near A as we please and falls short of every right angle
CAR placed along AC on that side. -/
theorem any_less_lt_right {A C D E R : Point} {α : Circle} (hE : Centre E α)
    (hA : OnCircle A α) (hC : OnCircle C α) (hAC : A ≠ C) (hACE : ¬ Collinear A C E)
    (hED : OppositeSidesOf E D A C) (hR : SameSideOf R D A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C α D).FallsShort C R := by
  obtain ⟨B, hB, hBEC, hAB, hEB⟩ := diameter_through hE hC hACE
  exact less_lt_right hE hA hB hC hBEC hAB hAC (BookIII.Prop31 hE hA hB hC hBEC hAB hAC).1
    (hEB.symm.trans_opposite hED) hR hCAR

/-- **The angle of the greater segment as Euclid draws it.** A is on the circle, the ray AC
passes within it (between A and C), and B is off AC. -/
theorem greater_wellFormed {A B C E : Point} {ABCD : Circle}
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hBEC : Between B E C) (hAB : A ≠ B) (hAC : A ≠ C) :
    (MixedAngle.ofSegment A C ABCD B).WellFormed := by
  have hABC : Triangle A B C := Triangle.of_onCircle hA hB hC hAB (ne_of_between_ends hBEC) hAC
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  obtain ⟨X, -, hAXC, -⟩ := exists_point_between hA_L hC_L hAC []
  exact ⟨hA, ⟨X, OnRay.of_between hAXC, inside_of_between (Or.inr hA) (Or.inr hC) hAXC⟩,
    hABC.acb⟩

/-- **The angle of the less segment as Euclid draws it.** A is on the circle, the ray AC
passes within it, and D, across AC from B, is off AC. -/
theorem less_wellFormed {A B C D : Point} {ABCD : Circle}
    (hA : OnCircle A ABCD) (hC : OnCircle C ABCD) (hAC : A ≠ C)
    (hBD : OppositeSidesOf B D A C) : (MixedAngle.ofSegment A C ABCD D).WellFormed := by
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  obtain ⟨X, -, hAXC, -⟩ := exists_point_between hA_L hC_L hAC []
  exact ⟨hA, ⟨X, OnRay.of_between hAXC, inside_of_between (Or.inr hA) (Or.inr hC) hAXC⟩,
    hBD.symm.triangle⟩

end Prop31

end Elements.MixedAngles
