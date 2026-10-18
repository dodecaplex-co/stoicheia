import Elements.Figure.Basics
import Elements.BookI.Prop12
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

* **Regions.** A region is a predicate on points. The region of the rectilineal angle `BAC`
  is `WithinAngle B A C`: the points on `C`'s side of `AB` and on `B`'s side of `AC`. The
  region of a mixed angle is `MixedAngle.region`.
* **Near the vertex.** "Near `A`" is said with a circle about `A`, as Euclid would draw it,
  and with no numbers: `LocallyWithin A R S` says that some circle about `A` holds no point
  of `R` outside `S`; `NearVertexOpen A R` says that every circle about `A`, however small,
  holds a point about which some circle holds only points of `R` (`Surrounds`).
* **Less.** `LocallyLess A R S`: near `A`, `R` lies within `S`, and the part of `S` outside
  `R` holds whole small circles as near `A` as we please. A straight ray that enters a
  circle soon leaves it again, so containment of whole regions would be the wrong
  comparison: only the neighbourhood of the vertex counts. Asking for whole circles, not
  single points, keeps an arm or a slit from counting as an excess: a line holds no circle
  (`not_locallyLess_arm`, `not_locallyLess_slit`).
* **Through the object.** `MixedAngle.Exceeds` and `MixedAngle.FallsShort` compare a mixed
  angle with a rectilineal angle placed at the mixed angle's own vertex.

Astra asked for checks on the interpretation before anything is called full, and they are
proved here in that order: (a) for rectilineal angles with a common arm the comparison is
the ordinary order of angles, and it is a strict order; (b) it does not depend on the points
that name the arms, equal angles placed on one side of one arm give one region, and the
angle of contact is the same, near its vertex, whatever straight line into the circle names
its branch; (c) the horn-like angle of III.16 is not empty: it holds whole small circles as
near its vertex as we please, though no straight ray from the vertex runs within it. Then
(d) the comparisons of III.16 and III.31 themselves, for every acute or right rectilineal
angle placed at the vertex, and Heath's "remaining angle" as what is left of the right angle.

Nothing here is used by `Elements/`; it is a prototype for the decision on issue #57, and
its account is `docs/reports/mixed-angles-prototype.md`.
-/

namespace Elements.MixedAngles

open Tacit

/-! ## The definitions -/

/-- **Within the angle `BAC`.** The region of the rectilineal angle `BAC`: the points on
`C`'s side of the straight line `AB` and on `B`'s side of the straight line `AC`. For a
true angle (`B`, `A`, `C` not on one straight line) it is the open region between the two
rays, which is less than two right angles; its arms are not in it. -/
def WithinAngle (B A C : Point) (P : Point) : Prop :=
  SameSideOf P C A B ∧ SameSideOf P B A C

/-- **A mixed angle**, an angle "contained by a straight line and a circumference"
(Definition III.7, and III.16). It is recorded by its vertex `A`, its straight
arm, the ray from `A` through a second point, its circle `α`, which passes through `A`,
and the branch and side of the circumference that bound it. Euclid uses two kinds, one for
each side of the circumference.

* `ofSegment A B α S`: **the angle of a segment** (Definition III.7), contained by the
  straight line `AB` and the circumference on `S`'s side of `AB`. Its straight arm is the
  ray from `A` through `B`; its branch is the one on `S`'s side; its side is within the
  circle. The region depends only on the straight line `AB`, so `B` may be any point of
  the ray: the other end of the chord, or, for the angle of the semicircle in III.16, a
  point of the diameter beyond the centre.
* `ofContact A E α B`: **the angle of contact**, contained by a straight line `AE` that
  touches `α` at `A` and the circumference: III.16's "remaining angle", the horn-like angle
  of Proclus. Its straight arm is the ray from `A` through `E`; its branch is the one on
  `E`'s side of a straight line `AB` that passes within the circle; its side is without
  the circle. Which such straight line names the branch does not matter near `A`
  (`Prop16.horn_locallyEqual`).

Nothing about the kinds is assumed when they are formed. The theorems that use them say
what the figure is: in III.16, `A` on the circle, `B` a point of the diameter through `A`
beyond the centre (the diameter produced if need be), and `AE` at right angles to `AB`,
which touches the circle by III.16's porism; in III.31, `A`, `B`, `C` on the circle. -/
inductive MixedAngle where
  | ofSegment (A B : Point) (α : Circle) (S : Point)
  | ofContact (A E : Point) (α : Circle) (B : Point)

namespace MixedAngle

/-- The vertex of a mixed angle: the point of the circle where its straight arm starts. -/
def vertex : MixedAngle → Point
  | ofSegment A _ _ _ => A
  | ofContact A _ _ _ => A

/-- **The region of a mixed angle.** For the angle of a segment, the points within the
circle on `S`'s side of `AB`: near `A` they lie between the ray `AB` and the branch of the
circumference on that side. For the angle of contact, the points without the circle and
within the angle `EAB`: near `A` they lie between the ray `AE` and the branch of the
circumference on `E`'s side. Far from `A` the regions run on (a segment is the whole of
it), but only their parts near the vertex enter a comparison. -/
def region : MixedAngle → Point → Prop
  | ofSegment A B α S => fun P => SameSideOf P S A B ∧ InsideCircle P α
  | ofContact A E α B => fun P => WithinAngle E A B P ∧ OutsideCircle P α

end MixedAngle

/-- **Near `A`, the region `R` lies within the region `S`.** Some circle about `A` holds
no point of `R` that is not a point of `S`. -/
def LocallyWithin (A : Point) (R S : Point → Prop) : Prop :=
  ∃ γ : Circle, Centre A γ ∧ ∀ P : Point, InsideCircle P γ → R P → S P

/-- **The region `R` comes as near `A` as we please.** Every circle about `A` holds a
point of `R`. -/
def NearVertex (A : Point) (R : Point → Prop) : Prop :=
  ∀ γ : Circle, Centre A γ → ∃ P : Point, InsideCircle P γ ∧ R P

/-- **The region `R` holds a whole circle about `P`.** Some circle about `P` holds only
points of `R`: `P` is a point of `R` and not on its edge. -/
def Surrounds (R : Point → Prop) (P : Point) : Prop :=
  ∃ δ : Circle, Centre P δ ∧ ∀ Q : Point, InsideCircle Q δ → R Q

/-- **The region `R` comes as near `A` as we please, and not by its edge alone.** Every
circle about `A` holds a point about which some circle holds only points of `R`. -/
def NearVertexOpen (A : Point) (R : Point → Prop) : Prop :=
  ∀ γ : Circle, Centre A γ → ∃ P : Point, InsideCircle P γ ∧ Surrounds R P

/-- **The angle with region `R` is less than the angle with region `S`, at `A`.** Near `A`,
`R` lies within `S`; and the points of `S` outside `R` hold whole small circles as near `A`
as we please. Points alone would not do: an arm or a slit, added to an angle, would then
count as an excess. -/
def LocallyLess (A : Point) (R S : Point → Prop) : Prop :=
  LocallyWithin A R S ∧ NearVertexOpen A (fun P => S P ∧ ¬ R P)

/-- **The angles with regions `R` and `S` are equal, at `A`.** Near `A`, each lies within
the other. -/
def LocallyEqual (A : Point) (R S : Point → Prop) : Prop :=
  LocallyWithin A R S ∧ LocallyWithin A S R

namespace MixedAngle

/-- **The mixed angle `m` is greater than the rectilineal angle `BXC`**, where `X` is the
vertex of `m`: placed at that vertex, the rectilineal angle is locally less than `m`. The
vertex is the mixed angle's own, so the comparison cannot be made at another point. -/
def Exceeds (m : MixedAngle) (B C : Point) : Prop :=
  LocallyLess m.vertex (WithinAngle B m.vertex C) m.region

/-- **The mixed angle `m` is less than the rectilineal angle `BXC`**, where `X` is the
vertex of `m`: `m` is locally less than the rectilineal angle placed at its vertex. -/
def FallsShort (m : MixedAngle) (B C : Point) : Prop :=
  LocallyLess m.vertex m.region (WithinAngle B m.vertex C)

end MixedAngle

/-! ## Small facts the checks need

These are Book Zero's kind of fact, proved from the foundations and Book Zero, with I.12,
I.17, I.19 and I.20 for the facts about circles about a point. -/

variable {A B C D E F P Q : Point} {α γ : Circle}

/-- A point off the straight line `AB` is on its own side of it. -/
theorem sameSideOf_self (h : Triangle A B C) : SameSideOf C C A B :=
  ⟨h.ne₁₂, fun _ hA hB => same_side_refl (h.off_line hA hB)⟩

/-- A point of the straight line `AB` (named as collinear with `A` and `B`) lies on every
straight line through `A` and `B`. -/
theorem onLine_of_collinear {L : Line} (hAB : A ≠ B) (h : Collinear A B C) (hA : OnLine A L)
    (hB : OnLine B L) : OnLine C L := by
  obtain ⟨M, hAM, hBM, hCM⟩ := h
  exact line_unique hAB hAM hBM hA hB ▸ hCM

/-- If `Y` is on the straight line `AX`, every point of the straight line `AX` is on the
straight line `AY`. -/
theorem collinear_of_collinear {X Y : Point} (hAX : A ≠ X) (hX : Collinear A X Y)
    (h : Collinear A X P) : Collinear A Y P := by
  obtain ⟨N, hA_N, hX_N, hP_N⟩ := h
  exact ⟨N, hA_N, onLine_of_collinear hAX hX hA_N hX_N, hP_N⟩

/-- The straight line `AB'`, for another point `B'` of the straight line `AB`, is the
straight line `AB`: sides of the one are sides of the other. -/
theorem sameSideOf_congr_collinear {B' : Point} (hAB : A ≠ B) (hB'A : B' ≠ A)
    (hcol : Collinear A B B') : SameSideOf P Q A B' ↔ SameSideOf P Q A B := by
  obtain ⟨L, hA, hB_L⟩ := Postulate1 A B hAB
  have hB'L : OnLine B' L := onLine_of_collinear hAB hcol hA hB_L
  exact ⟨fun h => SameSideOf.of_line hAB hA hB_L (h.sameSide hA hB'L),
    fun h => SameSideOf.of_line hB'A.symm hA hB'L (h.sameSide hA hB_L)⟩

/-- The straight line `AB'`, for `B'` on the ray from `A` through `B`, is the straight line
`AB`. -/
theorem sameSideOf_congr_line {B' : Point} (hB : OnRay B' A B) :
    SameSideOf P Q A B' ↔ SameSideOf P Q A B :=
  sameSideOf_congr_collinear hB.1 hB.2.1 hB.2.2.1

/-- `C`'s side of the straight line `AB` is the side of every point `C'` on the ray from
`A` through `C`. -/
theorem sameSideOf_congr_point {C' : Point} (hC : OnRay C' A C) :
    SameSideOf P C' A B ↔ SameSideOf P C A B := by
  constructor
  · intro h
    have hC' : SameSideOf C' C' A B := sameSideOf_self h.symm.triangle
    exact h.trans (SameSideOf.of_onRay hC.symm hC').symm
  · intro h
    have hC'' : SameSideOf C C A B := sameSideOf_self h.symm.triangle
    exact h.trans (SameSideOf.of_onRay hC hC'').symm

/-- Two points of one ray from `A`: the first is on the ray from `A` through the second. -/
theorem onRay_trans (hP : OnRay P A B) (hQ : OnRay Q A B) : OnRay P A Q := by
  obtain ⟨L, hA, hB, hPL⟩ := hP.2.2.1
  have hQL : OnLine Q L := hQ.onLine hA hB
  exact ⟨hQ.2.1.symm, hP.2.1, ⟨L, hA, hQL, hPL⟩, fun h => hP.not_between hQ h⟩

/-- A point between a point `Y` of the straight line `AB` and a point `W` on `Q`'s side of
it is on `Q`'s side too (System E, Pasch 2). -/
theorem sameSideOf_of_between {Y W : Point} (hY : Collinear A B Y) (hW : SameSideOf W Q A B)
    (h : Between Y P W) : SameSideOf P Q A B := by
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
  exact ⟨Y, onRay_trans (OnRay.of_between hAYG) hG.symm,
    inside_of_between (Or.inl (centre_inside hγ)) (Or.inr hGγ) hAYG⟩

/-- Of two circles about one point, one lies within the other: some circle about `A` holds
only points within both. -/
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

/-- **The perpendicular is the least straight line to a straight line.** If `N` is the foot
of the perpendicular from `A` to the straight line `BC`, every other point `X` of `BC` is
farther from `A`: the angle at `N` is right, so the angle at `X` is less [I. 17], and the
greater side is opposite it [I. 19]. -/
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
three points are not a triangle too: if `OP` and `PQ` together are less than a length `x`,
so is `OQ`. For a triangle this is I.20; for three points of one straight line, one lies
between the other two (System E, Between 6), and the whole is the sum of its parts or less
than it. -/
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
about it on the same side, within, or without. The radius is the distance to the foot of
the perpendicular [I. 12], or to the circumference along the straight line through the
centre; the other points are farther (`foot_nearest`, `len_lt_of_add_lt`). -/

/-- The common part of two regions holds a whole circle about `P` if each does. -/
theorem Surrounds.and {R S : Point → Prop} (hR : Surrounds R P) (hS : Surrounds S P) :
    Surrounds (fun Q => R Q ∧ S Q) P := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hR
  obtain ⟨δ₂, hδ₂, h₂⟩ := hS
  obtain ⟨δ, hδ, h⟩ := exists_inside_both hδ₁ hδ₂
  exact ⟨δ, hδ, fun Q hQ => ⟨h₁ Q (h Q hQ).1, h₂ Q (h Q hQ).2⟩⟩

/-- **A straight line holds no circle.** No circle about any point holds only points of the
straight line `AC`: the ray from its centre towards a point off `AC` has points within it
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

/-- **A point on one side of a straight line has a whole circle about it on that side.**
The circle about `P` through `N`, the foot of the perpendicular from `P` to `AB` [I. 12]:
a point within it nearer `P` than `N` is, on `AB` or beyond it, would put a point of `AB`
nearer `P` than `N` is (System E, Intersection 1), against `foot_nearest`. -/
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

/-- **A point within a circle has a whole circle about it within the circle.** If `P` is
not the centre `O`, the circle about `P` through `K`, where `OP` produced beyond `P` meets
the circumference (System E, Intersection 5): a point `Q` within it is nearer `O` than `K`
is, since `OQ` is less than `OP`, `PQ` together, and these less than `OP`, `PK` together,
which make `OK` (`len_lt_of_add_lt`). -/
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
about `P` through `K`, where the straight line from the centre `O` to `P` crosses the
circumference (System E, Intersection 4): were a point `Q` within it no farther from `O`
than `K` is, `OQ`, `QP` together would be less than `OK`, `KP` together, which make `OP`,
against `len_lt_of_add_lt`. -/
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

/-- Whole circles as near `A` as we please give points as near `A` as we please: the
centres. -/
theorem nearVertex {T : Point → Prop} (h : NearVertexOpen A T) : NearVertex A T := by
  intro γ hγ
  obtain ⟨P, hPγ, δ, hδ, hT⟩ := h γ hγ
  exact ⟨P, hPγ, hT P (centre_inside hδ)⟩

/-- For a region that holds a whole circle about each of its points, points as near `A` as
we please give whole circles as near `A` as we please. -/
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

/-- **Only the neighbourhood of `A` counts.** If, within some circle `γ₀` about `A`, the
points of `T` are points of `U`, then whole circles of `T` as near `A` as we please give
whole circles of `U`: each is shrunk to lie within `γ₀` (`surrounds_inside`). -/
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

/-- The region of the angle `BAC` is the region of the angle `CAB`. -/
theorem comm : WithinAngle B A C P ↔ WithinAngle C A B P :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **The naming points do not matter.** If `B'` is on the ray from `A` through `B`, and
`C'` on the ray from `A` through `C`, the angle `B'AC'` has the region of the angle
`BAC`. -/
theorem congr {B' C' : Point} (hB : OnRay B' A B) (hC : OnRay C' A C) :
    WithinAngle B' A C' P ↔ WithinAngle B A C P :=
  and_congr ((sameSideOf_congr_line hB).trans (sameSideOf_congr_point hC))
    ((sameSideOf_congr_line hC).trans (sameSideOf_congr_point hB))

/-- **Equal angles placed alike have one region.** If `D` and `C` are on the same side of
the straight line `AB`, and the angle `BAD` is equal to the angle `BAC`, the two angles
have one region: `D` is on the ray from `A` through `C` (`onRay_of_angle_eq`). -/
theorem eq_of_angle_eq (hDC : SameSideOf D C A B) (h : ∠ B A D = ∠ B A C) :
    WithinAngle B A D P ↔ WithinAngle B A C P :=
  congr (OnRay.self hDC.1) (onRay_of_angle_eq hDC h)

/-- A point within the angle `BAD`, where `D` is within the angle `BAC`, is within the
angle `BAC` (System E, Triple incidence 3). -/
theorem mono (hD : WithinAngle B A C D) (hP : WithinAngle B A D P) : WithinAngle B A C P := by
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

/-- A point within the angle `DAC`, where `D` is within the angle `BAC`, is within the
angle `BAC`. -/
theorem mono' (hD : WithinAngle B A C D) (hP : WithinAngle D A C P) : WithinAngle B A C P :=
  comm.2 (mono (comm.1 hD) (comm.1 hP))

/-- If `D` is within the angle `BAC`, the straight line `AD` separates `B` from `C`
(System E, Triple incidence 1). -/
theorem not_sameSideOf (hD : WithinAngle B A C D) : ¬ SameSideOf B C A D := by
  intro h
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hD.1.1
  obtain ⟨M, hA_M, hD_M⟩ := Postulate1 A D h.1
  obtain ⟨N, hA_N, hC_N⟩ := Postulate1 A C hD.2.1
  exact triple_incidence1 hA_L hA_M hA_N hB_L hD_M hC_N (hD.1.sameSide hA_L hB_L)
    (same_side_symm (hD.2.sameSide hA_N hC_N)) (h.sameSide hA_M hD_M)

/-- A point between a point of the ray `AU` and a point of the ray `AV` is within the angle
`UAV` (System E, Pasch 2). -/
theorem of_between {U V Y W : Point} (hUAV : Triangle U A V) (hY : OnRay Y A U)
    (hW : OnRay W A V) (h : Between Y P W) : WithinAngle U A V P :=
  ⟨sameSideOf_of_between hY.2.2.1 (SameSideOf.of_onRay hW (sameSideOf_self hUAV.bac)) h,
    sameSideOf_of_between hW.2.2.1 (SameSideOf.of_onRay hY (sameSideOf_self hUAV.bac.acb))
      (between_symm h)⟩

/-- Every circle about the vertex of an angle holds a point within the angle: take a point
of each arm within the circle, and a point between them. -/
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

/-- **The region of an angle has no edge points.** A point within the angle `BAC` has a
whole circle about it within the angle (`surrounds_sameSideOf`, twice). -/
theorem surrounds (h : WithinAngle B A C P) : Surrounds (WithinAngle B A C) P :=
  (surrounds_sameSideOf h.1).and (surrounds_sameSideOf h.2)

/-- Every circle about the vertex of an angle holds a whole circle within the angle. -/
theorem nearVertexOpen {U V : Point} (hUAV : Triangle U A V) :
    NearVertexOpen A (WithinAngle U A V) :=
  NearVertexOpen.of_nearVertex (fun _ hP => hP.surrounds) (fun _ hγ => exists_near hUAV hγ)

end WithinAngle

/-- On one side of the straight line `AB`, the less angle lies within the greater: if `D`
and `C` are on the same side of `AB`, and the angle `BAD` is less than the angle `BAC`, then
`D` is on `B`'s side of `AC`. Were `D` on `AC`, the angles would be equal; were it on the
other side, `C` would be within the angle `BAD` (System E, Triple incidence 2), and the
angle `BAC` a part of the angle `BAD` [C.N. 5]. -/
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

/-- If the angle with region `S` lies within the angle with region `R` near `A`, then `S`
cannot have points outside `R` as near `A` as we please. -/
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

/-- **The less angle is locally less.** If `D` and `C` are on the same side of `AB`, and
the angle `BAD` is less than the angle `BAC`, then near `A` the region of `BAD` lies within
that of `BAC` (indeed everywhere), and every circle about `A` holds a whole circle within
the angle `DAC`, which is within `BAC` and has no point within `BAD`. -/
theorem WithinAngle.locallyLess_of_lt (hDC : SameSideOf D C A B) (h : ∠ B A D < ∠ B A C) :
    LocallyLess A (WithinAngle B A D) (WithinAngle B A C) := by
  have hD : WithinAngle B A C D := ⟨hDC, sameSideOf_of_angle_lt hDC h⟩
  obtain ⟨γ₀, hγ₀⟩ := exists_centre A
  refine ⟨⟨γ₀, hγ₀, fun P _ hP => WithinAngle.mono hD hP⟩, ?_⟩
  exact (WithinAngle.nearVertexOpen hD.2.triangle.cab).mono fun P hP =>
    ⟨WithinAngle.mono' hD hP, fun h' => hD.not_sameSideOf (h'.2.symm.trans hP.1)⟩

/-- **Check (a), less.** For two rectilineal angles `BAD`, `BAC` with the common arm `AB`
and `D`, `C` on the same side of it, the angle `BAD` is locally less than the angle `BAC`
exactly when it is less as an angle. -/
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

/-- **Check (a), equal.** For two rectilineal angles `BAD`, `BAC` with the common arm `AB`
and `D`, `C` on the same side of it, the angles are locally equal exactly when they are
equal as angles. -/
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

/-- **Check (a), edges add nothing.** A true angle is not locally less than itself with one
arm added: the added points lie on a straight line, which holds no circle
(`Surrounds.not_line`). -/
theorem not_locallyLess_arm (h : Triangle B A C) :
    ¬ LocallyLess A (WithinAngle B A C) (fun P => WithinAngle B A C P ∨ OnRay P A C) := by
  intro hL
  obtain ⟨γ, hγ⟩ := exists_centre A
  obtain ⟨P, -, δ, hδ, hT⟩ := hL.2 γ hγ
  exact Surrounds.not_line h.ne₂₃ (P := P)
    ⟨δ, hδ, fun Q hQ => ((hT Q hQ).1.resolve_left (hT Q hQ).2).2.2.1⟩

/-- **Check (a), slits add nothing.** An angle with the ray `AD` taken out, for `D` within
it, is not locally less than the angle: what is taken out lies on a straight line. -/
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

/-- Near `A`, every region lies within itself. -/
theorem LocallyWithin.refl (A : Point) (R : Point → Prop) : LocallyWithin A R R := by
  obtain ⟨γ, hγ⟩ := exists_centre A
  exact ⟨γ, hγ, fun _ _ h => h⟩

/-- Lying within, near `A`, passes along. -/
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

/-- **Less than a less is less.** Near `A`, `R` lies within `S` and `S` within `T`; the
whole circles of `T` outside `S`, shrunk to the circle where `R` lies within `S`, are
outside `R` (`NearVertexOpen.mono_near`). -/
theorem LocallyLess.trans {R S T : Point → Prop} (h₁ : LocallyLess A R S)
    (h₂ : LocallyLess A S T) : LocallyLess A R T := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  obtain ⟨γ₁, hγ₁, f₁⟩ := h₁.1
  exact h₂.2.mono_near hγ₁ fun Q hQ hT => ⟨hT.1, fun hR => hT.2 (f₁ Q hQ hR)⟩

/-- **Equal angles compare alike, on the left.** If `R` and `R'` are locally equal, and `R`
is locally less than `S`, so is `R'`. -/
theorem LocallyLess.congr_left {R R' S : Point → Prop} (hE : LocallyEqual A R R')
    (h : LocallyLess A R S) : LocallyLess A R' S := by
  refine ⟨hE.2.trans h.1, ?_⟩
  obtain ⟨γ₁, hγ₁, f₁⟩ := hE.2
  exact h.2.mono_near hγ₁ fun Q hQ hT => ⟨hT.1, fun hR' => hT.2 (f₁ Q hQ hR')⟩

/-- **Equal angles compare alike, on the right.** If `S` and `S'` are locally equal, and `R`
is locally less than `S`, it is locally less than `S'`. -/
theorem LocallyLess.congr_right {R S S' : Point → Prop} (hE : LocallyEqual A S S')
    (h : LocallyLess A R S) : LocallyLess A R S' := by
  refine ⟨h.1.trans hE.1, ?_⟩
  obtain ⟨γ₁, hγ₁, f₁⟩ := hE.1
  exact h.2.mono_near hγ₁ fun Q hQ hT => ⟨f₁ Q hQ hT.1, hT.2⟩

/-! ## Check (b): the naming points do not matter -/

namespace MixedAngle

@[simp] theorem region_ofSegment {S : Point} :
    (ofSegment A B α S).region P ↔ SameSideOf P S A B ∧ InsideCircle P α := Iff.rfl

@[simp] theorem region_ofContact :
    (ofContact A E α B).region P ↔ WithinAngle E A B P ∧ OutsideCircle P α := Iff.rfl

/-- **Check (b), the angle of a segment.** Naming the straight arm by another point `B'` of
the ray `AB`, or the side by another point `S'` on `S`'s side, gives the same region. -/
theorem ofSegment_congr {B' S S' : Point} (hB : OnRay B' A B) (hS : SameSideOf S' S A B) :
    (ofSegment A B' α S').region P ↔ (ofSegment A B α S).region P := by
  simp only [region_ofSegment]
  exact and_congr
    ((sameSideOf_congr_line hB).trans ⟨fun h => h.trans hS, fun h => h.trans hS.symm⟩) Iff.rfl

/-- **Check (b), the angle of contact.** Naming the straight arm by another point `E'` of
the ray `AE`, or the branch by another point `B'` of the ray `AB`, gives the same region.
Another straight line into the circle gives the same angle near `A`
(`Prop16.horn_locallyEqual`). -/
theorem ofContact_congr {E' B' : Point} (hE : OnRay E' A E) (hB : OnRay B' A B) :
    (ofContact A E' α B').region P ↔ (ofContact A E α B).region P := by
  simp only [region_ofContact]
  exact and_congr (WithinAngle.congr hE hB) Iff.rfl

end MixedAngle

/-- **Check (b), placement.** Compared with any region `S`, a rectilineal angle placed
along `AB` depends only on its size: if `D` and `C` are on the same side of `AB` and the
angles `BAD`, `BAC` are equal, `BAD` is locally less than `S` exactly when `BAC` is, and
`S` locally less than `BAD` exactly when it is less than `BAC`. -/
theorem WithinAngle.locallyLess_placement {S : Point → Prop} (hDC : SameSideOf D C A B)
    (h : ∠ B A D = ∠ B A C) :
    (LocallyLess A (WithinAngle B A D) S ↔ LocallyLess A (WithinAngle B A C) S) ∧
      (LocallyLess A S (WithinAngle B A D) ↔ LocallyLess A S (WithinAngle B A C)) :=
  ⟨locallyLess_congr (fun _ => WithinAngle.eq_of_angle_eq hDC h) (fun _ => Iff.rfl),
    locallyLess_congr (fun _ => Iff.rfl) (fun _ => WithinAngle.eq_of_angle_eq hDC h)⟩

/-! ## Near the vertex, a rectilineal angle in a circle is within it -/

/-- **An angle between two chords lies within the circle near its vertex.** If `A`, `B`
and `C` are on or within the circle `α`, and `BAC` is a true angle, some circle about `A`
holds no point of the angle `BAC`, nor of its arms, that is not within `α`.

The circle about `A` passes through `N`, the foot of the perpendicular from `A` to `BC`
[I. 12]; every other point `X` of the straight line `BC` is farther from `A`
(`foot_nearest`). A point `P` of the angle within that circle lies on a ray from `A` that
crosses `BC` at some `X` (the crossbar, `crossbar`), nearer `A` than `X`, and so between `A`
and a point within `α` (System E, Circle 2). -/
theorem near_inside_of_angle (hA : InsideCircle A α ∨ OnCircle A α)
    (hB : InsideCircle B α ∨ OnCircle B α) (hC : InsideCircle C α ∨ OnCircle C α)
    (hBAC : Triangle B A C) :
    ∃ γ : Circle, Centre A γ ∧ ∀ P : Point, InsideCircle P γ →
      (WithinAngle B A C P ∨ OnRay P A B ∨ OnRay P A C) → InsideCircle P α := by
  have hBC : B ≠ C := hBAC.ne₁₃
  have hA_BC : ¬ Collinear B C A := fun ⟨L, h1, h2, h3⟩ => hBAC ⟨L, h1, h3, h2⟩
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

/-- **Points on either side of the circumference, near the vertex.** Let `UAV` be a true
angle, with the points of the ray `AU` near `A` within the circle `α`, and every point of
the ray `AV` without it. Then every circle about `A` holds a point within the angle `UAV`
and within `α`, and another within the angle and without `α`: on the straight line from a
point `Y` of `AU` to a point `W` of `AV`, both near `A`, on either side of the point where
it crosses the circumference (System E, Intersections 4, Circles 2 and 3). -/
theorem exists_near_across {U V : Point} (hUAV : Triangle U A V)
    (hU : ∃ γ₀ : Circle, Centre A γ₀ ∧
      ∀ P : Point, InsideCircle P γ₀ → OnRay P A U → InsideCircle P α)
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
`exists_near_across`, for a circle `α` about `O`, every circle about `A` holds a whole
circle within the angle `UAV` and within `α`, and another within the angle and without
`α` (`WithinAngle.surrounds`, `surrounds_inside`, `surrounds_outside`). -/
theorem near_across {O U V : Point} (hO : Centre O α) (hUAV : Triangle U A V)
    (hU : ∃ γ₀ : Circle, Centre A γ₀ ∧
      ∀ P : Point, InsideCircle P γ₀ → OnRay P A U → InsideCircle P α)
    (hV : ∀ P : Point, OnRay P A V → OutsideCircle P α) :
    NearVertexOpen A (fun P => WithinAngle U A V P ∧ InsideCircle P α) ∧
      NearVertexOpen A (fun P => WithinAngle U A V P ∧ OutsideCircle P α) :=
  ⟨NearVertexOpen.of_nearVertex (fun _ hP => hP.1.surrounds.and (surrounds_inside hO hP.2))
      (fun _ hγ => (exists_near_across hUAV hU hV hγ).1),
    NearVertexOpen.of_nearVertex (fun _ hP => hP.1.surrounds.and (surrounds_outside hO hP.2))
      (fun _ hγ => (exists_near_across hUAV hU hV hγ).2)⟩

/-- The points of a ray from a point `A` of a circle towards a point `B` on or within it,
near `A`, are within the circle: some circle about `A` holds no point of the ray that is
not between `A` and `B`. -/
theorem near_inside_of_ray (hA : OnCircle A α) (hB : InsideCircle B α ∨ OnCircle B α)
    (hAB : A ≠ B) :
    ∃ γ₀ : Circle, Centre A γ₀ ∧ ∀ P : Point, InsideCircle P γ₀ → OnRay P A B →
      InsideCircle P α := by
  obtain ⟨γ₀, hγ₀, hBγ₀⟩ := Postulate3 A B hAB
  exact ⟨γ₀, hγ₀, fun P hP hPB => inside_of_between (Or.inr hA) hB
    (OnRay.between_of_len_lt hPB (OnRay.self hAB) (len_lt_of_inside hγ₀ hBγ₀ hP))⟩

/-! ## Check (c) and the comparisons of III.16

Heath's letters: the circle `ABC` about `D` as centre, with `AB` a diameter, and `AE`
drawn from `A` at right angles to `AB`. The angle of the semicircle is
`MixedAngle.ofSegment A B ABC E`, contained by the straight line `BA` and the
circumference on `E`'s side, which is Heath's `CHA`; the remaining angle is
`MixedAngle.ofContact A E ABC B`, contained by that circumference and the straight line
`AE`.

The steps take III.16's two parts as hypotheses, `h1` (every point of `AE` but `A` is
without the circle) and `h2` (every other straight line through `A` falls within it), and
do not cite III.16. So a restatement of III.16 with the comparisons can prove its two parts
first and then these, in its own file, with the steps before it. The forms for any acute
angle at the end, which are companions, supply the parts from `BookIII.Prop16`. -/

namespace Prop16

/-- The points of the ray `AE` are without the circle: III.16's first part. -/
theorem outside_of_onRay {A E : Point} {ABC : Circle}
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC) :
    ∀ P : Point, OnRay P A E → OutsideCircle P ABC :=
  fun P hP => h1 P hP.2.2.1 hP.2.1

/-- The whole circle lies on `B`'s side of the straight line `AE`: a point within it on the
other side, or on `AE`, would put a point of `AE` within the circle, on the way to the
centre (System E, Intersection 1 and Circle 2), against III.16's first part. -/
theorem inside_sameSideOf {A B D E Q : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC)
    (hQ : InsideCircle Q ABC) : SameSideOf Q B A E := by
  have hABE : Triangle A B E := hE
  obtain ⟨L, hA_L, hE_L⟩ := Postulate1 A E hABE.ne₁₃
  have hoff : ∀ X : Point, InsideCircle X ABC → ¬ OnLine X L := fun X hX hX_L =>
    (h1 X ⟨L, hA_L, hE_L, hX_L⟩ (fun e => inside_not_on (e ▸ hX) hA)).1 hX
  have hDα : InsideCircle D ABC := centre_inside hD
  have hDB : SameSideOf D B A E :=
    SameSideOf.of_onRay (OnRay.of_between hADB) (sameSideOf_self hABE.acb)
  refine (SameSideOf.of_line hABE.ne₁₃ hA_L hE_L ?_).trans hDB
  refine Classical.byContradiction fun hs => ?_
  obtain ⟨X, hX_L, hQXD⟩ := OppositeSides.exists_between ⟨hoff Q hQ, hoff D hDα, hs⟩
  exact hoff X (inside_of_between (Or.inl hQ) (Or.inl hDα) hQXD) hX_L

/-- **No straight line between, near `A`.** For a point `F` within the angle `EAB`, some
circle about `A` holds no point within the angle `FAB`, nor on the ray `AF`, that is not
within the circle. This is III.16's second part made local: the straight line `AF` falls
within the circle at some `G` (on `F`'s side of `A`, since the circle lies on `B`'s side of
`AE`), and near `A` the angle `GAD` lies within the circle (`near_inside_of_angle`). -/
theorem near_inside {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC)
    (h2 : ∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC)
    (hF : WithinAngle E A B F) :
    ∃ γ : Circle, Centre A γ ∧ ∀ P : Point, InsideCircle P γ →
      (WithinAngle F A B P ∨ OnRay P A F) → InsideCircle P ABC := by
  obtain ⟨G, hG, hGα⟩ := h2 F hF.1.triangle
  have hGA : G ≠ A := fun e => inside_not_on (e ▸ hGα) hA
  have hGB : SameSideOf G B A E := inside_sameSideOf hD hA hADB hE h1 hGα
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
  · exact Or.inr (Or.inl (onRay_trans hR hGray))

/-- **Check (c): the horn-like angle is not nothing.** Every circle about `A`, however
small, holds a whole circle within the remaining angle of III.16: within the angle `EAB`
and without the circle. (Points of `AB` near `A` are within the circle, every point of `AE`
but `A` is without it, and the circumference crosses between them: `near_across`.) So the
upper bounds below are not satisfied by an empty region, nor by an edge. -/
theorem horn_nearVertex {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC) :
    NearVertexOpen A (MixedAngle.ofContact A E ABC B).region := by
  have hABE : Triangle A B E := hE
  have hDray : OnRay D A B := OnRay.of_between hADB
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside_of_ray hA (Or.inl (centre_inside hD)) hDray.2.1.symm
  exact (near_across hD hABE.bac ⟨γ₀, hγ₀, fun P hP hPB => hnear P hP (onRay_trans hPB hDray)⟩
    (outside_of_onRay h1)).2.mono fun P hP =>
      MixedAngle.region_ofContact.2 ⟨WithinAngle.comm.1 hP.1, hP.2⟩

/-- **Check (c): no straight ray runs within the horn.** For every point `F` within the
angle `EAB`, the points of the ray `AF` near `A` are not in the remaining angle: they are
within the circle. So the horn is not the region of any rectilineal angle, though it holds
whole circles as near `A` as we please (`horn_nearVertex`). -/
theorem horn_no_ray {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC)
    (h2 : ∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC)
    (hF : WithinAngle E A B F) :
    ∃ γ : Circle, Centre A γ ∧ ∀ P : Point, InsideCircle P γ → OnRay P A F →
      ¬ (MixedAngle.ofContact A E ABC B).region P := by
  obtain ⟨γ, hγ, hnear⟩ := near_inside hD hA hADB hE h1 h2 hF
  exact ⟨γ, hγ, fun P hPγ hPF hP =>
    (MixedAngle.region_ofContact.1 hP).2.1 (hnear P hPγ (Or.inr hPF))⟩

/-- **The horn lies within every angle `EAF` near `A`.** For a point `F` within the angle
`EAB`, near `A` a point of the remaining angle cannot be on `AF` or beyond it, for there the
points are within the circle (`near_inside`). -/
theorem horn_within {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC)
    (h2 : ∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC)
    (hFw : WithinAngle E A B F) :
    LocallyWithin A (MixedAngle.ofContact A E ABC B).region (WithinAngle E A F) := by
  have hF : SameSideOf F B A E := hFw.1
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE h1 h2 hFw
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

/-- **Check (b): the angle of contact does not depend on the straight line that names its
branch.** For any point `B'` on `B`'s side of `AE`, that is, any straight line `AB'` from
`A` into the circle, the angle of contact named by `B'` is locally equal to the one named by
the diameter. If `B'` is on the ray `AB`, the regions are the same (`ofContact_congr`). If
it is within the angle `EAB`, the one region lies within the other, and the rest, between
`AB'` and `AB`, is within the circle near `A` (`horn_within`). If it is on the other side of
`AB`, the same holds with `AE` produced beyond `A` to `E'`, which is at right angles to `AB`
as well: the rest, between `AB` and `AB'`, is within the circle near `A` (`near_inside`, for
`E'`). -/
theorem horn_locallyEqual {A B B' D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC)
    (h2 : ∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC)
    (hB' : SameSideOf B' B A E) :
    LocallyEqual A (MixedAngle.ofContact A E ABC B).region
      (MixedAngle.ofContact A E ABC B').region := by
  have hABE : Triangle A B E := hE
  have hAB : A ≠ B := hABE.ne₁₂
  have hAE : A ≠ E := hABE.ne₁₃
  have hB'A : B' ≠ A := hB'.triangle.ne₁₃.symm
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hE_L : ¬ OnLine E L := hABE.off_line hA_L hB_L
  by_cases hB'_L : OnLine B' L
  · /- `B'` on the ray `AB`. -/
    have hray : OnRay B' A B := OnRay.of_sameSideOf hB' ⟨L, hA_L, hB_L, hB'_L⟩ hB'A
    exact LocallyEqual.of_iff fun P =>
      (MixedAngle.ofContact_congr (P := P) (α := ABC) (OnRay.self hAE) hray).symm
  by_cases hs : SameSide B' E L
  · /- `B'` within the angle `EAB`. -/
    have hFw : WithinAngle E A B B' := ⟨hB', SameSideOf.of_line hAB hA_L hB_L hs⟩
    obtain ⟨γ₀, hγ₀⟩ := exists_centre A
    obtain ⟨γ, hγ, hW⟩ := horn_within hD hA hADB hE h1 h2 hFw
    exact ⟨⟨γ, hγ, fun P hPγ hP => MixedAngle.region_ofContact.2
        ⟨hW P hPγ hP, (MixedAngle.region_ofContact.1 hP).2⟩⟩,
      ⟨γ₀, hγ₀, fun P _ hP => MixedAngle.region_ofContact.2
        ⟨WithinAngle.mono hFw (MixedAngle.region_ofContact.1 hP).1,
          (MixedAngle.region_ofContact.1 hP).2⟩⟩⟩
  /- `B'` on the other side of `AB` from `E`: `AE` is produced beyond `A` to `E'`. -/
  have hopp : OppositeSidesOf B' E A B :=
    OppositeSidesOf.of_line hAB hA_L hB_L ⟨hB'_L, hE_L, hs⟩
  obtain ⟨E', hEAE'⟩ := produce hAE.symm
  have hEE' : OppositeSidesOf E E' A B := (OppositeSidesOf.of_between hABE.bac hEAE').swap
  have hB'E' : SameSideOf B' E' A B := OppositeSidesOf.sameSideOf hopp.symm hEE'
  have hABE' : ¬ Collinear A B E' := hB'E'.symm.triangle
  have hAE' : A ≠ E' := (ne_of_between (between_symm hEAE')).symm
  obtain ⟨M, hE_M, hA_M⟩ := Postulate1 E A hAE.symm
  have hE'_M : OnLine E' M := on_line_of_between hEAE' hE_M hA_M
  have hcol : Collinear A E E' := ⟨M, hA_M, hE_M, hE'_M⟩
  have hcol' : Collinear A E' E := ⟨M, hA_M, hE'_M, hE_M⟩
  /- III.16's two parts hold for `AE'`, which is the straight line `AE`. -/
  have h1' : ∀ P : Point, Collinear A E' P → P ≠ A → OutsideCircle P ABC :=
    fun P hP hPA => h1 P (collinear_of_collinear hAE' hcol' hP) hPA
  have h2' : ∀ F : Point, ¬ Collinear A E' F →
      ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC :=
    fun F hF => h2 F fun h => hF (collinear_of_collinear hAE hcol h)
  have hFw' : WithinAngle E' A B B' :=
    ⟨(sameSideOf_congr_collinear hAE hAE'.symm hcol).2 hB', hB'E'⟩
  obtain ⟨γ₁, hγ₁, hnear₁⟩ := near_inside hD hA hADB hABE' h1' h2' hFw'
  have hDray : OnRay D A B := OnRay.of_between hADB
  obtain ⟨γ₂, hγ₂, hnear₂⟩ := near_inside_of_ray hA (Or.inl (centre_inside hD)) hDray.2.1.symm
  obtain ⟨γ, hγ, hboth⟩ := exists_inside_both hγ₁ hγ₂
  /- `E` and `B` are on one side of `AB'`: `AB'` separates `E'` from `B`, and `E` from
     `E'`. -/
  have hAB'B : Triangle A B' B := by
    rintro ⟨N, hA_N, hB'_N, hB_N⟩
    exact hB'_L (onLine_of_collinear hAB ⟨N, hA_N, hB_N, hB'_N⟩ hA_L hB_L)
  have hEE'' : OppositeSidesOf E E' A B' :=
    (OppositeSidesOf.of_between hB'.triangle.cab hEAE').swap
  have hE'B : OppositeSidesOf E' B A B' := by
    obtain ⟨N, hA_N, hB'_N⟩ := Postulate1 A B' hB'A.symm
    exact OppositeSidesOf.of_line hB'A.symm hA_N hB'_N
      ⟨(hEE''.oppositeSides hA_N hB'_N).2.1, hAB'B.off_line hA_N hB'_N,
        fun h => hFw'.not_sameSideOf (SameSideOf.of_line hB'A.symm hA_N hB'_N h)⟩
  have hEB : SameSideOf E B A B' := OppositeSidesOf.sameSideOf hEE''.symm hE'B
  have hBin : WithinAngle E A B' B := ⟨hB'.symm, hEB.symm⟩
  refine ⟨⟨γ, hγ, fun P _ hP => ?_⟩, ⟨γ, hγ, fun P hPγ hP => ?_⟩⟩
  · obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
    exact MixedAngle.region_ofContact.2 ⟨WithinAngle.mono hBin hW, hout⟩
  · obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
    have hPB : SameSideOf P B A E := hW.1.trans hB'
    have hPA : P ≠ A := hW.1.triangle.ne₁₃.symm
    refine MixedAngle.region_ofContact.2 ⟨⟨hPB, ?_⟩, hout⟩
    by_cases hP_L : OnLine P L
    · exact absurd (hnear₂ P (hboth P hPγ).2
        (onRay_trans (OnRay.of_sameSideOf hPB ⟨L, hA_L, hB_L, hP_L⟩ hPA) hDray)) hout.1
    by_cases hsP : SameSide P E L
    · exact SameSideOf.of_line hAB hA_L hB_L hsP
    · exfalso
      have hPE : OppositeSidesOf E P A B :=
        OppositeSidesOf.of_line hAB hA_L hB_L ⟨hE_L, hP_L, fun h => hsP (same_side_symm h)⟩
      have hPB' : SameSideOf P B' A B := OppositeSidesOf.sameSideOf hPE hopp.symm
      exact hout.1 (hnear₁ P (hboth P hPγ).1 (Or.inl ⟨hW.2.trans hEB, hPB'⟩))

/-- **Heath's "remaining angle".** Within the right angle `BAE`, every point is in the angle
of the semicircle, or in the remaining angle, or on the circumference; and every point of
those is within the right angle. The three parts have no point in common, for no point is
both within and on a circle, and a point without it is neither (`OutsideCircle`). So the
remaining angle is what is left of the right angle `BAE` when the angle of the semicircle is
taken away, with the circumference between them. -/
theorem remaining {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC) (P : Point) :
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
      exact ⟨hPE, inside_sameSideOf hD hA hADB hE h1 hPα⟩
    · exact WithinAngle.comm.1 (MixedAngle.region_ofContact.1 h).1
    · exact h.2

/-- **III.16: the angle of the semicircle is greater than any acute rectilineal angle.**
For every point `F` on `E`'s side of the diameter `AB` with the angle `BAF` acute, the
angle of the semicircle exceeds the angle `BAF`: near `A` the angle `BAF` lies within the
circle (`near_inside`), and every circle about `A` holds whole circles within the circle
and within the angle `FAE`, which are in the semicircle's angle and not in `BAF`. -/
theorem semicircle_gt {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC)
    (h2 : ∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC)
    (hF : SameSideOf F E A B) (hBAF : ∠ B A F < ∟) :
    (MixedAngle.ofSegment A B ABC E).Exceeds B F := by
  show LocallyLess A (WithinAngle B A F) (MixedAngle.ofSegment A B ABC E).region
  have hlt : ∠ B A F < ∠ B A E := by rw [hBAE]; exact hBAF
  have hFw : WithinAngle E A B F := ⟨sameSideOf_of_angle_lt hF hlt, hF⟩
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE h1 h2 hFw
  refine ⟨⟨γ₀, hγ₀, fun P hPγ hP => MixedAngle.region_ofSegment.2
    ⟨hP.1.trans hF, hnear P hPγ (Or.inl (WithinAngle.comm.1 hP))⟩⟩, ?_⟩
  refine (near_across hD hFw.1.triangle.cab ⟨γ₀, hγ₀, fun P hP hPF => hnear P hP (Or.inr hPF)⟩
    (outside_of_onRay h1)).1.mono fun P hP => ?_
  obtain ⟨hPw, hPα⟩ := hP
  refine ⟨MixedAngle.region_ofSegment.2
    ⟨(WithinAngle.mono hFw (WithinAngle.comm.1 hPw)).2, hPα⟩, fun h' => ?_⟩
  exact hFw.not_sameSideOf (hPw.1.symm.trans h'.2)

/-- **III.16: the remaining angle is less than any acute rectilineal angle.** For every
point `F` on the circle's side of `AE` with the angle `EAF` acute, the remaining angle,
between `AE` and the circumference, falls short of the angle `EAF`: near `A` it lies within
the angle `EAF` (`horn_within`); and every circle about `A` holds whole circles within the
angle `EAF` and within the circle, which are not in the horn. -/
theorem horn_lt {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (hBAE : ∠ B A E = ∟)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC)
    (h2 : ∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC)
    (hF : SameSideOf F B A E) (hEAF : ∠ E A F < ∟) :
    (MixedAngle.ofContact A E ABC B).FallsShort E F := by
  show LocallyLess A (MixedAngle.ofContact A E ABC B).region (WithinAngle E A F)
  have hABE : Triangle A B E := hE
  have hlt : ∠ E A F < ∠ E A B := by
    rw [angle_symm hABE.ne₁₃.symm hABE.ne₁₂.symm, hBAE]; exact hEAF
  have hFw : WithinAngle E A B F := ⟨hF, sameSideOf_of_angle_lt hF hlt⟩
  refine ⟨horn_within hD hA hADB hE h1 h2 hFw, ?_⟩
  obtain ⟨γ₀, hγ₀, hnear⟩ := near_inside hD hA hADB hE h1 h2 hFw
  exact (near_across hD hFw.1.triangle.cab ⟨γ₀, hγ₀, fun P hP hPF => hnear P hP (Or.inr hPF)⟩
    (outside_of_onRay h1)).1.mono fun P hP =>
      ⟨WithinAngle.comm.1 hP.1, fun h' => (MixedAngle.region_ofContact.1 h').2.1 hP.2⟩

/-- **The angle of the semicircle is less than a right angle.** The angle of the semicircle
lies within the right angle `BAE` (the whole circle is on `B`'s side of `AE`), and every
circle about `A` holds whole circles of the horn, which are within `BAE` and not in the
semicircle's angle. With `semicircle_gt` and `LocallyLess.trans`, the angle of the
semicircle lies strictly between every acute angle and a right angle. -/
theorem semicircle_lt_right {A B D E : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hADB : Between A D B) (hE : ¬ Collinear A B E)
    (h1 : ∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC) :
    (MixedAngle.ofSegment A B ABC E).FallsShort B E := by
  show LocallyLess A (MixedAngle.ofSegment A B ABC E).region (WithinAngle B A E)
  obtain ⟨γ₀, hγ₀⟩ := exists_centre A
  refine ⟨⟨γ₀, hγ₀, fun P _ hP => ?_⟩, (horn_nearVertex hD hA hADB hE h1).mono fun P hP => ?_⟩
  · obtain ⟨hPE, hPα⟩ := MixedAngle.region_ofSegment.1 hP
    exact ⟨hPE, inside_sameSideOf hD hA hADB hE h1 hPα⟩
  · obtain ⟨hW, hout⟩ := MixedAngle.region_ofContact.1 hP
    exact ⟨WithinAngle.comm.1 hW, fun h' => hout.1 (MixedAngle.region_ofSegment.1 h').2⟩

/-- **III.16, for any acute rectilineal angle.** Every acute rectilineal angle `XYZ` can be
placed at `A` along `AB`, on `E`'s side [I. 23], and there the angle of the semicircle
exceeds it. (Placed so, it has one region whatever the placement:
`WithinAngle.locallyLess_placement`.) -/
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

/-- **III.16, the remaining angle, for any acute rectilineal angle.** Every acute
rectilineal angle `XYZ` can be placed at `A` along `AE`, towards the circle [I. 23], and
there the remaining angle falls short of it. -/
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

end Prop16

/-! ## The comparisons of III.31

Heath's letters: the circle `ABCD` with diameter `BC` and centre `E`, and `A` on it; `BA`
is carried through to `F`. The angle of the greater segment is
`MixedAngle.ofSegment A C ABCD B`, contained by the circumference `ABC` and the straight
line `AC`; the angle of the less segment is `MixedAngle.ofSegment A C ABCD D`, for a point
`D` on the other side of `AC`, contained by the circumference `ADC` and the straight line
`AC`. A right angle placed along `AC` on `B`'s side is the angle `CAB`, and on `D`'s side
the angle `CAF`.

The two steps take III.31's first part, that the angle `BAC` is right, as a hypothesis, and
do not cite III.31; the forms for any straight line in the circle, which are companions,
supply it from `BookIII.Prop31`. -/

namespace Prop31

/-- **III.31: the angle of the greater segment is greater than a right angle.** The angle of
the greater segment exceeds every right angle `CAR` placed along `AC` on `B`'s side. The
angle `CAR` is the angle `CAB` (the angle `BAC` is right, and on one side one ray makes a
given angle), which near `A` lies within the circle (`near_inside_of_angle`); and every
circle about `A` holds whole circles within the circle and within the angle between `AB`
and `CA` produced beyond `A`, which are in the greater segment's angle and not in `CAB`. -/
theorem greater_gt_right {A B C E R : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hBEC : Between B E C) (hAB : A ≠ B) (hAC : A ≠ C) (hBAC : ∠ B A C = ∟)
    (hR : SameSideOf R B A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C ABCD B).Exceeds C R := by
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
  /- `CA` produced beyond `A` to `C'`: its points are without the circle. -/
  obtain ⟨C', hCAC'⟩ := produce hAC.symm
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  have hC'_L : OnLine C' L := on_line_of_between hCAC' hC_L hA_L
  have hB_L : ¬ OnLine B L := hABC.acb.off_line hA_L hC_L
  have hBAC' : Triangle B A C' :=
    (Triangle.of_line hA_L hC'_L (ne_of_between (between_symm hCAC')).symm hB_L).cab
  obtain ⟨γ₁, hγ₁, hnear₁⟩ := near_inside_of_ray hA (Or.inr hB) hAB
  have hC'col : Collinear A C C' := ⟨L, hA_L, hC_L, hC'_L⟩
  have hopp : OppositeSidesOf C C' A B :=
    (OppositeSidesOf.of_between hABC.bac hCAC').swap
  obtain ⟨N, hA_N, hB_N⟩ := Postulate1 A B hAB
  refine (near_across hE hBAC' ⟨γ₁, hγ₁, hnear₁⟩
    (fun P hP => outside_of_between (Or.inr hC) (fun h => inside_not_on h hA)
      (hP.between hCAC'))).1.mono fun P hP => ?_
  obtain ⟨hPw, hPα⟩ := hP
  refine ⟨MixedAngle.region_ofSegment.2
    ⟨(sameSideOf_congr_collinear hAC hBAC'.ne₂₃.symm hC'col).1 hPw.2, hPα⟩, fun h' => ?_⟩
  exact ((hopp.oppositeSides hA_N hB_N).2.2)
    (same_side_trans (h'.2.sameSide hA_N hB_N) (hPw.1.sameSide hA_N hB_N))

/-- **III.31: the angle of the less segment is less than a right angle.** For a point `D`
on the other side of `AC` from `B`, the angle of the less segment falls short of every right
angle `CAR` placed along `AC` on `D`'s side. The angle `CAR` is the angle `CAF`, `BA` being
produced to `F`. The less segment lies wholly within the angle `CAF`: a point within the
circle on `F`'s side of `AC`, and on `AB` or beyond it, would give a point within the circle
on the straight line `AB` outside `AB` itself (System E, Circle 1, Pasch 2 and 3). And every
circle about `A` holds whole circles within the angle `CAF` and without the circle, which
are not in the less segment's angle. -/
theorem less_lt_right {A B C D E R : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hBEC : Between B E C) (hAB : A ≠ B) (hAC : A ≠ C) (hBAC : ∠ B A C = ∟)
    (hBD : OppositeSidesOf B D A C) (hR : SameSideOf R D A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C ABCD D).FallsShort C R := by
  show LocallyLess A (MixedAngle.ofSegment A C ABCD D).region (WithinAngle C A R)
  have hABC : Triangle A B C := Triangle.of_onCircle hA hB hC hAB (ne_of_between_ends hBEC) hAC
  obtain ⟨F, hBAF⟩ := produce hAB.symm
  obtain ⟨N, hA_N, hB_N⟩ := Postulate1 A B hAB
  have hF_N : OnLine F N := on_line_of_between hBAF hB_N hA_N
  have hC_N : ¬ OnLine C N := hABC.off_line hA_N hB_N
  have hAF : A ≠ F := ne_of_between (between_symm hBAF) |>.symm
  have hBF : OppositeSidesOf B F A C := (OppositeSidesOf.of_between hABC.cab hBAF).swap
  have hDF : SameSideOf D F A C := OppositeSidesOf.sameSideOf hBD hBF
  /- The angle `CAF` is right, as its adjacent angle `BAC` is (System E, Diagram-angle 3). -/
  have hCAF : ∠ C A F = ∟ := by
    rw [← (adjacent_eq_of_right hB_N hF_N hBAF hC_N hBAC), hBAC]
  have hRray : OnRay R A F := onRay_of_angle_eq (hR.trans hDF) (hCAR.trans hCAF.symm)
  refine (locallyLess_congr (fun _ => Iff.rfl)
    (fun P => WithinAngle.congr (OnRay.self hAC) hRray)).2 ?_
  have hFcol : Collinear A B F := ⟨N, hA_N, hB_N, hF_N⟩
  obtain ⟨M, hA_M, hC_M⟩ := Postulate1 A C hAC
  /- No point is on both `B`'s side and `D`'s side of `AC`. -/
  have hnotB : ∀ T : Point, SameSideOf T D A C → ¬ SameSideOf T B A C := fun T hTD hTB =>
    (hBD.oppositeSides hA_M hC_M).2.2 ((hTB.symm.trans hTD).sameSide hA_M hC_M)
  /- A point `T` within the circle on the straight line `AB` lies between `A` and `B`
     (System E, Circle 1), and so on `B`'s side of `AC` (Pasch 2). -/
  have hseg : ∀ T : Point, OnLine T N → InsideCircle T ABCD → SameSideOf T B A C :=
    fun T hT hTα => sameSideOf_of_between ⟨M, hA_M, hC_M, hA_M⟩ (sameSideOf_self hABC.acb)
      (between_of_inside_chord hT hA_N hB_N hTα hA hB hAB)
  /- So a point within the circle on `D`'s side of `AC` is on `C`'s side of `AB`: were it on
     `AB`, it would be on `B`'s side of `AC`; were it on the other side of `AB`, the straight
     line from it to `C` would cross `AB` within the circle (Intersection 1, Circle 2), at a
     point on `D`'s side of `AC` (Pasch 2). -/
  have hside : ∀ P : Point, SameSideOf P D A C → InsideCircle P ABCD → SameSideOf P C A B := by
    intro P hPD hPα
    by_cases hP_N : OnLine P N
    · exact absurd (hseg P hP_N hPα) (hnotB P hPD)
    refine SameSideOf.of_line hAB hA_N hB_N (Classical.byContradiction fun hs => ?_)
    obtain ⟨T, hT_N, hPTC⟩ := OppositeSides.exists_between ⟨hP_N, hC_N, hs⟩
    have hTα : InsideCircle T ABCD := inside_of_between (Or.inl hPα) (Or.inr hC) hPTC
    have hTD : SameSideOf T D A C :=
      sameSideOf_of_between ⟨M, hA_M, hC_M, hC_M⟩ hPD (between_symm hPTC)
    exact hnotB T hTD (hseg T hT_N hTα)
  obtain ⟨γ₀, hγ₀⟩ := exists_centre A
  refine ⟨⟨γ₀, hγ₀, fun P _ hP => ?_⟩, ?_⟩
  · obtain ⟨hPD, hPα⟩ := MixedAngle.region_ofSegment.1 hP
    exact ⟨hPD.trans hDF, (sameSideOf_congr_collinear hAB hAF.symm hFcol).2 (hside P hPD hPα)⟩
  · have hCAF' : Triangle C A F := hBF.symm.triangle.bac
    obtain ⟨γ₁, hγ₁, hnear₁⟩ := near_inside_of_ray hA (Or.inr hC) hAC
    exact (near_across hE hCAF' ⟨γ₁, hγ₁, hnear₁⟩
      (fun P hP => outside_of_between (Or.inr hB) (fun h => inside_not_on h hA)
        (hP.between hBAF))).2.mono fun P hP =>
          ⟨hP.1, fun h' => hP.2.1 (MixedAngle.region_ofSegment.1 h').2⟩

/-- For a straight line `AC` in a circle about `E` that does not pass through the centre,
the diameter through `C` ends at a point `B` of the circle, other than `A`, on the centre's
side of `AC` (System E, Intersections 5 and Pasch 2). -/
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
    sameSideOf_of_between ⟨M, hA_M, hC_M, hC_M⟩ (sameSideOf_self hACB) (between_symm hBEC)⟩

/-- **III.31, for every straight line in a circle not through the centre.** At either end
`A` of such a straight line `AC`, the angle of the greater segment, the one on the centre's
side, exceeds every right angle `CAR` placed along `AC` on that side. (Euclid's figure, with
`B` the far end of the diameter through `C`: `greater_gt_right`, with III.31's first part.)
-/
theorem chord_greater_gt_right {A C E R : Point} {α : Circle} (hE : Centre E α)
    (hA : OnCircle A α) (hC : OnCircle C α) (hAC : A ≠ C) (hACE : ¬ Collinear A C E)
    (hR : SameSideOf R E A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C α E).Exceeds C R := by
  show LocallyLess A (WithinAngle C A R) (MixedAngle.ofSegment A C α E).region
  obtain ⟨B, hB, hBEC, hAB, hEB⟩ := diameter_through hE hC hACE
  have hBAC := (BookIII.Prop31 hE hA hB hC hBEC hAB hAC).1
  exact (locallyLess_congr (fun _ => Iff.rfl)
    (fun _ => MixedAngle.ofSegment_congr (OnRay.self hAC) hEB)).2
    (greater_gt_right hE hA hB hC hBEC hAB hAC hBAC (hR.trans hEB) hCAR)

/-- **III.31, the less segment, for every straight line in a circle not through the
centre.** At either end `A` of such a straight line `AC`, the angle of the less segment,
on the side away from the centre, falls short of every right angle `CAR` placed along `AC`
on that side. -/
theorem chord_less_lt_right {A C D E R : Point} {α : Circle} (hE : Centre E α)
    (hA : OnCircle A α) (hC : OnCircle C α) (hAC : A ≠ C) (hACE : ¬ Collinear A C E)
    (hED : OppositeSidesOf E D A C) (hR : SameSideOf R D A C) (hCAR : ∠ C A R = ∟) :
    (MixedAngle.ofSegment A C α D).FallsShort C R := by
  obtain ⟨B, hB, hBEC, hAB, hEB⟩ := diameter_through hE hC hACE
  exact less_lt_right hE hA hB hC hBEC hAB hAC (BookIII.Prop31 hE hA hB hC hBEC hAB hAC).1
    (hEB.symm.trans_opposite hED) hR hCAR

end Prop31

end Elements.MixedAngles
