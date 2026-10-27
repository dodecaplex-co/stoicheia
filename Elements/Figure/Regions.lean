import Elements.Figure.OnCircles
import Elements.Figure.Rectangles

/-!
# Book Zero: angles as regions, and mixed angles near their vertex

III.16 and III.31 compare angles contained by a straight line and a circumference with
rectilineal angles. Their words are in `Foundations/DefinitionsIII.lean`: an angle is read
as the region it opens near its vertex (`WithinAngle`, `MixedAngle.region`), and two angles
at one vertex are compared by containment near it (`LocallyWithin`, `LocallyLess`), with
whole small circles of excess (`Surrounds`, `NearVertexOpen`). This file holds the facts
about them that cite no proposition:

* the sides of a straight line named by other points of it, and the points of one ray;
* circles about a point: every point is the centre of one, a ray from the centre has points
  within it, and of two circles about one point one lies within the other;
* the region of a rectilineal angle: it does not depend on the points that name its arms,
  equal angles placed alike have one region, the less angle on one side lies within the
  greater, and every circle about the vertex holds points of it;
* no angle is less than itself, and of two angles not each is less than the other; an arm
  or a slit adds or takes away nothing;
* the regions of a mixed angle, which do not depend on the points that name them, and what
  a comparison says of the angles it compares: they are something, and neither is
  straight.

The facts that need a proposition, the order of rectilineal angles among them, and that
comparisons chain (`LocallyLess.trans`, by I.20), are in `BookIII/MixedAngles.lean`.
Nothing here cites a proposition of the *Elements*, and nothing in it is an axiom.
-/

namespace Elements

open Tacit

variable {A B C D E F P Q : Point} {α γ : Circle}

/-! ## Sides, rays and straight lines -/

/-- A point off the straight line AB is on its own side of it. -/
theorem sameSideOf_self (h : Triangle A B C) : SameSideOf C C A B :=
  ⟨h.ne₁₂, fun _ hA hB => same_side_refl (h.off_line hA hB)⟩

/-- A point of the straight line AB, named as on one straight line with A and B, lies on
every straight line through A and B. -/
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
AB: its sides are the sides of AB. -/
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

/-- Across the straight line XY from a point W: a point Z off XY that is not on the side of
W's fellow V, which is on W's side, is on the other side from W. -/
theorem oppositeSidesOf_of_not_sameSideOf {X Y Z W V : Point} (hZ : Triangle X Y Z)
    (hWV : SameSideOf W V X Y) (hn : ¬ SameSideOf Z V X Y) : OppositeSidesOf Z W X Y := by
  obtain ⟨L, hX_L, hY_L⟩ := Postulate1 X Y hZ.ne₁₂
  exact OppositeSidesOf.of_line hZ.ne₁₂ hX_L hY_L ⟨hZ.off_line hX_L hY_L,
    not_on_line_of_same_side (hWV.sameSide hX_L hY_L),
    fun h => hn ((SameSideOf.of_line hZ.ne₁₂ hX_L hY_L h).trans hWV)⟩

/-! ## Circles about a point -/

/-- Every point is the centre of some circle [Post. 3]. -/
theorem exists_circle_about (A : Point) : ∃ γ : Circle, Centre A γ := by
  obtain ⟨B, hB⟩ := exists_point [A]
  have hAB : A ≠ B := fun h => hB (h ▸ List.mem_singleton_self A)
  obtain ⟨γ, hγ, -⟩ := Postulate3 A B hAB
  exact ⟨γ, hγ⟩

/-- Every ray from the centre of a circle has points within the circle: between the centre
and the point where the ray meets the circumference, which are nearer the centre than it. -/
theorem exists_onRay_inside (hγ : Centre A γ) (hAC : A ≠ C) :
    ∃ Y : Point, OnRay Y A C ∧ InsideCircle Y γ := by
  obtain ⟨K, hK, -⟩ := exists_point_on_circle γ []
  have hAK : A ≠ K := (ne_of_centre_of_on hγ hK).symm
  obtain ⟨G, hG, hAG⟩ := OnRay.exists_len_eq hAK hAC
  have hGγ : OnCircle G γ := on_circle_of_len_eq hγ hK hAG
  obtain ⟨L, hA, hG_L⟩ := Postulate1 A G hG.2.1.symm
  obtain ⟨Y, -, hAYG, -⟩ := exists_point_between hA hG_L hG.2.1.symm []
  exact ⟨Y, OnRay.of_sameRay (OnRay.of_between hAYG) hG.symm,
    inside_of_len_lt hγ hGγ (len_lt_of_between hAYG)⟩

/-- Of two circles about one point, one lies within the other: some circle about A holds
only points within both. -/
theorem exists_inside_both {γ₁ γ₂ : Circle} (hγ₁ : Centre A γ₁) (hγ₂ : Centre A γ₂) :
    ∃ γ : Circle, Centre A γ ∧
      ∀ P : Point, InsideCircle P γ → InsideCircle P γ₁ ∧ InsideCircle P γ₂ := by
  obtain ⟨K₁, hK₁, -⟩ := exists_point_on_circle γ₁ []
  obtain ⟨K₂, hK₂, -⟩ := exists_point_on_circle γ₂ []
  rcases lt_trichotomy ‖A K₁‖ ‖A K₂‖ with h | h | h
  · exact ⟨γ₁, hγ₁, fun P hP =>
      ⟨hP, inside_of_len_lt hγ₂ hK₂ (lt_trans (len_lt_of_inside hγ₁ hK₁ hP) h)⟩⟩
  · exact ⟨γ₁, hγ₁, fun P hP =>
      ⟨hP, inside_of_len_lt hγ₂ hK₂ (h ▸ len_lt_of_inside hγ₁ hK₁ hP)⟩⟩
  · exact ⟨γ₂, hγ₂, fun P hP =>
      ⟨inside_of_len_lt hγ₁ hK₁ (lt_trans (len_lt_of_inside hγ₂ hK₂ hP) h), hP⟩⟩

/-! ## Whole circles, and points near a vertex -/

/-- The common part of two regions holds a whole circle about P if each does. -/
theorem Surrounds.and {R S : Point → Prop} (hR : Surrounds R P) (hS : Surrounds S P) :
    Surrounds (fun Q => R Q ∧ S Q) P := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hR
  obtain ⟨δ₂, hδ₂, h₂⟩ := hS
  obtain ⟨δ, hδ, h⟩ := exists_inside_both hδ₁ hδ₂
  exact ⟨δ, hδ, fun Q hQ => ⟨h₁ Q (h Q hQ).1, h₂ Q (h Q hQ).2⟩⟩

/-- **A straight line holds no circle.** No circle about any point holds only points of the
straight line AC: the ray from its centre towards a point off AC has points within it. -/
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

namespace NearVertexOpen

/-- Whole circles as near A as we please give points as near A as we please: their
centres. -/
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
region: D is on the ray from A through C. -/
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

/-- A point of the ray from A through a point within the angle UAV is within it too. -/
theorem of_onRay {U V M : Point} (hM : WithinAngle U A V M) (hP : OnRay P A M) :
    WithinAngle U A V P :=
  ⟨SameSideOf.of_onRay hP hM.1, SameSideOf.of_onRay hP hM.2⟩

/-- Every circle about the vertex of an angle holds a point within the angle: on the ray
from the vertex through a point between the ends of the arms. -/
theorem exists_near {U V : Point} (hUAV : Triangle U A V) (hγ : Centre A γ) :
    ∃ P : Point, InsideCircle P γ ∧ WithinAngle U A V P := by
  obtain ⟨L, hU_L, hV_L⟩ := Postulate1 U V hUAV.ne₁₃
  obtain ⟨M, -, hUMV, -⟩ := exists_point_between hU_L hV_L hUAV.ne₁₃ []
  have hM : WithinAngle U A V M :=
    of_between hUAV (OnRay.self hUAV.ne₁₂.symm) (OnRay.self hUAV.ne₂₃) hUMV
  obtain ⟨P, hP, hPγ⟩ := exists_onRay_inside hγ hM.1.triangle.ne₁₃
  exact ⟨P, hPγ, of_onRay hM hP⟩

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
angle CAR is less than the angle CAT. -/
theorem WithinAngle.iff_angle_lt {R T : Point} (hRT : SameSideOf R T A C) :
    SameSideOf R C A T ↔ ∠ C A R < ∠ C A T := by
  constructor
  · intro hRC
    have hadd : ∠ C A T = ∠ C A R + ∠ R A T := angle_add_of_within hRT hRC
    have hlt := CommonNotion5 (a := ∠ C A R) hRC.triangle.cab.angle_pos
    rw [← hadd] at hlt
    exact hlt
  · exact sameSideOf_of_angle_lt hRT

/-- **The angle CAR holds CAT.** Let R and T be on one side of the
straight line AC, and R not on C's side of AT. Then R is on the ray AT, and the two angles
have one region; or R is across AT from C, the straight line RC crosses AT at a point X of
the ray AT within the angle CAR (System E, Intersection 1, Pasch 2), and the angle CAX lies
within the angle CAR. -/
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

/-! ## The comparison near a vertex -/

/-- If the region S lies within the region R near A, then S cannot have points outside
R as near A as we please. -/
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

/-- **Equal angles placed alike compare alike.** Compared with any region S, a rectilineal
angle placed along AB depends only on its size: if D and C are on the same side of AB and
the angles BAD, BAC are equal, BAD is locally less than S exactly when BAC is, and S
locally less than BAD exactly when it is less than BAC. -/
theorem WithinAngle.locallyLess_placement {S : Point → Prop} (hDC : SameSideOf D C A B)
    (h : ∠ B A D = ∠ B A C) :
    (LocallyLess A (WithinAngle B A D) S ↔ LocallyLess A (WithinAngle B A C) S) ∧
      (LocallyLess A S (WithinAngle B A D) ↔ LocallyLess A S (WithinAngle B A C)) :=
  ⟨locallyLess_congr (fun _ => WithinAngle.eq_of_angle_eq hDC h) (fun _ => Iff.rfl),
    locallyLess_congr (fun _ => Iff.rfl) (fun _ => WithinAngle.eq_of_angle_eq hDC h)⟩

/-- **An arm adds nothing.** A true angle is not locally less than itself with one arm added:
the added points lie on a straight line, which holds no circle. -/
theorem not_locallyLess_arm (h : Triangle B A C) :
    ¬ LocallyLess A (WithinAngle B A C) (fun P => WithinAngle B A C P ∨ OnRay P A C) := by
  intro hL
  obtain ⟨γ, hγ⟩ := exists_circle_about A
  obtain ⟨P, -, δ, hδ, hT⟩ := hL.2 γ hγ
  exact Surrounds.not_line h.ne₂₃ (P := P)
    ⟨δ, hδ, fun Q hQ => ((hT Q hQ).1.resolve_left (hT Q hQ).2).2.2.1⟩

/-- **A slit takes nothing away.** An angle with the ray AD taken out, for D within it, is
not locally less than the angle: what is taken out lies on a straight line. -/
theorem not_locallyLess_slit (hD : WithinAngle B A C D) :
    ¬ LocallyLess A (fun P => WithinAngle B A C P ∧ ¬ OnRay P A D) (WithinAngle B A C) := by
  intro hL
  obtain ⟨γ, hγ⟩ := exists_circle_about A
  obtain ⟨P, -, δ, hδ, hT⟩ := hL.2 γ hγ
  have hray : ∀ Q, InsideCircle Q δ → OnRay Q A D := fun Q hQ =>
    Classical.byContradiction fun hn => (hT Q hQ).2 ⟨(hT Q hQ).1, hn⟩
  exact Surrounds.not_line hD.1.triangle.ne₁₃ (P := P) ⟨δ, hδ, fun Q hQ => (hray Q hQ).2.2.1⟩

/-- Near A, every region lies within itself. -/
theorem LocallyWithin.refl (A : Point) (R : Point → Prop) : LocallyWithin A R R := by
  obtain ⟨γ, hγ⟩ := exists_circle_about A
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
  obtain ⟨γ, hγ⟩ := exists_circle_about A
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
  obtain ⟨γ, hγ⟩ := exists_circle_about A
  obtain ⟨P, -, hP, hn⟩ := h.2.nearVertex γ hγ
  exact hn hP

/-- Of two angles, not each is locally less than the other. -/
theorem LocallyLess.asymm {R S : Point → Prop} (h₁ : LocallyLess A R S)
    (h₂ : LocallyLess A S R) : False :=
  not_locallyWithin h₂.1 h₁.2.nearVertex

/-! ## Mixed angles -/

namespace MixedAngle

@[simp] theorem region_ofSegment {S : Point} :
    (ofSegment A B α S).region P ↔ SameSideOf P S A B ∧ InsideCircle P α := Iff.rfl

@[simp] theorem region_ofContact :
    (ofContact A E α B).region P ↔ WithinAngle E A B P ∧ OutsideCircle P α := Iff.rfl

/-- **The naming points of the angle of a segment do not matter.** Naming the straight arm
by another point B′ of the straight line AB, or the side by another point S′ on S's side,
gives the same region. A comparison still reads the ray from A through the naming point, so
it is B′ on the ray AB that names the same angle. -/
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
same region. -/
theorem ofContact_congr {E' B' : Point} (hE : OnRay E' A E) (hB : OnRay B' A B) :
    (ofContact A E' α B').region P ↔ (ofContact A E α B).region P := by
  simp only [region_ofContact]
  exact and_congr (WithinAngle.congr hE hB) Iff.rfl

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
  obtain ⟨γ, hγ⟩ := exists_circle_about m.vertex
  obtain ⟨P, -, hP, -⟩ := h.2.nearVertex γ hγ
  exact hP.1.symm.triangle.bac

end MixedAngle

end Elements
