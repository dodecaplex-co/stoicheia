import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookI.Prop06
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop17
import Elements.BookI.Prop23
import Elements.BookI.Prop24
import Elements.BookIII.Prop02
import Elements.BookIII.Prop09

/-!
# Book III, Proposition 25

Euclid's text, in Heath's translation: [`heath/III/25.md`](../../heath/III/25.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- Given a segment of a circle, to describe the complete circle of which it is a segment. -/
theorem Prop25 {A C : Point} {ABC : Circle} (hABC : ∃ E : Point, Centre E ABC) (hA : OnCircle A ABC)
    (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  -- Let ABC be the given segment of a circle;
  intro P hP
  have hAC : A ≠ C := (show Triangle A C P from hP).ne₁₂
  -- thus it is required to describe the complete circle belonging to the segment ABC, that is,
  -- of which it is a segment.
  -- For let AC be bisected at D, let DB be drawn from the point D at right angles to AC, and
  -- let AB be joined;
  obtain ⟨D, hADC, hAD⟩ := BookI.Prop10 hAC
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  have hD_L : OnLine D L := on_line_of_between_ends hADC hA_L hC_L
  obtain ⟨X, hXP, hX⟩ := BookI.Prop11 hAC ⟨L, hA_L, hC_L, hD_L⟩ hP
  have hD_in : InsideCircle D ABC := Prop2 hABC hA hC D hADC
  have hX_L : ¬ OnLine X L := hXP.triangle.off_line hA_L hC_L
  have hDX : D ≠ X := fun e => hX_L (e ▸ hD_L)
  obtain ⟨N, hD_N, hX_N⟩ := Postulate1 D X hDX
  obtain ⟨Y, hY_N, hXDY, -⟩ := Postulate2 hX_N hD_N hDX.symm []
  obtain ⟨B, hB, hB_N, hBDY⟩ :=
    line_circle_beyond hD_in hD_N hY_N (ne_of_between (between_symm hXDY))
  have hBD : B ≠ D := fun e => inside_not_on hD_in (e ▸ hB)
  have hB_L : ¬ OnLine B L := fun hB_L =>
    hX_L ((line_unique hBD hB_N hD_N hB_L hD_L) ▸ hX_N)
  have hY_L : ¬ OnLine Y L := fun hY_L =>
    hX_L ((line_unique (ne_of_between (between_symm hXDY)) hY_N hD_N hY_L hD_L) ▸ hX_N)
  have hBX : SameSide B X L := same_side_of_opposite_sides
    ⟨hY_L, hB_L, fun h => pasch3 hBDY hD_L (same_side_symm h)⟩
    ⟨hY_L, hX_L, fun h => pasch3 hXDY hD_L (same_side_symm h)⟩
  have hBP : SameSideOf B P A C := (SameSideOf.of_line hAC hA_L hC_L hBX).trans hXP
  have hBray : OnRay B D X := OnRay.of_between_between (between_symm hXDY) (between_symm hBDY)
  have hAD' : A ≠ D := ne_of_between hADC
  have hCD' : C ≠ D := (ne_of_between (between_symm hADC))
  have hADB : ∠ A D B = ∟ := by
    rw [angle_onRay_right hBray hAD']
    exact hX A ⟨L, hA_L, hC_L, hA_L⟩ hAD'
  have hABD : Triangle A B D := (Triangle.of_line hA_L hD_L hAD' hB_L).acb
  have hAB : A ≠ B := hABD.ne₁₂
  have hBC : B ≠ C := fun e => hB_L (e ▸ hC_L)
  have hA_N : ¬ OnLine A N := fun hA_N => hB_L ((line_unique hAD' hA_N hD_N hA_L hD_L) ▸ hB_N)
  -- the angle ABD is then greater than, equal to, or less than the angle BAD.
  rcases lt_trichotomy (∠ B A D) (∠ A B D) with h | h | h
  -- First let it be greater;
  -- and on the straight line BA, and at the point A on it, let the angle BAE be constructed
  -- equal to the angle ABD; let DB be drawn through to E, and let EC be joined.
  · obtain ⟨G, F, hF, hGD, hGAF⟩ := BookI.Prop23 hAB hABD hABD
    have hGA : G ≠ A := hGD.triangle.ne₁₃.symm
    have hBAG : ∠ B A G = ∠ A B D :=
      (angle_onRay_left hF hGA).symm.trans ((angle_symm hF.2.1 hGA).trans hGAF)
    obtain ⟨M, hA_M, hB_M⟩ := Postulate1 A B hAB
    obtain ⟨K, hA_K, hG_K⟩ := Postulate1 A G hGA.symm
    /- Postulate 5 makes AG and DB produced meet, for the angles GAB, ABD are less than two
       right angles, ABD being less than a right angle [I. 17]. -/
    have hABD_lt : ∠ A B D < ∟ := by
      have h17 := (BookI.Prop17 hABD).1
      rw [angle_symm hBD hAD', hADB] at h17
      exact Magnitude.lt_of_add_lt_add_right h17
    obtain ⟨E, hE_K, hE_N, hEG⟩ := Postulate5 hG_K hA_K hA_M hB_M hB_N hD_N hAB
      (hGD.sameSide hA_M hB_M)
      (by rw [angle_symm hGA hAB.symm, hBAG]; exact Magnitude.add_self_lt_add_self hABD_lt)
    have hEG' : SameSideOf E G A B := SameSideOf.of_line hAB hA_M hB_M hEG
    have hED' : SameSideOf E D A B := hEG'.trans hGD
    have hEA : E ≠ A := hEG'.triangle.ne₁₃.symm
    have hEB : E ≠ B := hEG'.triangle.ne₂₃.symm
    have hEray : OnRay E A G := OnRay.of_sameSideOf hEG' ⟨K, hA_K, hG_K, hE_K⟩ hEA
    have hBAE : ∠ B A E = ∠ A B D := (angle_onRay_right hEray hAB.symm).trans hBAG
    have hEray' : OnRay E B D := OnRay.of_sameSideOf hED'.swap ⟨N, hB_N, hD_N, hE_N⟩ hEB
    /- E is beyond D: were it D, or between B and D, the angle BAE would not be greater than
       BAD. -/
    have hED : E ≠ D := fun e => by rw [e] at hBAE; rw [hBAE] at h; exact lt_irrefl _ h
    have hBDE : Between B D E := by
      rcases between_cases hBD hED.symm hEB.symm hB_N hD_N hE_N with h' | h' | h'
      · exact h'
      · exact absurd (between_symm h') hEray'.2.2.2
      · have hlt := angle_lt_of_between (V := A) (Triangle.of_line hD_N hB_N hBD.symm hA_N)
          (between_symm h')
        rw [angle_symm hEA hAB.symm, angle_symm hAD'.symm hAB.symm, hBAE] at hlt
        exact absurd (lt_trans hlt h) (lt_irrefl _)
    -- Then, since the angle ABE is equal to the angle BAE,
    have hABE : ∠ A B E = ∠ B A E := by
      rw [angle_onRay_right hEray' hAB, hBAE]
    -- the straight line EB is also equal to EA. [I. 6]
    have hEBA : Triangle E B A := (Triangle.of_line hB_N hE_N hEB.symm hA_N).bac
    have hEB_EA : ‖E B‖ = ‖E A‖ := BookI.Prop6 hEBA (by
      rw [angle_symm hEB hAB, hABE, angle_symm hAB.symm hEA])
    -- And, since AD is equal to DC,
    have hDA_DC : ‖D A‖ = ‖D C‖ := (len_symm D A).trans hAD
    -- and DE is common,
    have hDE : ‖D E‖ = ‖D E‖ := rfl
    -- the two sides AD, DE are equal to the two sides CD, DE respectively;
    -- and the angle ADE is equal to the angle CDE, for each is right;
    have hADE : ∠ A D E = ∟ := by
      rw [← adjacent_eq_of_right hB_N hE_N hBDE hA_N (by rw [angle_symm hBD hAD']; exact hADB),
        angle_symm hBD hAD', hADB]
    have hE_L : ¬ OnLine E L := fun hE_L =>
      hB_L ((line_unique hED hE_N hD_N hE_L hD_L) ▸ hB_N)
    have hCDE : ∠ C D E = ∟ := by
      rw [angle_symm hCD' hED, ← adjacent_eq_of_right hA_L hC_L hADC hE_L hADE, hADE]
    -- therefore the base AE is equal to the base CE.
    have hAE : ‖A E‖ = ‖C E‖ :=
      (BookI.Prop4 (Triangle.of_line hD_L hA_L hAD'.symm hE_L)
        (Triangle.of_line hD_L hC_L hCD'.symm hE_L) hDA_DC hDE
        (hADE.trans hCDE.symm)).1
    -- But AE was proved equal to BE;
    have h1 : ‖E A‖ = ‖E B‖ := hEB_EA.symm
    -- therefore BE is also equal to CE;
    have h2 : ‖E B‖ = ‖E C‖ := by rw [hEB_EA, len_symm E A, hAE, len_symm C E]
    -- therefore the three straight lines AE, EB, EC are equal to one another.
    -- Therefore the circle drawn with centre E and distance one of the straight lines AE, EB, EC
    -- will also pass through the remaining points and will have been completed. [III. 9]
    have hE : Centre E ABC := Prop9 hABC hA hB hC hAB hBC hAC h1 h2
    -- Therefore, given a segment of a circle, the complete circle has been described.
    -- And it is manifest that the segment ABC is less than a semicircle, because the centre E
    -- happens to be outside it.
    have hEB_AC : OppositeSidesOf E B A C :=
      OppositeSidesOf.of_line hAC hA_L hC_L ⟨hE_L, hB_L, pasch3 (between_symm hBDE) hD_L⟩
    exact ⟨B, D, E, hB, hBP, hADC, hAD, hADB, hE, ⟨N, hD_N, hB_N, hE_N⟩, fun _ => hEB_AC,
      fun h' => absurd (h'.symm ▸ h) (lt_irrefl _),
      fun h' => absurd (lt_trans h h') (lt_irrefl _)⟩
  -- Similarly, even if the angle ABD be equal to the angle BAD,
  -- AD being equal to each of the two BD, DC,
  · have hDA_DB : ‖D A‖ = ‖D B‖ := BookI.Prop6 (Triangle.of_line hD_L hA_L hAD'.symm hB_L) (by
      rw [angle_symm hAD'.symm hAB.symm, h, angle_symm hAB hBD.symm])
    -- the three straight lines DA, DB, DC will be equal to one another,
    have hDB_DC : ‖D B‖ = ‖D C‖ := by rw [← hDA_DB, len_symm D A, hAD]
    -- D will be the centre of the completed circle,
    have hD : Centre D ABC := Prop9 hABC hA hB hC hAB hBC hAC hDA_DB hDB_DC
    -- and ABC will clearly be a semicircle.
    exact ⟨B, D, D, hB, hBP, hADC, hAD, hADB, hD, ⟨N, hD_N, hB_N, hD_N⟩,
      fun h' => absurd (h ▸ h') (lt_irrefl _), fun _ => rfl,
      fun h' => absurd (h ▸ h') (lt_irrefl _)⟩
  -- But, if the angle ABD be less than the angle BAD,
  -- and if we construct, on the straight line BA and at the point A on it, an angle equal to
  -- the angle ABD, the centre will fall on DB within the segment ABC, and the segment ABC will
  -- clearly be greater than a semicircle.
  · obtain ⟨G, F, hF, hGD, hGAF⟩ := BookI.Prop23 hAB hABD hABD
    have hGA : G ≠ A := hGD.triangle.ne₁₃.symm
    have hBAG : ∠ B A G = ∠ A B D :=
      (angle_onRay_left hF hGA).symm.trans ((angle_symm hF.2.1 hGA).trans hGAF)
    /- The straight line AG falls within the angle BAD, and crosses BD at E. -/
    have hGB : SameSideOf G B A D := BookI.Prop24.within hGD.symm (by rw [hBAG]; exact h)
    obtain ⟨E, hBED, hEray⟩ := crossbar hGD hGB
    have hBAE : ∠ B A E = ∠ A B D := (angle_onRay_right hEray hAB.symm).trans hBAG
    have hE_N : OnLine E N := on_line_of_between_ends hBED hB_N hD_N
    have hED : E ≠ D := (ne_of_between (between_symm hBED)).symm
    have hEB : E ≠ B := (ne_of_between hBED).symm
    have hEA : E ≠ A := fun e => hA_N (e ▸ hE_N)
    /- As in the first case, EB is equal to EA [I. 6]. -/
    have hABE : ∠ A B E = ∠ B A E := by
      rw [angle_onRay_right (OnRay.of_between hBED) hAB, hBAE]
    have hEBA : Triangle E B A := (Triangle.of_line hB_N hE_N hEB.symm hA_N).bac
    have hEB_EA : ‖E B‖ = ‖E A‖ := BookI.Prop6 hEBA (by
      rw [angle_symm hEB hAB, hABE, angle_symm hAB.symm hEA])
    /- AE is equal to CE, for the angles at D are right [I. 4]. -/
    have hADE : ∠ A D E = ∟ := by
      rw [angle_onRay_right (OnRay.of_between (between_symm hBED)) hAD']; exact hADB
    have hE_L : ¬ OnLine E L := fun hE_L =>
      hB_L ((line_unique hED hE_N hD_N hE_L hD_L) ▸ hB_N)
    have hCDE : ∠ C D E = ∟ := by
      rw [angle_symm hCD' hED, ← adjacent_eq_of_right hA_L hC_L hADC hE_L hADE, hADE]
    have hAE : ‖A E‖ = ‖C E‖ :=
      (BookI.Prop4 (Triangle.of_line hD_L hA_L hAD'.symm hE_L)
        (Triangle.of_line hD_L hC_L hCD'.symm hE_L) (by rw [len_symm D A, hAD]) rfl
        (hADE.trans hCDE.symm)).1
    /- So the three straight lines AE, EB, EC are equal, and E is the centre [III. 9]. -/
    have h1 : ‖E A‖ = ‖E B‖ := hEB_EA.symm
    have h2 : ‖E B‖ = ‖E C‖ := by rw [hEB_EA, len_symm E A, hAE, len_symm C E]
    have hE : Centre E ABC := Prop9 hABC hA hB hC hAB hBC hAC h1 h2
    /- E lies between B and D, on B's side of AC, within the segment. -/
    have hEB_AC : SameSideOf E B A C :=
      SameSideOf.of_line hAC hA_L hC_L (pasch2 (between_symm hBED) hD_L hE_L)
    -- Therefore, given a segment of a circle, the complete circle has been described.
    exact ⟨B, D, E, hB, hBP, hADC, hAD, hADB, hE, ⟨N, hD_N, hB_N, hE_N⟩,
      fun h' => absurd (lt_trans h h') (lt_irrefl _),
      fun h' => absurd (h' ▸ h) (lt_irrefl _), fun _ => hEB_AC⟩
  -- Q. E. F.

end Elements.BookIII
