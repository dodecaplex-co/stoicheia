import Elements.Figure.Basics
import Elements.BookI.Prop05
import Elements.BookI.Helpers

/-!
# Book I, Proposition 7

Euclid's text, in Heath's translation: [`heath/I/07.md`](../../heath/I/07.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid draws one figure: the straight lines AD and CB cross, so that CB falls
within the angle ACD and DA within the angle CDB. The lemmas before the
theorem say what he reads off that figure, and settle the figures he does not draw.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- D is a different point from C, on the same side of AB and as far from A. Then
D is not on the straight line AC, so ACD really is a triangle. Heath: "The case in
which D falls on AC or BC does not require proof" (vol. 1, p. 260). On the ray from A
through C, the point D would make one length equal to itself with something added; on the
other ray, the straight line AB would separate C from D. -/
theorem Prop7.triangle {A B C D : Point} (hCD : SameSideOf C D A B) (hCA : ‖C A‖ = ‖D A‖)
    (hne : C ≠ D) : Triangle A C D := by
  rintro ⟨N, hA, hC, hD⟩
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hCD.1
  have hs : SameSide C D L := hCD.2 L hAL hBL
  have hAC : A ≠ C := fun h => not_on_line_of_same_side hs (h ▸ hAL)
  have hAD : A ≠ D := fun h => not_on_line_of_same_side (same_side_symm hs) (h ▸ hAL)
  have hAC_AD : ‖A C‖ = ‖A D‖ := by rw [len_symm A C, hCA, len_symm D A]
  rcases between_cases hAC hne hAD hA hC hD with h | h | h
  · have hsum := len_add_of_between h
    rw [← hAC_AD] at hsum
    have hlt := CommonNotion5 (a := ‖A C‖) (len_pos hne)
    rw [hsum] at hlt
    exact lt_irrefl _ hlt
  · exact pasch3 h hAL hs
  · have hsum := len_add_of_between h
    rw [hAC_AD] at hsum
    have hlt := CommonNotion5 (a := ‖A D‖) (len_pos hne.symm)
    rw [hsum] at hlt
    exact lt_irrefl _ hlt

/-- When D and A are on opposite sides of the straight line BC, the straight line AD
crosses BC at a point X on C's side of AB. Either X falls between B and C, and
the straight lines AD, CB cross as in Euclid's figure, or C falls between B and X,
and then C lies within the triangle ABD. -/
theorem Prop7.cross {A B C D : Point} {Q : Line} (hCD : SameSideOf C D A B)
    (hCA : ‖C A‖ = ‖D A‖) (hCB : ‖C B‖ = ‖D B‖) (hne : C ≠ D)
    (hBQ : OnLine B Q) (hCQ : OnLine C Q) (h : ¬ SameSide D A Q) :
    (∃ X : Point, Between A X D ∧ Between B X C) ∨ InsideTriangle C A B D := by
  have hACD : Triangle A C D := Prop7.triangle hCD hCA hne
  have hBCD : Triangle B C D := Prop7.triangle (SameSideOf.swap hCD) hCB hne
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hCD.1
  have hs : SameSide C D L := hCD.2 L hAL hBL
  obtain ⟨R, hAR, hDR⟩ := Postulate1 A D hACD.ne₁₃
  have hAQ : ¬ OnLine A Q := fun hA => not_on_line_of_same_side (hCD.2 Q hA hBQ) hCQ
  have hDQ : ¬ OnLine D Q := fun hD => hBCD ⟨Q, hBQ, hCQ, hD⟩
  obtain ⟨hQR, X, hXQ, hXR⟩ := lines_meet_of_opposite_sides ⟨hDQ, hAQ, h⟩ hDR hAR
  have hDXA : Between D X A :=
    pasch4 hQR hXQ hXR hDR hAR hACD.ne₁₃.symm (fun e => hDQ (e ▸ hXQ))
      (fun e => hAQ (e ▸ hXQ)) h
  have hAXD : Between A X D := between_symm hDXA
  have hXL : ¬ OnLine X L := fun hX =>
    not_on_line_of_same_side (same_side_symm hs)
      ((line_unique (ne_of_between hAXD) hAR hXR hAL hX) ▸ hDR)
  have hXC : SameSide X C L :=
    same_side_trans (same_side_symm (pasch2 hAXD hAL hXL)) (same_side_symm hs)
  have hCR : ¬ OnLine C R := fun hC => hACD ⟨R, hAR, hC, hDR⟩
  have hXC' : X ≠ C := fun e => hCR (e ▸ hXR)
  have hBX : B ≠ X := fun e => hXL (e ▸ hBL)
  rcases between_cases hBX hXC' hBCD.ne₁₂ hBQ hXQ hCQ with h' | h' | h'
  · exact Or.inl ⟨X, hAXD, h'⟩
  · exact absurd hXC (pasch3 h' hBL)
  · refine Or.inr ⟨⟨hBCD.ne₁₃, fun S hBS hDS => ?_⟩, ⟨hACD.ne₁₃.symm, fun R' hDR' hAR' => ?_⟩,
      hCD⟩
    · have hCS : ¬ OnLine C S := fun hC => hBCD ⟨S, hBS, hC, hDS⟩
      have hXS : ¬ OnLine X S := fun hX => by
        have hRS : R = S := line_unique (ne_of_between hDXA) hDR hXR hDS hX
        have hAS : OnLine A S := hRS ▸ hAR
        exact not_on_line_of_same_side (same_side_symm (hCD.2 S hAS hBS)) hDS
      exact same_side_trans (same_side_symm (pasch2 h' hBS hCS)) (pasch2 hDXA hDS hXS)
    · have hXR' : OnLine X R' := on_line_of_between_ends hAXD hAR' hDR'
      have hCR' : ¬ OnLine C R' := fun hC => hACD ⟨R', hAR', hC, hDR'⟩
      exact pasch2 (between_symm h') hXR' hCR'

/-- Where can D be? Either it falls within the triangle ABC, or C falls within the
triangle ABD, or the straight lines AD and CB cross (Euclid's figure), or AC and
DB cross (Euclid's figure with C and D exchanged). -/
theorem Prop7.cases {A B C D : Point} (hCD : SameSideOf C D A B) (hCA : ‖C A‖ = ‖D A‖)
    (hCB : ‖C B‖ = ‖D B‖) (hne : C ≠ D) :
    InsideTriangle D A B C ∨ InsideTriangle C A B D ∨
      (∃ X : Point, Between A X D ∧ Between B X C) ∨
      (∃ X : Point, Between A X C ∧ Between B X D) := by
  have hACD : Triangle A C D := Prop7.triangle hCD hCA hne
  have hBCD : Triangle B C D := Prop7.triangle (SameSideOf.swap hCD) hCB hne
  obtain ⟨P, hAP, hCP⟩ := Postulate1 A C hACD.ne₁₂
  obtain ⟨Q, hBQ, hCQ⟩ := Postulate1 B C hBCD.ne₁₂
  by_cases h₁ : SameSide D A Q
  · by_cases h₂ : SameSide D B P
    · refine Or.inl ⟨⟨hBCD.ne₁₂, fun Q' hBQ' hCQ' => ?_⟩,
        ⟨hACD.ne₁₂.symm, fun P' hCP' hAP' => ?_⟩, SameSideOf.symm hCD⟩
      · rw [← line_unique hBCD.ne₁₂ hBQ hCQ hBQ' hCQ']
        exact h₁
      · rw [← line_unique hACD.ne₁₂ hAP hCP hAP' hCP']
        exact h₂
    · rcases Prop7.cross (SameSideOf.swap hCD) hCB hCA hne hAP hCP h₂ with
        ⟨X, hBXD, hAXC⟩ | h
      · exact Or.inr (Or.inr (Or.inr ⟨X, hAXC, hBXD⟩))
      · exact Or.inr (Or.inl ⟨SameSideOf.swap h.2.1, SameSideOf.swap h.1,
          SameSideOf.swap h.2.2⟩)
  · rcases Prop7.cross hCD hCA hCB hne hBQ hCQ h₁ with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)

/-- Euclid's figure. When the straight lines AD and CB cross (at X), the straight line
CB falls within the angle ACD, and DA within the angle CDB. So each of those angles is
made up of two angles, and neither part is nothing. -/
theorem Prop7.figure {A B C D X : Point} (hCD : SameSideOf C D A B) (hCA : ‖C A‖ = ‖D A‖)
    (hCB : ‖C B‖ = ‖D B‖) (hne : C ≠ D) (hAXD : Between A X D) (hBXC : Between B X C) :
    ∠ A C D = ∠ A C B + ∠ B C D ∧ ∠ C D B = ∠ C D A + ∠ A D B ∧
      0 < ∠ A C B ∧ 0 < ∠ A D B := by
  have hACD : Triangle A C D := Prop7.triangle hCD hCA hne
  have hBCD : Triangle B C D := Prop7.triangle (SameSideOf.swap hCD) hCB hne
  obtain ⟨P, hAP, hCP⟩ := Postulate1 A C hACD.ne₁₂
  obtain ⟨Q, hBQ, hCQ⟩ := Postulate1 B C hBCD.ne₁₂
  obtain ⟨M, hCM, hDM⟩ := Postulate1 C D hne
  obtain ⟨R, hAR, hDR⟩ := Postulate1 A D hACD.ne₁₃
  obtain ⟨S, hBS, hDS⟩ := Postulate1 B D hBCD.ne₁₃
  have hXQ : OnLine X Q := on_line_of_between_ends hBXC hBQ hCQ
  have hXR : OnLine X R := on_line_of_between_ends hAXD hAR hDR
  /- First we say which points lie off which straight lines. -/
  have hAM : ¬ OnLine A M := fun h => hACD ⟨M, h, hCM, hDM⟩
  have hBP : ¬ OnLine B P := fun h => not_on_line_of_same_side (hCD.2 P hAP h) hCP
  have hDP : ¬ OnLine D P := fun h => hACD ⟨P, hAP, hCP, h⟩
  have hAS : ¬ OnLine A S := fun h =>
    not_on_line_of_same_side (same_side_symm (hCD.2 S h hBS)) hDS
  have hCS : ¬ OnLine C S := fun h => hBCD ⟨S, hBS, h, hDS⟩
  have hBR : ¬ OnLine B R := fun h =>
    not_on_line_of_same_side (same_side_symm (hCD.2 R hAR h)) hDR
  have hBM : ¬ OnLine B M := fun h => hBCD ⟨M, h, hCM, hDM⟩
  have hXM : ¬ OnLine X M := fun h =>
    hBCD ⟨Q, hBQ, hCQ, (line_unique (ne_of_between (between_symm hBXC)) hCQ hXQ hCM h) ▸ hDM⟩
  have hXP : ¬ OnLine X P := fun h =>
    hDP ((line_unique (ne_of_between hAXD) hAR hXR hAP h) ▸ hDR)
  have hXS : ¬ OnLine X S := fun h =>
    hAS ((line_unique (ne_of_between (between_symm hAXD)) hDR hXR hDS h) ▸ hAR)
  /- A and B are on the same side of CD, D and B of AC, and C and A of BD:
     each pair is joined to X without crossing the straight line. -/
  have hABM : SameSide A B M :=
    same_side_trans (pasch2 (between_symm hAXD) hDM hXM) (pasch2 (between_symm hBXC) hCM hXM)
  have hDBP : SameSide D B P :=
    same_side_trans (pasch2 hAXD hAP hXP) (pasch2 (between_symm hBXC) hCP hXP)
  have hCAS : SameSide C A S :=
    same_side_trans (pasch2 hBXC hBS hXS) (pasch2 (between_symm hAXD) hDS hXS)
  have hPM : P ≠ M := fun h => hDP (h ▸ hDM)
  have hMS : M ≠ S := fun h => hCS (h ▸ hCM)
  refine ⟨angle_add_of_inside hCP hCM hAP hDM hACD.ne₁₂.symm hne hBP hBM hPM hABM hDBP,
    angle_add_of_inside hDM hDS hCM hBS hne.symm hBCD.ne₁₃.symm hAM hAS hMS hCAS
      (same_side_symm hABM), ?_, ?_⟩
  · exact (Triangle.of_line hAP hCP hACD.ne₁₂ hBP).angle_pos
  · exact (Triangle.of_line hAR hDR hACD.ne₁₃ hBR).angle_pos

/-- The case Euclid leaves out, answered as Proclus answers it (Heath, vol. 1, p. 260). If
D falls within the triangle ABC, produce AC, AD to E, F. Since AC is equal to
AD, the angles ECD, FDC under the base of the triangle ACD are equal [I. 5]. But the
angle ECD is greater than the angle BCD, so the angle BDC is greater by far than the
angle BCD; and, since DB is equal to CB, it is also equal to it [I. 5]. -/
theorem Prop7.within {A B C D : Point} (hCD : SameSideOf C D A B) (hCA : ‖C A‖ = ‖D A‖)
    (hCB : ‖C B‖ = ‖D B‖) (hne : C ≠ D) (hD : InsideTriangle D A B C) : False := by
  have hACD : Triangle A C D := Prop7.triangle hCD hCA hne
  have hBCD : Triangle B C D := Prop7.triangle (SameSideOf.swap hCD) hCB hne
  obtain ⟨L, hAL, hBL⟩ := Postulate1 A B hCD.1
  obtain ⟨P, hAP, hCP⟩ := Postulate1 A C hACD.ne₁₂
  obtain ⟨Q, hBQ, hCQ⟩ := Postulate1 B C hBCD.ne₁₂
  obtain ⟨M, hCM, hDM⟩ := Postulate1 C D hne
  obtain ⟨R, hAR, hDR⟩ := Postulate1 A D hACD.ne₁₃
  obtain ⟨S, hBS, hDS⟩ := Postulate1 B D hBCD.ne₁₃
  have hDAQ : SameSide D A Q := hD.1.2 Q hBQ hCQ
  have hDBP : SameSide D B P := hD.2.1.2 P hCP hAP
  have hDCL : SameSide D C L := same_side_symm (hCD.2 L hAL hBL)
  /- We produce AC, AD to E and F. [Post. 2] -/
  obtain ⟨E, hEP, hACE, -⟩ := Postulate2 hAP hCP hACD.ne₁₂ []
  obtain ⟨F, hFR, hADF, -⟩ := Postulate2 hAR hDR hACD.ne₁₃ []
  have hEC : E ≠ C := ne_of_between (between_symm hACE)
  have hFD : F ≠ D := ne_of_between (between_symm hADF)
  /- First we say which points lie off which straight lines. -/
  have hAM : ¬ OnLine A M := fun h => hACD ⟨M, h, hCM, hDM⟩
  have hBM : ¬ OnLine B M := fun h => hBCD ⟨M, h, hCM, hDM⟩
  have hBP : ¬ OnLine B P := fun h => not_on_line_of_same_side (hCD.2 P hAP h) hCP
  have hDP : ¬ OnLine D P := fun h => hACD ⟨P, hAP, hCP, h⟩
  have hAS : ¬ OnLine A S := fun h =>
    not_on_line_of_same_side (same_side_symm (hCD.2 S h hBS)) hDS
  have hCS : ¬ OnLine C S := fun h => hBCD ⟨S, hBS, h, hDS⟩
  have hEM : ¬ OnLine E M := fun h => hDP ((line_unique hEC hEP hCP h hCM) ▸ hDM)
  have hFM : ¬ OnLine F M := fun h => hAM ((line_unique hFD hFR hDR h hDM) ▸ hAR)
  have hFS : ¬ OnLine F S := fun h => hAS ((line_unique hFD hFR hDR h hDS) ▸ hAR)
  /- With D within the angle ACB, the straight line CD separates A from B; with
     D within the angle ABC, the straight line BD separates A from C. (System E,
     Triple incidence 1.) -/
  have hABM : ¬ SameSide A B M :=
    triple_incidence1 hCP hCM hCQ hAP hDM hBQ hDBP (same_side_symm hDAQ)
  have hACS : ¬ SameSide A C S :=
    triple_incidence1 hBL hBS hBQ hAL hDS hCQ hDCL (same_side_symm hDAQ)
  /- So E, beyond C, is on B's side of CD; and F, beyond D, is on B's side of
     CD and on C's side of BD. -/
  have hEBM : SameSide E B M :=
    same_side_of_opposite_sides ⟨hAM, hEM, pasch3 hACE hCM⟩ ⟨hAM, hBM, hABM⟩
  have hBFM : SameSide B F M :=
    same_side_of_opposite_sides ⟨hAM, hBM, hABM⟩ ⟨hAM, hFM, pasch3 hADF hDM⟩
  have hCFS : SameSide C F S :=
    same_side_of_opposite_sides ⟨hAS, hCS, hACS⟩ ⟨hAS, hFS, pasch3 hADF hDS⟩
  have hPM : P ≠ M := fun h => hDP (h ▸ hDM)
  have hSM : S ≠ M := fun h => hCS (h ▸ hCM)
  /- CB falls within the angle ECD, and DF within the angle BDC. -/
  have hECD : ∠ E C D = ∠ E C B + ∠ B C D :=
    angle_add_of_inside hCP hCM hEP hDM hEC.symm hne hBP hBM hPM hEBM hDBP
  have hBDC : ∠ B D C = ∠ B D F + ∠ F D C :=
    angle_add_of_inside hDS hDM hBS hCM hBCD.ne₁₃.symm hne.symm hFS hFM hSM hBFM hCFS
  have hECB : 0 < ∠ E C B := (Triangle.of_line hEP hCP hEC hBP).angle_pos
  have hBDF : 0 < ∠ B D F := (Triangle.of_line hBS hDS hBCD.ne₁₃ hFS).angle_pos
  /- Since AC is equal to AD, the angles ECD, FDC under the base are equal. [I. 5] -/
  have hAC_AD : ‖A C‖ = ‖A D‖ := by rw [len_symm A C, hCA, len_symm D A]
  have hunder : ∠ D C E = ∠ C D F := (Prop5 hACD hAC_AD hACE hADF).2
  /- But the angle ECD is greater than the angle BCD; [C.N. 5] -/
  have h₁ : ∠ B C D < ∠ E C D := by
    rw [hECD, add_comm]
    exact CommonNotion5 hECB
  /- therefore the angle FDC is also greater than the angle BCD. -/
  have h₂ : ∠ B C D < ∠ F D C := by
    rw [← angle_symm hne hFD, ← hunder, ← angle_symm hEC hne.symm]
    exact h₁
  /- Therefore the angle BDC is greater by far than the angle BCD. [C.N. 5] -/
  have h₃ : ∠ B C D < ∠ B D C := by
    refine lt_trans h₂ ?_
    rw [hBDC, add_comm]
    exact CommonNotion5 hBDF
  /- Again, since DB is equal to CB, the angles at the base of the triangle BDC are equal:
     the angle BDC is equal to the angle BCD. [I. 5] -/
  have hBC_BD : ‖B C‖ = ‖B D‖ := by rw [len_symm B C, hCB, len_symm D B]
  have hbase : ∠ B C D = ∠ B D C := Prop5.base hBCD hBC_BD
  /- Therefore the same angle BDC is both greater than and equal to the angle BCD: which is
     impossible. -/
  rw [hbase] at h₃
  exact lt_irrefl _ h₃

/-- Given two straight lines constructed on a straight line (from its extremities) and meeting in a
point, there cannot be constructed on the same straight line (from its extremities), and on the
same side of it, two other straight lines meeting in another point and equal to the former two
respectively, namely each to that which has the same extremity with it. -/
theorem Prop7 {A B C D : Point} (hCD : SameSideOf C D A B) (hCA : ‖C A‖ = ‖D A‖)
    (hCB : ‖C B‖ = ‖D B‖) :
    C = D := by
  -- For, if possible, given two straight lines AC, CB constructed on the straight line AB and
  -- meeting at the point C, let two other straight lines AD, DB be constructed on the same
  -- straight line AB, on the same side of it, meeting in another point D and equal to the
  -- former two respectively, namely each to that which has the same extremity with it, so that
  -- CA is equal to DA which has the same extremity A with it, and CB to DB which has the same
  -- extremity B with it; and let CD be joined.
  apply Classical.byContradiction
  intro hne
  /- Euclid draws one figure, in which the straight lines AD and CB cross. Three others are
     possible (`Prop7.cases`). If AC and DB cross instead, it is Euclid's figure with the
     letters C and D exchanged, so we exchange them. If D falls within the triangle ABC, or C
     within the triangle ABD, Euclid's argument does not apply as it stands: that is the case
     Proclus answers with the second part of I. 5, proved in `Prop7.within`. From here on, C
     and D are named as in Euclid's figure, and X is the point where AD and CB cross.
     Our proof draws no straight line CD here: `Prop7.figure` draws its own. -/
  obtain ⟨C, D, hCD, hCA, hCB, hne, X, hAXD, hBXC⟩ :
      ∃ C D : Point, SameSideOf C D A B ∧ ‖C A‖ = ‖D A‖ ∧ ‖C B‖ = ‖D B‖ ∧ C ≠ D ∧
        ∃ X : Point, Between A X D ∧ Between B X C := by
    rcases Prop7.cases hCD hCA hCB hne with h | h | h | h
    · exact (Prop7.within hCD hCA hCB hne h).elim
    · exact (Prop7.within (SameSideOf.symm hCD) hCA.symm hCB.symm (Ne.symm hne) h).elim
    · exact ⟨C, D, hCD, hCA, hCB, hne, h⟩
    · exact ⟨D, C, SameSideOf.symm hCD, hCA.symm, hCB.symm, Ne.symm hne, h⟩
  have hACD : Triangle A C D := Prop7.triangle hCD hCA hne
  have hBCD : Triangle B C D := Prop7.triangle (SameSideOf.swap hCD) hCB hne
  -- Then, since AC is equal to AD,
  have hAC_AD : ‖A C‖ = ‖A D‖ := by rw [len_symm A C, hCA, len_symm D A]
  -- the angle ACD is also equal to the angle ADC; [I. 5]
  /- I.5 is stated with the equal sides produced, so `Prop5.base` produces AC, AD
     [Post. 2] and keeps only the angles at the base. -/
  have hACD_ADC : ∠ A C D = ∠ A D C := Prop5.base hACD hAC_AD
  -- therefore the angle ADC is greater than the angle DCB;
  /- Heath: "It would be natural to insert here the step 'but the angle ACD is greater than
     the angle BCD. [C. N. 5.]'" (vol. 1, p. 260). It rests on what the figure shows: CB
     falls within the angle ACD, so the angle ACD is made up of the angles ACB, BCD. -/
  obtain ⟨hACD_sum, hCDB_sum, hACB, hADB⟩ := Prop7.figure hCD hCA hCB hne hAXD hBXC
  have hDCB_ADC : ∠ D C B < ∠ A D C := by
    rw [← hACD_ADC, hACD_sum, angle_symm (Ne.symm hne) hBCD.ne₁₂, add_comm]
    exact CommonNotion5 hACB
  -- therefore the angle CDB is much greater than the angle DCB.
  /- DA falls within the angle CDB, so the angle CDB is greater than the angle CDA. [C.N. 5] -/
  have hDCB_CDB : ∠ D C B < ∠ C D B := by
    refine lt_trans hDCB_ADC ?_
    rw [hCDB_sum, angle_symm hACD.ne₁₃ hne]
    exact CommonNotion5 hADB
  -- Again, since CB is equal to DB,
  have hBC_BD : ‖B C‖ = ‖B D‖ := by rw [len_symm B C, hCB, len_symm D B]
  -- the angle CDB is also equal to the angle DCB.
  have hCDB_DCB : ∠ C D B = ∠ D C B := by
    rw [angle_symm hne hBCD.ne₁₃, ← Prop5.base hBCD hBC_BD, angle_symm hBCD.ne₁₂ (Ne.symm hne)]
  -- But it was also proved much greater than it:
  rw [hCDB_DCB] at hDCB_CDB
  -- which is impossible.
  exact lt_irrefl _ hDCB_CDB
  -- Therefore etc.
  -- Q. E. D.

/-- Two distinct common points of two distinct circles cannot lie on the same side of
the straight line through their centres (System E, Circle 4). We prove it from I.7,
Definition I.15 and `Tacit.circle_eq`. The centres differ, since circles with the same
centre and a common point coincide. The common points have equal distances from each
centre, so I.7 excludes their lying on the same side. -/
theorem _root_.Elements.Tacit.not_same_side_of_circles_meet
    {A B C D : Point} {L : Line} {α β : Circle}
    (hαβ : α ≠ β) (hCα : OnCircle C α) (hCβ : OnCircle C β)
    (hDα : OnCircle D α) (hDβ : OnCircle D β) (hCD : C ≠ D) (hA : Centre A α)
    (hB : Centre B β) (hAL : OnLine A L) (hBL : OnLine B L) : ¬ SameSide C D L := by
  intro hs
  have hAB : A ≠ B := by
    intro e
    subst B
    exact hαβ (circle_eq hA hB hCα hCβ rfl)
  apply hCD
  exact Prop7 (SameSideOf.of_line hAB hAL hBL hs)
    (by rw [len_symm C A, len_symm D A]; exact Definition15 hA hCα hDα)
    (by rw [len_symm C B, len_symm D B]; exact Definition15 hB hCβ hDβ)

end Elements.BookI
