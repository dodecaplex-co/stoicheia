import Elements
open Elements Elements.Tacit

namespace Scratch

open BookIII

/-- Halving keeps "less". -/
theorem half_lt {k : Kind} {a b : Magnitude k} (h : a + a < b + b) : a < b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · exact h'
  · subst h'; exact absurd h (lt_irrefl _)
  · exact absurd (lt_trans h (Magnitude.add_self_lt_add_self h')) (lt_irrefl _)

/-- The angle in a segment is acute, right or obtuse as the centre lies on its side of
the base, on the base, or beyond it. -/
theorem angle_type {X Y Z M : Point} {α : Circle} (hM : Centre M α) (hX : OnCircle X α)
    (hY : OnCircle Y α) (hZ : OnCircle Z α) (hXYZ : Triangle X Y Z) :
    (SameSideOf M Z X Y ∧ ∠ X Z Y < ∟) ∨ (Between X M Y ∧ ∠ X Z Y = ∟) ∨
      (OppositeSidesOf M Z X Y ∧ ∟ < ∠ X Z Y) := by
  obtain ⟨W, hW, hWZ⟩ := exists_onCircle_oppositeSidesOf hX hY hXYZ
  have hm : circumference α X W Y = ∠ X Z Y + ∠ X Z Y := Circumference.eq ⟨M, hM⟩ hZ hX hY hWZ.symm
  obtain ⟨L, hX_L, hY_L⟩ := Postulate1 X Y hXYZ.ne₁₂
  by_cases hM_L : OnLine M L
  · have hXMY := between_of_inside_chord hM_L hX_L hY_L (centre_inside hM) hX hY hXYZ.ne₁₂
    have hs := Circumference.semicircle hM hX hY hXMY hWZ.triangle
    rw [hm] at hs
    exact Or.inr (Or.inl ⟨hXMY, Magnitude.eq_of_add_self_eq hs⟩)
  by_cases hs : SameSide M Z L
  · have hMZ : SameSideOf M Z X Y := SameSideOf.of_line hXYZ.ne₁₂ hX_L hY_L hs
    have hlt := Circumference.lt_semicircle hM hX hY (hMZ.trans_opposite hWZ.symm)
    rw [hm] at hlt
    exact Or.inl ⟨hMZ, half_lt hlt⟩
  · have hMZ : OppositeSidesOf M Z X Y :=
      OppositeSidesOf.of_line hXYZ.ne₁₂ hX_L hY_L ⟨hM_L, hXYZ.off_line hX_L hY_L, hs⟩
    have hgt := Circumference.gt_semicircle hM hX hY (OppositeSidesOf.sameSideOf hMZ.symm hWZ.symm)
    rw [hm] at hgt
    exact Or.inr (Or.inr ⟨hMZ, half_lt hgt⟩)

/-- Isosceles triangles on equal bases with equal angles at the vertex have equal sides:
the angles at the base are equal [I. 5], and with the vertex make two right angles
[I. 32]; then angle, side, angle [I. 26]. -/
theorem iso {A B G C D H : Point} (hABG : Triangle A B G) (hCDH : Triangle C D H)
    (hG : ‖G A‖ = ‖G B‖) (hH : ‖H C‖ = ‖H D‖) (hAB : ‖A B‖ = ‖C D‖)
    (hang : ∠ A G B = ∠ C H D) : ‖G A‖ = ‖H C‖ := by
  have b₁ : ∠ G A B = ∠ G B A := BookI.Prop5.base hABG.cab hG
  have b₂ : ∠ H C D = ∠ H D C := BookI.Prop5.base hCDH.cab hH
  obtain ⟨P, hBGP⟩ := produce hABG.ne₂₃
  obtain ⟨-, s₁⟩ := BookI.Prop32 hABG hBGP
  obtain ⟨Q, hDHQ⟩ := produce hCDH.ne₂₃
  obtain ⟨-, s₂⟩ := BookI.Prop32 hCDH hDHQ
  have t₁ : ∠ G A B + ∠ G A B + ∠ A G B = ∟ + ∟ := by
    rw [← s₁, angle_symm hABG.ne₁₂ hABG.ne₂₃.symm, ← b₁, angle_symm hABG.ne₂₃ hABG.ne₁₃]
    ac_rfl
  have t₂ : ∠ H C D + ∠ H C D + ∠ C H D = ∟ + ∟ := by
    rw [← s₂, angle_symm hCDH.ne₁₂ hCDH.ne₂₃.symm, ← b₂, angle_symm hCDH.ne₂₃ hCDH.ne₁₃]
    ac_rfl
  have hA : ∠ G A B = ∠ H C D :=
    Magnitude.eq_of_add_self_eq (CommonNotion3 (by rw [t₁, t₂]) hang)
  have hB : ∠ A B G = ∠ C D H := by
    rw [angle_symm hABG.ne₁₂ hABG.ne₂₃.symm, ← b₁, hA, b₂, angle_symm hCDH.ne₂₃.symm hCDH.ne₁₂]
  exact (BookI.Prop26 hABG.cab hCDH.cab hA hB (Or.inl hAB)).1

/-- **III.24** without superposition: the circumferences by the measure; the radii by the
angles at the centres, which the equal angles in the segments make equal (III.20, with
III.22 for the other segment), and the isosceles triangles on the equal bases. -/
theorem T24 {A B C D E F : Point} {AEB CFD : Circle} (hAEB : ∃ O : Point, Centre O AEB)
    (hCFD : ∃ O : Point, Centre O CFD) (hA : OnCircle A AEB) (hB : OnCircle B AEB)
    (hE : OnCircle E AEB) (hC : OnCircle C CFD) (hD : OnCircle D CFD)
    (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E) (hF_CD : ¬ Collinear C D F)
    (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D := by
  obtain ⟨G, hG⟩ := hAEB
  obtain ⟨H, hH⟩ := hCFD
  have hABE : Triangle A B E := hE_AB
  have hCDF : Triangle C D F := hF_CD
  obtain ⟨X, hX, hXE⟩ := exists_onCircle_oppositeSidesOf hA hB hABE
  obtain ⟨Y, hY, hYF⟩ := exists_onCircle_oppositeSidesOf hC hD hCDF
  /- The other segments: the angles at `X`, `Y` make two right angles with those at `E`,
     `F` [III. 22]. -/
  have q₁ : ∠ A E B + ∠ A X B = ∟ + ∟ := by
    have := (BookIII.Prop22 ⟨G, hG⟩ hE hA hX hB hXE.symm).2
    rwa [angle_symm hXE.triangle.ne₂₃ hXE.triangle.ne₁₃] at this
  have q₂ : ∠ C F D + ∠ C Y D = ∟ + ∟ := by
    have := (BookIII.Prop22 ⟨H, hH⟩ hF hC hY hD hYF.symm).2
    rwa [angle_symm hYF.triangle.ne₂₃ hYF.triangle.ne₁₃] at this
  have hXY : ∠ A X B = ∠ C Y D := by
    apply CommonNotion3 (c := ∠ A E B) (d := ∠ C F D) _ hsim
    rw [add_comm (∠ A X B), q₁, add_comm (∠ C Y D), q₂]
  refine ⟨⟨G, H, A, C, hG, hH, hA, hC, ?_⟩, ?_⟩
  · have hGA : ‖G A‖ = ‖G B‖ := Definition15 hG hA hB
    have hHC : ‖H C‖ = ‖H D‖ := Definition15 hH hC hD
    /- The angles at the centres, when the centres are off the bases. -/
    have central : ∀ {P Q : Point}, OnCircle P AEB → OnCircle Q CFD → SameSideOf G P A B →
        SameSideOf H Q C D → ∠ A P B = ∠ C Q D → ‖G A‖ = ‖H C‖ := by
      intro P Q hP hQ hGP hHQ hPQ
      exact iso hGP.triangle hHQ.triangle hGA hHC hAB (by
        rw [Prop20 hG hP hA hB hGP, Prop20 hH hQ hC hD hHQ, hPQ])
    rcases angle_type hG hA hB hE hABE with ⟨hGE, hlt⟩ | ⟨hAGB, hrt⟩ | ⟨hGE, hgt⟩ <;>
      rcases angle_type hH hC hD hF hCDF with ⟨hHF, hlt'⟩ | ⟨hCHD, hrt'⟩ | ⟨hHF, hgt'⟩
    · exact central hE hF hGE hHF hsim
    · rw [hsim, hrt'] at hlt; exact absurd hlt (lt_irrefl _)
    · rw [hsim] at hlt; exact absurd (lt_trans hlt hgt') (lt_irrefl _)
    · rw [← hsim, hrt] at hlt'; exact absurd hlt' (lt_irrefl _)
    · /- Both bases are diameters. -/
      have d₁ : ‖A B‖ = ‖G A‖ + ‖G A‖ := by
        rw [← len_add_of_between hAGB, len_symm A G, ← hGA]
      have d₂ : ‖C D‖ = ‖H C‖ + ‖H C‖ := by
        rw [← len_add_of_between hCHD, len_symm C H, ← hHC]
      exact Magnitude.eq_of_add_self_eq (d₁.symm.trans (hAB.trans d₂))
    · rw [← hsim, hrt] at hgt'; exact absurd hgt' (lt_irrefl _)
    · rw [hsim] at hgt; exact absurd (lt_trans hlt' hgt) (lt_irrefl _)
    · rw [hsim, hrt'] at hgt; exact absurd hgt (lt_irrefl _)
    · exact central hX hY (OppositeSidesOf.sameSideOf hGE.symm hXE.symm)
        (OppositeSidesOf.sameSideOf hHF.symm hYF.symm) hXY
  · /- The circumferences: each with twice the angle in its segment is the whole. -/
    have w₁ := Circumference.whole ⟨G, hG⟩ hA hB hXE
    have w₂ := Circumference.whole ⟨H, hH⟩ hC hD hYF
    rw [Circumference.eq ⟨G, hG⟩ hE hA hB hXE.symm] at w₁
    rw [Circumference.eq ⟨H, hH⟩ hF hC hD hYF.symm, ← hsim] at w₂
    exact CommonNotion3 (w₁.trans w₂.symm) rfl

end Scratch
