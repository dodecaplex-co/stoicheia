import Elements
open Elements Elements.Tacit

namespace Scratch

open BookIII

/-- Where the centre lies: on `C`'s side of `AB`, on `AB`, or on the other side. -/
theorem centre_cases {A B C K : Point} (hABC : Triangle A B C) :
    SameSideOf K C A B ∨ Collinear A B K ∨ OppositeSidesOf K C A B := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B hABC.ne₁₂
  have hC : ¬ OnLine C L := hABC.off_line hA hB
  by_cases hK : OnLine K L
  · exact Or.inr (Or.inl ⟨L, hA, hB, hK⟩)
  by_cases hs : SameSide K C L
  · exact Or.inl (SameSideOf.of_line hABC.ne₁₂ hA hB hs)
  · exact Or.inr (Or.inr (OppositeSidesOf.of_line hABC.ne₁₂ hA hB ⟨hK, hC, hs⟩))

/-- A straight line through the centre is a diameter, twice the radius. -/
theorem diam {A B K : Point} {α : Circle} (hK : Centre K α) (hA : OnCircle A α)
    (hB : OnCircle B α) (hAKB : Between A K B) : ‖A B‖ = ‖K A‖ + ‖K A‖ := by
  rw [← len_add_of_between hAKB, len_symm A K, Definition15 hK hB hA]

/-- In equal circles a straight line equal to a diameter of the one is a diameter of the
other: else it would be less than two radii [I. 20]. -/
theorem diam_of_eq {A B D E K L : Point} {α β : Circle} (hK : Centre K α) (hL : Centre L β)
    (hA : OnCircle A α) (hD : OnCircle D β) (hE : OnCircle E β) (hr : ‖K A‖ = ‖L D‖)
    (hAB : ‖A B‖ = ‖K A‖ + ‖K A‖) (hDE : ‖A B‖ = ‖D E‖) (hDE' : D ≠ E) : Between D L E := by
  by_cases hcol : Collinear D E L
  · obtain ⟨M, hD_M, hE_M, hL_M⟩ := hcol
    exact between_of_inside_chord hL_M hD_M hE_M (centre_inside hL) hD hE hDE'
  · have h20 := (BookI.Prop20 (show Triangle L D E from fun h => hcol (by
      obtain ⟨M, h1, h2, h3⟩ := h; exact ⟨M, h2, h3, h1⟩))).1
    rw [← hDE, hAB, len_symm D L, hr, Definition15 hL hE hD] at h20
    exact absurd h20 (lt_irrefl _)

/-- **III.26** by the measure (not Euclid's route, which goes by III.24). -/
theorem T26 {A B C D E F G H K L : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :
    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      circumference ABC B K C = circumference DEF E L F) ∧
    (∠ B A C = ∠ E D F → circumference ABC B K C = circumference DEF E L F) := by
  refine ⟨fun hGK hHL h => ?_, fun h => ?_⟩
  · rw [Circumference.centre hG hB hC hGK, Circumference.centre hH hE hF hHL, h]
  · rw [Circumference.eq ⟨G, hG⟩ hA hB hC hAK, Circumference.eq ⟨H, hH⟩ hD hE hF hDL, h]

/-- **III.27** by the measure. -/
theorem T27 {A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hBAC : Triangle B A C) (hEDF : Triangle E D F)
    (heq : standing ABC B A C = standing DEF E D F) :
    ∠ B A C = ∠ E D F ∧
      (SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F) := by
  rw [Circumference.standing ⟨G, hG⟩ hA hB hC hBAC.acb,
    Circumference.standing ⟨H, hH⟩ hD hE hF hEDF.acb] at heq
  have hA' : ∠ B A C = ∠ E D F := Magnitude.eq_of_add_self_eq heq
  refine ⟨hA', fun hGA hHD => ?_⟩
  rw [BookIII.Prop20 hG hA hB hC hGA, BookIII.Prop20 hH hD hE hF hHD, hA']

/-- **III.28** in full, by Euclid's route where the centres lie beyond the less
circumferences, with the case of diameters. -/
theorem T28 {A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hCG : OppositeSidesOf C G A B) (hFH : OppositeSidesOf F H D E) (hAB : ‖A B‖ = ‖D E‖)
    (hABC : circumference ABC A G B ≤ circumference ABC A C B)
    (hDEF : circumference DEF D H E ≤ circumference DEF D F E) :
    circumference ABC A C B = circumference DEF D F E ∧
      circumference ABC A G B = circumference DEF D H E := by
  obtain ⟨K, L, P, Q, hK, hL, hP, hQ, -⟩ := id hcircles
  have hr : ‖K A‖ = ‖L D‖ := hcircles.radii hK hL hA hD
  have hrB : ‖K B‖ = ‖L E‖ := hcircles.radii hK hL hB hE
  /- The two circumferences on each side make up the whole. -/
  have hw₁ := Circumference.whole ⟨K, hK⟩ hA hB hCG.symm
  have hw₂ := Circumference.whole ⟨L, hL⟩ hD hE hFH.symm
  /- The centre is not on the side of the less circumference. -/
  have not_near : ∀ {X Y P Q M : Point} {α : Circle}, Centre M α → OnCircle X α →
      OnCircle Y α → OppositeSidesOf P Q X Y →
      circumference α X Q Y ≤ circumference α X P Y → ¬ SameSideOf M Q X Y := by
    intro X Y P Q M α hM hX hY hPQ hle hMQ
    exact hle (lt_trans (Circumference.lt_semicircle hM hX hY (hMQ.trans_opposite hPQ.symm))
      (Circumference.gt_semicircle hM hX hY hMQ))
  have hAB' : A ≠ B := hCG.1
  have hDE' : D ≠ E := hFH.1
  have offAB : ∀ {M : Point}, Triangle A B M → ¬ Between A M B := fun h hb =>
    h (by obtain ⟨N, h1, h2, h3⟩ := collinear_of_between hb; exact ⟨N, h1, h3, h2⟩)
  rcases centre_cases (K := K) hCG.triangle with hKC | hKcol | hKC
  · /- `K` beyond the less circumference `AGB`: Euclid's figure. -/
    have hKG : OppositeSidesOf K G A B := hKC.trans_opposite hCG
    rcases centre_cases (K := L) hFH.triangle with hLF | hLcol | hLF
    · have hLH : OppositeSidesOf L H D E := hLF.trans_opposite hFH
      /- The angles at the centres are equal [I. 8], and so the less circumferences
         [III. 26]; the greater remain [C.N. 3]. -/
      have hAKB : ∠ A K B = ∠ D L E :=
        BookI.Prop8 hKG.triangle.cab hLH.triangle.cab hr hrB hAB
      have h₂ : circumference ABC A G B = circumference DEF D H E := by
        rw [Circumference.centre hK hA hB hKG, Circumference.centre hL hD hE hLH, hAKB]
      refine ⟨CommonNotion3 (hw₁.trans hw₂.symm) h₂, h₂⟩
    · /- `DE` a diameter: then so is `AB`, against `K` being off it. -/
      obtain ⟨M, hD_M, hE_M, hL_M⟩ := hLcol
      have hDLE := between_of_inside_chord hL_M hD_M hE_M (centre_inside hL) hD hE hDE'
      have hAKB := diam_of_eq hL hK hD hA hB hr.symm (diam hL hD hE hDLE) hAB.symm hAB'
      exact absurd hAKB (offAB hKC.triangle)
    · exact absurd (OppositeSidesOf.sameSideOf hLF.symm hFH) (not_near hL hD hE hFH hDEF)
  · /- `AB` a diameter, and so `DE`: four semicircles. -/
    obtain ⟨M, hA_M, hB_M, hK_M⟩ := hKcol
    have hAKB := between_of_inside_chord hK_M hA_M hB_M (centre_inside hK) hA hB hAB'
    have hDLE := diam_of_eq hK hL hA hD hE hr (diam hK hA hB hAKB) hAB hDE'
    rw [Circumference.semicircle hK hA hB hAKB hCG.symm.triangle,
      Circumference.semicircle hK hA hB hAKB hCG.triangle,
      Circumference.semicircle hL hD hE hDLE hFH.symm.triangle,
      Circumference.semicircle hL hD hE hDLE hFH.triangle]
    exact ⟨rfl, rfl⟩
  · exact absurd (OppositeSidesOf.sameSideOf hKC.symm hCG) (not_near hK hA hB hCG hABC)

/-- **III.29** in full: the angles at the centres, or the remaining circumferences, or
two diameters. -/
theorem T29 {B C E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hG : ¬ Collinear B C G) (hH : ¬ Collinear E F H)
    (heq : circumference ABC B G C = circumference DEF E H F) :
    ‖B C‖ = ‖E F‖ := by
  obtain ⟨K, L, P, Q, hK, hL, -, -, -⟩ := id hcircles
  have hr : ‖K B‖ = ‖L E‖ := hcircles.radii hK hL hB hE
  have hrC : ‖K C‖ = ‖L F‖ := hcircles.radii hK hL hC hF
  /- Equal circumferences beyond the centres: equal angles at the centres [III. 27],
     and equal bases [I. 4]. -/
  have minor : ∀ {X Y : Point}, OppositeSidesOf K X B C → OppositeSidesOf L Y E F →
      circumference ABC B X C = circumference DEF E Y F → ‖B C‖ = ‖E F‖ := by
    intro X Y hKX hLY h
    rw [Circumference.centre hK hB hC hKX, Circumference.centre hL hE hF hLY] at h
    exact (BookI.Prop4 hKX.triangle.cab hLY.triangle.cab hr hrC h).1
  have hGt : Triangle B C G := hG
  have hHt : Triangle E F H := hH
  /- A circumference less than, equal to, or greater than a semicircle, as the centre
     lies beyond it, on its base, or on its side. -/
  have size : ∀ {X Y Z M : Point} {α : Circle}, Centre M α → OnCircle X α → OnCircle Y α →
      Triangle X Y Z → (OppositeSidesOf M Z X Y ∧ circumference α X Z Y < ∟ + ∟) ∨
        (Between X M Y ∧ circumference α X Z Y = ∟ + ∟) ∨
        (SameSideOf M Z X Y ∧ ∟ + ∟ < circumference α X Z Y) := by
    intro X Y Z M α hM hX hY hXYZ
    rcases centre_cases (K := M) hXYZ with h | ⟨N, hX_N, hY_N, hM_N⟩ | h
    · exact Or.inr (Or.inr ⟨h, Circumference.gt_semicircle hM hX hY h⟩)
    · have hXMY := between_of_inside_chord hM_N hX_N hY_N (centre_inside hM) hX hY hXYZ.ne₁₂
      exact Or.inr (Or.inl ⟨hXMY, Circumference.semicircle hM hX hY hXMY hXYZ⟩)
    · exact Or.inl ⟨h, Circumference.lt_semicircle hM hX hY h⟩
  rcases size hK hB hC hGt with ⟨hKG, hlt⟩ | ⟨hBKC, heq₁⟩ | ⟨hKG, hgt⟩ <;>
    rcases size hL hE hF hHt with ⟨hLH, hlt'⟩ | ⟨hELF, heq₂⟩ | ⟨hLH, hgt'⟩
  · exact minor hKG hLH heq
  · rw [heq, heq₂] at hlt; exact absurd hlt (lt_irrefl _)
  · rw [heq] at hlt; exact absurd (lt_trans hlt hgt') (lt_irrefl _)
  · rw [heq] at heq₁; rw [heq₁] at hlt'; exact absurd hlt' (lt_irrefl _)
  · /- Two diameters of equal circles. -/
    rw [← len_add_of_between hBKC, ← len_add_of_between hELF, len_symm B K, hr, hrC,
      len_symm E L]
  · rw [heq] at heq₁; rw [heq₁] at hgt'; exact absurd hgt' (lt_irrefl _)
  · rw [heq] at hgt; exact absurd (lt_trans hlt' hgt) (lt_irrefl _)
  · rw [heq, heq₂] at hgt; exact absurd hgt (lt_irrefl _)
  · /- Both greater than semicircles: the remaining circumferences are equal. -/
    obtain ⟨X, hX, -⟩ := exists_oppositeSidesOf hGt []
    obtain ⟨Y, hY, -⟩ := exists_oppositeSidesOf hHt []
    have hw₁ := Circumference.whole ⟨K, hK⟩ hB hC hX
    have hw₂ := Circumference.whole ⟨L, hL⟩ hE hF hY
    rw [heq] at hw₁
    have hrest : circumference ABC B X C = circumference DEF E Y F := by
      apply CommonNotion3 (c := circumference DEF E H F) (d := circumference DEF E H F) _ rfl
      rw [add_comm (circumference ABC B X C), hw₁, add_comm (circumference DEF E Y F), hw₂]
    exact minor (hKG.trans_opposite hX.symm) (hLH.trans_opposite hY.symm) hrest

/-- **III.30** by the measure (not Euclid's route, which goes by III.28). -/
theorem T30 {A B : Point} {ADB : Circle} (hADB : ∃ O : Point, Centre O ADB) (hA : OnCircle A ADB)
    (hB : OnCircle B ADB) :
    ∀ P : Point, ¬ Collinear A B P → ∃ D : Point, OnCircle D ADB ∧ SameSideOf D P A B ∧
      standing ADB A B D = standing ADB D A B := by
  intro P hP
  have hAB : A ≠ B := (show Triangle A B P from hP).ne₁₂
  obtain ⟨C, hACB, hAC⟩ := BookI.Prop10 hAB
  obtain ⟨X, hXP, hX⟩ := BookI.Prop11 hAB (collinear_of_between hACB |> fun h => by
    obtain ⟨N, h1, h2, h3⟩ := h; exact ⟨N, h1, h3, h2⟩) hP
  /- `CX` meets the circle on `P`'s side. -/
  have hC_in : InsideCircle C ADB := inside_of_between (Or.inr hA) (Or.inr hB) hACB
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  have hC_L : OnLine C L := on_line_of_between_ends hACB hA_L hB_L
  have hX_L : ¬ OnLine X L := hXP.triangle.off_line hA_L hB_L
  have hCX : C ≠ X := fun e => hX_L (e ▸ hC_L)
  obtain ⟨N, hC_N, hX_N⟩ := Postulate1 C X hCX
  obtain ⟨Y, hY_N, hXCY, -⟩ := Postulate2 hX_N hC_N hCX.symm []
  obtain ⟨D, hD, hD_N, hDCY⟩ := line_circle_beyond hC_in hC_N hY_N (ne_of_between (between_symm hXCY))
  have hDC : D ≠ C := fun e => inside_not_on hC_in (e ▸ hD)
  have hD_L : ¬ OnLine D L := fun hD_L =>
    hX_L ((line_unique hDC hD_N hC_N hD_L hC_L) ▸ hX_N)
  have hY_L : ¬ OnLine Y L := fun hY_L =>
    hX_L ((line_unique (ne_of_between (between_symm hXCY)) hY_N hC_N hY_L hC_L) ▸ hX_N)
  have hDX : SameSide D X L := same_side_of_opposite_sides
    ⟨hY_L, hD_L, fun h => pasch3 hDCY hC_L (same_side_symm h)⟩
    ⟨hY_L, hX_L, fun h => pasch3 hXCY hC_L (same_side_symm h)⟩
  have hDP : SameSideOf D P A B := (SameSideOf.of_line hAB hA_L hB_L hDX).trans hXP
  refine ⟨D, hD, hDP, ?_⟩
  /- `AD` is equal to `DB` [I. 4], and the angles at `A`, `B` [I. 5]. -/
  have hDray : OnRay D C X := OnRay.of_between_between (between_symm hXCY) (between_symm hDCY)
  have hACD : ∠ A C D = ∟ := by
    rw [angle_onRay_right hDray (ne_of_between hACB)]
    exact hX A ⟨L, hA_L, hB_L, hA_L⟩ (ne_of_between hACB)
  have hBCD : ∠ B C D = ∟ := by
    rw [angle_onRay_right hDray (ne_of_between (between_symm hACB))]
    exact hX B ⟨L, hA_L, hB_L, hB_L⟩ (ne_of_between (between_symm hACB))
  have hCAD : Triangle C A D := Triangle.of_line hC_L hA_L (ne_of_between hACB).symm hD_L
  have hCBD : Triangle C B D := Triangle.of_line hC_L hB_L (ne_of_between (between_symm hACB)).symm hD_L
  have hAD : ‖A D‖ = ‖B D‖ := (BookI.Prop4 hCAD hCBD (by rw [len_symm C A, hAC]) rfl
    (hACD.trans hBCD.symm)).1
  have hABD : Triangle A B D := Triangle.of_line hA_L hB_L hAB hD_L
  rw [Circumference.standing hADB hB hA hD hABD.acb, Circumference.standing hADB hA hD hB hABD.cba,
    BookI.Prop5.base hABD.cab (by rw [len_symm D A, hAD, len_symm B D]),
    angle_symm hABD.ne₁₂ hABD.ne₂₃.symm]

end Scratch
