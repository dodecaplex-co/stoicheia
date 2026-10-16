import Elements
open Elements Elements.Tacit

/-! The first steps of the statements not proved in full elsewhere: each is Book III's
statement word for word, with Euclid's first constructions carried out, and the rest left
(`sorry`). Where the proof is short it is finished. -/

namespace Scratch

open BookIII

/-- At a point `A`, only one straight line is at right angles to `AD`. -/
theorem one_perp {A D E F : Point} (hE : Triangle D A E) (hF : Triangle D A F)
    (hDAE : ∠ D A E = ∟) (hDAF : ∠ D A F = ∟) : Collinear A E F := by
  have hAD : A ≠ D := hE.ne₁₂.symm
  obtain ⟨L, hA_L, hD_L⟩ := Postulate1 A D hAD
  have hE_L : ¬ OnLine E L := hE.bac.off_line hA_L hD_L
  have hF_L : ¬ OnLine F L := hF.bac.off_line hA_L hD_L
  by_cases hs : SameSide F E L
  · exact (onRay_of_angle_eq (SameSideOf.of_line hAD hA_L hD_L hs) (hDAF.trans hDAE.symm)).2.2.1
  · obtain ⟨M, hE_M, hA_M⟩ := Postulate1 E A hE.ne₂₃.symm
    obtain ⟨E', hE'_M, hEAE', -⟩ := Postulate2 hE_M hA_M hE.ne₂₃.symm []
    have hD_M : ¬ OnLine D M := fun hD => hE ⟨M, hD, hA_M, hE_M⟩
    have hEAD : ∠ E A D = ∟ := by rw [angle_symm hE.ne₂₃.symm hE.ne₁₂]; exact hDAE
    have hDAE' : ∠ D A E' = ∟ := (adjacent_eq_of_right hE_M hE'_M hEAE' hD_M hEAD).symm.trans hEAD
    have hE'_L : ¬ OnLine E' L := fun h => hE_L (on_line_of_between (between_symm hEAE') h hA_L)
    have hFE' : SameSide F E' L := same_side_of_opposite_sides
      ⟨hE_L, hF_L, fun h => hs (same_side_symm h)⟩ ⟨hE_L, hE'_L, pasch3 hEAE' hA_L⟩
    obtain ⟨-, -, ⟨N, hA_N, hE'_N, hF_N⟩, -⟩ :=
      onRay_of_angle_eq (SameSideOf.of_line hAD hA_L hD_L hFE') (hDAF.trans hDAE'.symm)
    have hNM : N = M := line_unique (ne_of_between (between_symm hEAE')).symm hA_N hE'_N hA_M hE'_M
    subst hNM
    exact ⟨N, hA_N, hE_M, hF_N⟩


/-- III.2, its setting-out: the centre by III.1, the radii, the triangle `DAB`. -/
theorem T02 {A B : Point} {ABC : Circle} (hABC : ∃ D : Point, Centre D ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) :
    ∀ E : Point, Between A E B → InsideCircle E ABC := by
  intro E hAEB
  obtain ⟨D, -, -, -, hD, -⟩ := Prop1 hABC hA hB (ne_of_between_ends hAEB)
  have hDAB : ‖D A‖ = ‖D B‖ := Definition15 hD hA hB
  have _ := hDAB
  sorry

/-- III.3, the first part in full; the second part's setting-out. -/
theorem T03 {A B E F : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAFB : Between A F B) (hE_AB : ¬ Collinear A B E) :
    (‖A F‖ = ‖F B‖ → ∠ A F E = ∟ ∧ ∠ B F E = ∟) ∧ (∠ A F E = ∟ → ‖A F‖ = ‖F B‖) := by
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hAFB)
  have hF_L := on_line_of_between_ends hAFB hA_L hB_L
  have hE_L : ¬ OnLine E L := (show Triangle A B E from hE_AB).off_line hA_L hB_L
  have hFAE : Triangle F A E := Triangle.of_line hF_L hA_L (ne_of_between hAFB).symm hE_L
  have hFBE : Triangle F B E :=
    Triangle.of_line hF_L hB_L (ne_of_between (between_symm hAFB)).symm hE_L
  have hEA : ‖E A‖ = ‖E B‖ := Definition15 hE hA hB
  refine ⟨fun hAF => ?_, fun hAFE => ?_⟩
  · /- I. 8, then I. Def. 10. -/
    have h8 : ∠ A F E = ∠ B F E := BookI.Prop8 hFAE hFBE (by rw [len_symm F A, hAF]) rfl
      (by rw [len_symm A E, len_symm B E, hEA])
    have hr : ∠ A F E = ∟ := Postulate4
      ⟨B, hAFB, hFAE.bac, h8.trans (angle_symm hFBE.ne₁₂.symm hFBE.ne₁₃.symm)⟩
    exact ⟨hr, h8 ▸ hr⟩
  · /- I. 5, then I. 26. -/
    have h5 : ∠ E A B = ∠ E B A := BookI.Prop5.base hFAE.cab.acb.bca |> fun _ =>
      BookI.Prop5.base (Triangle.of_line hA_L hB_L (ne_of_between_ends hAFB) hE_L).cab hEA
    have _ := h5
    sorry

/-- III.4, its first steps: the centre by III.1, and III.3 for `AC`. -/
theorem T04 {A B C D E : Point} {ABCD : Circle} (hABCD : ∃ F : Point, Centre F ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hD : OnCircle D ABCD) (hAEC : Between A E C) (hBED : Between B E D)
    (hB_AC : ¬ Collinear A C B) (hAC : ∀ F : Point, Centre F ABCD → ¬ Collinear A C F)
    (hBD : ∀ F : Point, Centre F ABCD → ¬ Collinear B D F) :
    ¬ (‖A E‖ = ‖E C‖ ∧ ‖B E‖ = ‖E D‖) := by
  rintro ⟨hAE, hBE⟩
  obtain ⟨F, -, -, -, hF, -⟩ := Prop1 hABCD hA hC (ne_of_between_ends hAEC)
  have h₁ := ((Prop3 hF hA hC hAEC (hAC F hF)).1 hAE).1
  have h₂ := ((Prop3 hF hB hD hBED (hBD F hF)).1 hBE).1
  sorry

/-- III.5 in full: one centre and one common point make one circle (System E,
Diagram-segment 2). -/
theorem T05 {E : Point} {ABC CDG : Circle} (hne : ABC ≠ CDG) (hcut : CirclesMeet ABC CDG) :
    ¬ (Centre E ABC ∧ Centre E CDG) := by
  rintro ⟨hE₁, hE₂⟩
  obtain ⟨B, C, -, -, -, hC₁, hC₂⟩ := hcut
  exact hne (circle_eq hE₁ hE₂ hC₁ hC₂ rfl)

/-- III.6 in full. -/
theorem T06 {C F : Point} {ABC CDE : Circle} (htouch : CirclesTouch ABC CDE C) :
    ¬ (Centre F ABC ∧ Centre F CDE) := by
  rintro ⟨hF₁, hF₂⟩
  rcases htouch with ⟨hC₁, hC₂, hne, -⟩ | ⟨hC₂, hC₁, hne, -⟩ | ⟨-, -, hout⟩
  · exact hne (circle_eq hF₁ hF₂ hC₁ hC₂ rfl)
  · exact hne (circle_eq hF₂ hF₁ hC₂ hC₁ rfl)
  · exact hout F (centre_inside hF₁) (centre_inside hF₂)

/-- III.7, its first steps. -/
theorem T07 {A D E F : Point} {ABCD : Circle} (hE : Centre E ABCD) (hA : OnCircle A ABCD)
    (hD : OnCircle D ABCD) (hAED : Between A E D) (hEFD : Between E F D) :
    (∀ B : Point, OnCircle B ABCD → B ≠ A → ‖F B‖ < ‖F A‖) ∧
    (∀ G : Point, OnCircle G ABCD → G ≠ D → ‖F D‖ < ‖F G‖) ∧
    (∀ B C : Point, OnCircle B ABCD → OnCircle C ABCD → SameSideOf B C A D →
      ∠ A F B < ∠ A F C → ‖F C‖ < ‖F B‖) ∧
    (∀ G : Point, OnCircle G ABCD → ¬ Collinear A D G → ∃ H : Point, OnCircle H ABCD ∧
      OppositeSidesOf H G A D ∧ ‖F H‖ = ‖F G‖ ∧
      ∀ K : Point, OnCircle K ABCD → ‖F K‖ = ‖F G‖ → K = G ∨ K = H) := by
  have hAEF : Between A E F := between_cut hAED hEFD
  have hFA : ‖F A‖ = ‖F E‖ + ‖E A‖ := by
    rw [len_symm F A, len_symm F E, len_symm E A, ← len_add_of_between hAEF]; ac_rfl
  refine ⟨fun B hB hBA => ?_, fun G hG hGD => ?_, fun B C hB hC hBC h => ?_, fun G hG hG' => ?_⟩
  · have _ := hFA
    sorry
  · sorry
  · sorry
  · sorry

/-- III.8, its first steps: the centre by III.1, on `GA`. -/
theorem T08 {A D G : Point} {ABC : Circle} (hABC : ∃ M : Point, Centre M ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A) :
    (∀ E : Point, OnCircle E ABC → E ≠ A → ‖D E‖ < ‖D A‖) ∧
    (∀ E F : Point, OnCircle E ABC → OnCircle F ABC →
      (∃ H : Point, OnCircle H ABC ∧ Between D H E) →
      (∃ L : Point, OnCircle L ABC ∧ Between D L F) →
      SameSideOf E F D A → ∠ A D E < ∠ A D F → ‖D F‖ < ‖D E‖) ∧
    (∀ K : Point, OnCircle K ABC → K ≠ G → ‖D G‖ < ‖D K‖) ∧
    (∀ K L : Point, OnCircle K ABC → OnCircle L ABC →
      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →
      (∃ F : Point, OnCircle F ABC ∧ Between D L F) →
      SameSideOf K L D A → ∠ A D K < ∠ A D L → ‖D K‖ < ‖D L‖) ∧
    (∀ K : Point, OnCircle K ABC → ¬ Collinear D A K → ∃ B : Point, OnCircle B ABC ∧
      OppositeSidesOf B K D A ∧ ‖D B‖ = ‖D K‖ ∧
      ∀ N : Point, OnCircle N ABC → ‖D N‖ = ‖D K‖ → N = K ∨ N = B) := by
  obtain ⟨M, -, -, -, hM, -⟩ := Prop1 hABC hA hG (ne_of_between (between_symm hDGA))
  have hGMA := hGA M hM
  sorry

/-- III.9, its first steps: `AB`, `BC` bisected at `E`, `F`. -/
theorem T09 {A B C D : Point} {ABC : Circle} (hABC : ∃ O : Point, Centre O ABC)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hDA : ‖D A‖ = ‖D B‖) (hDB : ‖D B‖ = ‖D C‖) :
    Centre D ABC := by
  obtain ⟨E, hAEB, hAE⟩ := BookI.Prop10 hAB
  obtain ⟨F, hBFC, hBF⟩ := BookI.Prop10 hBC
  obtain ⟨O, hO⟩ := hABC
  sorry

/-- III.10, its first steps. -/
theorem T10 {B G H : Point} {ABC DEF : Circle} (hABC : ∃ P : Point, Centre P ABC)
    (hDEF : ∃ P : Point, Centre P DEF) (hB₁ : OnCircle B ABC) (hB₂ : OnCircle B DEF)
    (hG₁ : OnCircle G ABC) (hG₂ : OnCircle G DEF) (hH₁ : OnCircle H ABC)
    (hH₂ : OnCircle H DEF) (hBG : B ≠ G) (hBH : B ≠ H) (hGH : G ≠ H) :
    ABC = DEF := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨K, hBKH, hBK⟩ := BookI.Prop10 hBH
  obtain ⟨L, hBLG, hBL⟩ := BookI.Prop10 hBG
  /- The two circles cut one another, at `B` and `G`; III.5 will forbid one centre. -/
  have hcut : CirclesMeet ABC DEF := ⟨B, G, hBG, hB₁, hB₂, hG₁, hG₂⟩
  sorry

/-- III.12, its first steps: the centres differ (III.6). -/
theorem T12 {A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)
    (htouch : TouchesExternally ABC ADE A) :
    Between F A G := by
  have hFG : F ≠ G := fun e => (Prop6 (F := F) (Or.inr (Or.inr htouch))) ⟨hF, e ▸ hG⟩
  have _ := hFG
  sorry

/-- III.14, its first steps: the centre by III.1, which is `E`; the feet within the
straight lines (`foot_between`), and bisecting them (III.3). -/
theorem T14 {A B C D E F G : Point} {ABDC : Circle} (hE : Centre E ABDC) (hA : OnCircle A ABDC)
    (hB : OnCircle B ABDC) (hC : OnCircle C ABDC) (hD : OnCircle D ABDC)
    (hE_AB : ¬ Collinear A B E) (hE_CD : ¬ Collinear C D E) (hF : Collinear A B F)
    (hEF : ∀ P : Point, Collinear A B P → P ≠ F → ∠ E F P = ∟) (hG : Collinear C D G)
    (hEG : ∀ P : Point, Collinear C D P → P ≠ G → ∠ E G P = ∟) :
    ‖A B‖ = ‖C D‖ ↔ ‖E F‖ = ‖E G‖ := by
  /- "Let the centre of the circle ABDC be taken [III. 1], and let it be E": III.1 finds a
     centre, and a circle has one centre (System E, Generalities 2). -/
  obtain ⟨E₀, -, -, -, hE₀, -⟩ := Prop1 ⟨E, hE⟩ hA hB (Triangle.ne₁₂ hE_AB)
  obtain rfl : E = E₀ := centre_unique hE hE₀
  /- The feet lie within the straight lines [I. 17, I. 19, through `foot_between`]. -/
  have hAFB : Between A F B := foot_between hE hA hB hE_AB hF hEF
  have hCGD : Between C G D := foot_between hE hC hD hE_CD hG hEG
  /- EF through the centre cuts AB at right angles, so bisects it [III. 3]. -/
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hAFB)
  have hF_L : OnLine F L := on_line_of_between_ends hAFB hA_L hB_L
  have hEF' : E ≠ F := fun h => hE_AB ⟨L, hA_L, hB_L, h ▸ hF_L⟩
  have hAF : ‖A F‖ = ‖F B‖ := (Prop3 hE hA hB hAFB hE_AB).2 (by
    have := hEF A ⟨L, hA_L, hB_L, hA_L⟩ (ne_of_between hAFB)
    rwa [angle_symm hEF' (ne_of_between hAFB)] at this)
  have _ := hCGD
  have _ := hAF
  sorry

/-- III.17, its first steps: the centre taken by III.1, after two points of the circle on
the straight line from the given centre to `A`; then `D` where `EA` meets the circle, and
the circle `AFG`. -/
theorem T17 {A : Point} {BCD : Circle} (hBCD : ∃ E : Point, Centre E BCD)
    (hA : OutsideCircle A BCD) :
    ∃ B : Point, OnCircle B BCD ∧ Touches A B BCD := by
  /- "Let the centre E of the circle be taken [III. 1]". III.1 needs two points of the
     circle: the straight line from the circle's centre `E₀` to `A` meets it between them
     (System E, Intersections 4) and beyond `E₀` (Intersections 5). III.1's centre is `E₀`
     (Generalities 2). -/
  obtain ⟨E₀, hE₀⟩ := hBCD
  have hE₀A : E₀ ≠ A := fun e => hA.1 (e ▸ centre_inside hE₀)
  obtain ⟨L, hE₀_L, hA_L⟩ := Postulate1 E₀ A hE₀A
  obtain ⟨D, hD, hD_L, hE₀DA⟩ := line_circle_between (centre_inside hE₀) hE₀_L hA hA_L
  obtain ⟨D', hD', -, hD'E₀A⟩ := line_circle_beyond (centre_inside hE₀) hE₀_L hA_L hE₀A.symm
  have hDD' : D ≠ D' := fun e => not_between_of_between (e ▸ hD'E₀A) hE₀DA
  obtain ⟨E, -, -, -, hE, -⟩ := Prop1 ⟨E₀, hE₀⟩ hD hD' hDD'
  obtain rfl : E = E₀ := centre_unique hE hE₀
  /- With centre `E` and distance `EA` the circle `AFG`. -/
  obtain ⟨AFG, hE', hA'⟩ := Postulate3 E A hE₀A
  have _ := hD_L
  sorry

/-- III.19 in full, from III.18. -/
theorem T19 {A C D E : Point} {ABC : Circle} (hC : OnCircle C ABC) (hDE : Touches D E ABC)
    (hCDE : Collinear D E C) (hA : ¬ Collinear D E A)
    (hCA : ∀ P : Point, Collinear D E P → P ≠ C → ∠ A C P = ∟) :
    ∀ F : Point, Centre F ABC → Collinear A C F := by
  intro F hF
  have h18 := Prop18 hF hC hDE hCDE
  /- A point `P` of the tangent other than `C`. -/
  obtain ⟨P, hP, hPC⟩ : ∃ P : Point, Collinear D E P ∧ P ≠ C := by
    obtain ⟨L, hD_L, hE_L⟩ := Postulate1 D E hDE.1
    by_cases hDC : D = C
    · exact ⟨E, ⟨L, hD_L, hE_L, hE_L⟩, fun e => hDE.1 (hDC.trans e.symm)⟩
    · exact ⟨D, ⟨L, hD_L, hE_L, hD_L⟩, hDC⟩
  obtain ⟨L, hD_L, hE_L, hP_L⟩ := hP
  have hC_L : OnLine C L := by
    obtain ⟨M, h1, h2, h3⟩ := hCDE; exact (line_unique hDE.1 h1 h2 hD_L hE_L) ▸ h3
  have hF_L : ¬ OnLine F L := fun h => hDE.not_inside ⟨L, hD_L, hE_L, h⟩ (centre_inside hF)
  have hA_L : ¬ OnLine A L := fun h => hA ⟨L, hD_L, hE_L, h⟩
  have hPCF : Triangle P C F := Triangle.of_line hP_L hC_L hPC hF_L
  have hPCA : Triangle P C A := Triangle.of_line hP_L hC_L hPC hA_L
  have hF' : ∠ P C F = ∟ := by
    rw [angle_symm hPC hPCF.ne₂₃.symm]; exact h18 P ⟨L, hD_L, hE_L, hP_L⟩ hPC
  have hA' : ∠ P C A = ∟ := by
    rw [angle_symm hPC hPCA.ne₂₃.symm]; exact hCA P ⟨L, hD_L, hE_L, hP_L⟩ hPC
  /- One straight line at right angles to `DE` at `C`. -/
  obtain ⟨M, hC_M, hF_M, hA_M⟩ := one_perp hPCF hPCA hF' hA'
  exact ⟨M, hA_M, hC_M, hF_M⟩

/-- III.23, its first steps. -/
theorem T23 {A B C D : Point} {ACB ADB : Circle} (hACB : ∃ O : Point, Centre O ACB)
    (hADB : ∃ O : Point, Centre O ADB) (hA₁ : OnCircle A ACB) (hB₁ : OnCircle B ACB)
    (hC : OnCircle C ACB) (hA₂ : OnCircle A ADB) (hB₂ : OnCircle B ADB)
    (hD : OnCircle D ADB) (hCD : SameSideOf C D A B) (hsim : ∠ A C B = ∠ A D B) :
    ACB = ADB := by
  refine Classical.byContradiction fun hne => ?_
  /- `C` is not on `ADB`: two circles meet in two points at most (III.10). -/
  have hC₂ : ¬ OnCircle C ADB := fun hC₂ =>
    hne (Prop10 hACB hADB hA₁ hA₂ hB₁ hB₂ hC hC₂ hCD.1 (hCD.triangle.ne₁₃)
      (hCD.triangle.ne₂₃))
  sorry

/-- III.25, its first steps: `AC` bisected at `D`, and the straight line at right angles on
the segment's side. -/
theorem T25 {A C : Point} {ABC : Circle} (hABC : ∃ E : Point, Centre E ABC) (hA : OnCircle A ABC)
    (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  intro P hP
  have hAC : A ≠ C := (show Triangle A C P from hP).ne₁₂
  obtain ⟨D, hADC, hAD⟩ := BookI.Prop10 hAC
  obtain ⟨L, hA_L, hC_L⟩ := Postulate1 A C hAC
  have hD_L := on_line_of_between_ends hADC hA_L hC_L
  obtain ⟨X, hXP, hX⟩ := BookI.Prop11 hAC ⟨L, hA_L, hC_L, hD_L⟩ hP
  sorry

/-- III.31 in full (the angle in the semicircle through the ground's semicircle, not
Euclid's I.5 and I.32; the rest as Euclid). -/
theorem T31 {A B C E : Point} {ABCD : Circle} (hE : Centre E ABCD) (hA : OnCircle A ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hBEC : Between B E C) (hAB : A ≠ B)
    (hAC : A ≠ C) :
    ∠ B A C = ∟ ∧
      (∀ X : Point, OnCircle X ABCD → SameSideOf X B A C → ∠ A X C < ∟) ∧
      ∀ D : Point, OnCircle D ABCD → OppositeSidesOf B D A C → ∟ < ∠ A D C := by
  have hABC : Triangle A B C :=
    Triangle.of_onCircle hA hB hC hAB (ne_of_between_ends hBEC) hAC
  obtain ⟨K, hK, -⟩ := exists_oppositeSidesOf hABC.bca []
  have hs := Circumference.semicircle hE hB hC hBEC hK.triangle
  rw [Circumference.eq ⟨E, hE⟩ hA hB hC hK.symm] at hs
  have hBAC : ∠ B A C = ∟ := Magnitude.eq_of_add_self_eq hs
  /- The angles `ABC`, `BAC` are less than two right angles [I. 17]. -/
  have h17 := (BookI.Prop17 hABC).2.2
  rw [angle_symm hABC.ne₁₃.symm hABC.ne₁₂.symm, hBAC] at h17
  have hABC' : ∠ A B C < ∟ := Magnitude.lt_of_add_lt_add_left h17
  /- Two angles making up two right angles: if one is less than a right angle, the
     other is greater. -/
  have other : ∀ {x y : Angle}, x + y = ∟ + ∟ → x < ∟ → ∟ < y := by
    intro x y hxy hx
    rcases lt_trichotomy ∟ y with h | h | h
    · exact h
    · rw [← h] at hxy
      exact absurd (CommonNotion3 hxy rfl) (Magnitude.ne_of_lt hx)
    · exact absurd (hxy ▸ lt_trans (add_lt_add_right y hx)
        (by rw [add_comm, add_comm ∟]; exact add_lt_add_right ∟ h)) (lt_irrefl _)
  /- The quadrilateral `ABCD` in the circle [III. 22]. -/
  have hless : ∀ D : Point, OnCircle D ABCD → OppositeSidesOf B D A C → ∟ < ∠ A D C := by
    intro D hD hBD
    have h22 := (Prop22 ⟨E, hE⟩ hB hC hD hA hBD.swap).2
    rw [angle_symm hABC.ne₂₃.symm hABC.ne₁₂] at h22
    exact other h22 hABC'
  refine ⟨hBAC, fun X hX hXB => ?_, hless⟩
  /- Any point `X` of the greater segment: with a point `D` of the less, `AXCD` is a
     quadrilateral in the circle [III. 22], and the angle at `D` is greater than a right
     angle. -/
  obtain ⟨D, hD, hDB⟩ := exists_onCircle_oppositeSidesOf hA hC hABC.acb
  have hXD : OppositeSidesOf X D A C := hXB.trans_opposite hDB.symm
  have h22 := (Prop22 ⟨E, hE⟩ hX hA hD hC hXD).2
  have hDAC : Triangle A D C := hXD.symm.triangle.acb
  rw [angle_symm hDAC.ne₂₃.symm hDAC.ne₁₂] at h22
  have hobtuse : ∟ < ∠ A D C := hless D hD hDB.symm
  rcases lt_trichotomy (∠ A X C) ∟ with h | h | h
  · exact h
  · rw [h, add_comm] at h22
    exact absurd (CommonNotion3 h22 rfl).symm (Magnitude.ne_of_lt hobtuse)
  · /- Both greater than a right angle: together greater than two. -/
    have h₁ : ∟ + ∟ < ∠ A X C + ∟ := add_lt_add_right ∟ h
    have h₂ : ∠ A X C + ∟ < ∠ A X C + ∠ A D C := by
      rw [add_comm (∠ A X C) ∟, add_comm (∠ A X C) (∠ A D C)]
      exact add_lt_add_right (∠ A X C) hobtuse
    exact absurd (h22 ▸ lt_trans h₁ h₂) (lt_irrefl _)

/-- III.32, its first steps: `BA` at right angles to `EF`. -/
theorem T32 {B D E F : Point} {ABCD : Circle} (hABCD : ∃ O : Point, Centre O ABCD)
    (hB : OnCircle B ABCD) (hD : OnCircle D ABCD) (hBD : B ≠ D) (hEF : Touches E F ABCD)
    (hEBF : Between E B F) :
    (∀ A : Point, OnCircle A ABCD → OppositeSidesOf A F B D → ∠ F B D = ∠ B A D) ∧
    (∀ C : Point, OnCircle C ABCD → SameSideOf C F B D → ∠ E B D = ∠ D C B) := by
  have hEF' : E ≠ F := ne_of_between_ends hEBF
  obtain ⟨L, hE_L, hF_L⟩ := Postulate1 E F hEF'
  have hB_L := on_line_of_between_ends hEBF hE_L hF_L
  have hD_L : ¬ OnLine D L := fun h => by
    /- `EF` touches the circle at `B` only. -/
    exact (hEF.2 L hE_L hF_L).2 ⟨B, D, hBD, hB_L, hB, h, hD⟩
  obtain ⟨X, hXD, hX⟩ := BookI.Prop11 hEF' ⟨L, hE_L, hF_L, hB_L⟩
    (fun ⟨M, h1, h2, h3⟩ => hD_L ((line_unique hEF' h1 h2 hE_L hF_L) ▸ h3))
  sorry

/-- III.33, its first steps: the angle at `C` is acute, right or obtuse. -/
theorem T33 {A B C₁ C C₂ : Point} (hAB : A ≠ B) (hC : Triangle C₁ C C₂) :
    ∃ (AEB : Circle) (E : Point), (∃ O : Point, Centre O AEB) ∧ OnCircle A AEB ∧
      OnCircle B AEB ∧ OnCircle E AEB ∧ ¬ Collinear A B E ∧ ∠ A E B = ∠ C₁ C C₂ := by
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  obtain ⟨F, G, -, -, hFAG⟩ := BookI.Prop23 hAB hC hP
  rcases lt_trichotomy (∠ C₁ C C₂) ∟ with h | h | h
  · sorry
  · sorry
  · sorry

/-- III.34, its first steps: a point `B` of the circle and the straight line touching at
it (III.16, Porism). -/
theorem T34 {D₁ D D₂ : Point} {ABC : Circle} (hABC : ∃ O : Point, Centre O ABC)
    (hD : Triangle D₁ D D₂) :
    ∃ A B C : Point, OnCircle A ABC ∧ OnCircle B ABC ∧ OnCircle C ABC ∧ Triangle B A C ∧
      ∠ B A C = ∠ D₁ D D₂ := by
  obtain ⟨O, hO⟩ := hABC
  obtain ⟨B, hB, -⟩ := exists_point_on_circle ABC []
  have hOB : O ≠ B := (ne_of_centre_of_on hO hB).symm
  obtain ⟨Q, hQ, -⟩ := exists_off_line hOB []
  obtain ⟨F, hFQ, hF⟩ := BookI.Prop11 hOB (by
    obtain ⟨L, h1, h2⟩ := Postulate1 O B hOB; exact ⟨L, h1, h2, h2⟩) hQ
  have hOBF : ∠ O B F = ∟ := hF O (by
    obtain ⟨L, h1, h2⟩ := Postulate1 O B hOB; exact ⟨L, h1, h2, h1⟩) hOB
  have htouch : Touches B F ABC := Prop16.porism hO hB (fun h => hFQ.triangle (by
    obtain ⟨L, h1, h2, h3⟩ := h; exact ⟨L, h1, h2, h3⟩)) hOBF
  sorry

/-- III.35, its first steps: the centre, and the case where `E` is it. -/
theorem T35 {A B C D E : Point} {ABCD : Circle} (hABCD : ∃ F : Point, Centre F ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hD : OnCircle D ABCD) (hAEC : Between A E C) (hBED : Between B E D) :
    rect A E E C = rect D E E B := by
  obtain ⟨F, -, -, -, hF, -⟩ := Prop1 hABCD hA hC (ne_of_between_ends hAEC)
  by_cases hEF : E = F
  · /- `AE`, `EC`, `DE`, `EB` all radii. -/
    subst hEF
    exact rect_congr (by rw [len_symm A E, Definition15 hF hA hD, len_symm])
      (Definition15 hF hC hB)
  · have _ := hBED
    sorry

/-- III.36, its first steps: the centre, and the right angle at `B` (III.18). -/
theorem T36 {A B C D : Point} {ABC : Circle} (hABC : ∃ F : Point, Centre F ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hDCA : Between D C A) (hDB : Touches D B ABC) :
    rect A D D C = sq D B := by
  obtain ⟨F, -, -, -, hF, -⟩ := Prop1 hABC hA hC (ne_of_between (between_symm hDCA))
  have hFBD : ∠ F B D = ∟ := Prop18 hF hB hDB (by
    obtain ⟨L, h1, h2⟩ := Postulate1 D B hDB.1; exact ⟨L, h1, h2, h2⟩) D (by
    obtain ⟨L, h1, h2⟩ := Postulate1 D B hDB.1; exact ⟨L, h1, h2, h1⟩)
    (fun e => hD.2 (e ▸ hB))
  sorry

/-- III.37, its first steps: `DE` drawn touching (III.17), the centre, and III.36. -/
theorem T37 {A B C D : Point} {ABC : Circle} (hABC : ∃ F : Point, Centre F ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hDCA : Between D C A) (h : rect A D D C = sq D B) :
    Touches D B ABC := by
  obtain ⟨E, hE, hDE⟩ := Prop17 hABC hD
  have h36 := Prop36 hABC hD hA hE hC hDCA hDE
  have hDE_DB : ‖D E‖ = ‖D B‖ := BookI.Prop46.sq (h36.symm.trans h)
  sorry

/-- III.15, its first steps: `EL` made equal to `EH` on `EK`, the less on the greater
(Definition III.5 gives `EH` less than `EK`). -/
theorem T15 {A B C D E F G H K : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hF : OnCircle F ABCD)
    (hG : OnCircle G ABCD) (hE_BC : ¬ Collinear B C E) (hE_FG : ¬ Collinear F G E)
    (hH : Collinear B C H) (hEH : ∀ P : Point, Collinear B C P → P ≠ H → ∠ E H P = ∟)
    (hK : Collinear F G K) (hEK : ∀ P : Point, Collinear F G P → P ≠ K → ∠ E K P = ∟)
    (hnearer : ‖E H‖ < ‖E K‖) :
    ‖B C‖ < ‖A D‖ ∧ ‖F G‖ < ‖B C‖ := by
  have hEK' : E ≠ K := fun e => by
    subst e; rw [len_self] at hnearer; exact not_lt_zero _ hnearer
  obtain ⟨L, hEL⟩ := BookI.Prop3 (A := E) (B := K) (C₁ := E) (C₂ := H)
    (fun e => by subst e; exact hE_BC hH) (by rw [len_symm E H] at hnearer ⊢; exact hnearer)
  sorry

end Scratch
