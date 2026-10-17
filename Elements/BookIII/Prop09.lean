import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop08
import Elements.BookI.Prop10
import Elements.BookI.Prop17
import Elements.BookIII.Prop01

/-!
# Book III, Proposition 9

Euclid's text, in Heath's translation: [`heath/III/09.md`](../../heath/III/09.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- When DA is equal to DB and D is off AB, the centre is on the straight line from D
to the middle point E of AB. This is Euclid's argument for GK, which his "For the same
reason" repeats for HL: I.8 and Definition I.10 make the angles at E right, and the
porism to III.1 puts the centre on ED. -/
theorem Prop9.centre_on {A B D E O : Point} {ABC : Circle} (hO : Centre O ABC)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hAEB : Between A E B) (hAE : ‖A E‖ = ‖E B‖)
    (hDA : ‖D A‖ = ‖D B‖) (hD : ¬ Collinear A B D) : ∠ A E D = ∟ ∧ Collinear E D O := by
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B (ne_of_between_ends hAEB)
  have hE_L := on_line_of_between_ends hAEB hA_L hB_L
  have hD_L : ¬ OnLine D L := (show Triangle A B D from hD).off_line hA_L hB_L
  have hEAD : Triangle E A D := Triangle.of_line hE_L hA_L (ne_of_between hAEB).symm hD_L
  have hEBD : Triangle E B D :=
    Triangle.of_line hE_L hB_L (ne_of_between (between_symm hAEB)).symm hD_L
  have h8 : ∠ A E D = ∠ B E D := BookI.Prop8 hEAD hEBD (by rw [len_symm E A, hAE]) rfl
    (by rw [len_symm A D, len_symm B D, hDA])
  have hr : ∠ A E D = ∟ := Postulate4
    ⟨B, hAEB, hEAD.bac, h8.trans (angle_symm hEBD.ne₁₂.symm hEBD.ne₁₃.symm)⟩
  exact ⟨hr, Prop1.porism hO hA hB hAEB hAE hD hr⟩

/-- The straight lines at right angles to AB at E and to BC at F are not one straight
line, for then the triangle BEF would have two right angles [I. 17]. Euclid reads this
off his figure. -/
theorem Prop9.apart {A B C D E F : Point} (hABC : Triangle A B C) (hAEB : Between A E B)
    (hBFC : Between B F C) (hDAB : ¬ Collinear A B D) (hDBC : ¬ Collinear B C D)
    (hAED : ∠ A E D = ∟) (hBFD : ∠ B F D = ∟) : ¬ Collinear E F D := by
  rintro ⟨L, hE_L, hF_L, hD_L⟩
  obtain ⟨M, hA_M, hB_M⟩ := Postulate1 A B hABC.ne₁₂
  obtain ⟨N, hB_N, hC_N⟩ := Postulate1 B C hABC.ne₂₃
  have hE_M := on_line_of_between_ends hAEB hA_M hB_M
  have hF_N := on_line_of_between_ends hBFC hB_N hC_N
  have hED : E ≠ D := fun e => hDAB ⟨M, hA_M, hB_M, e ▸ hE_M⟩
  have hFD : F ≠ D := fun e => hDBC ⟨N, hB_N, hC_N, e ▸ hF_N⟩
  have hBE : B ≠ E := ne_of_between (between_symm hAEB)
  have hEF : E ≠ F := by
    rintro rfl
    exact hABC ⟨M, hA_M, hB_M, (line_unique hBE.symm hE_M hB_M hF_N hB_N) ▸ hC_N⟩
  have hB_L : ¬ OnLine B L := fun hB =>
    hDAB ⟨M, hA_M, hB_M, (line_unique hBE hB hE_L hB_M hE_M) ▸ hD_L⟩
  have hBED : ∠ B E D = ∟ := by
    have := adjacent_eq_of_right hA_M hB_M hAEB (fun h => hDAB ⟨M, hA_M, hB_M, h⟩) hAED
    rw [angle_symm hBE hED.symm, ← this]; exact hAED
  have hDEB : ∠ D E B = ∟ := by rw [angle_symm hED.symm hBE]; exact hBED
  /- Whether F is on the ray ED or on the opposite ray, the angle BEF is right. -/
  have hBEF : ∠ B E F = ∟ := by
    by_cases hb : Between D E F
    · have := adjacent_eq_of_right hD_L hF_L hb hB_L hDEB
      rw [← this]; exact hDEB
    · rw [angle_onRay_right ⟨hED, hEF.symm, ⟨L, hE_L, hD_L, hF_L⟩, fun h => hb (between_symm h)⟩
        hBE]
      exact hBED
  have hBFE : ∠ B F E = ∟ := by
    by_cases hb : Between D F E
    · have h1 : ∠ D F B = ∟ := by
        rw [angle_symm hFD.symm (ne_of_between hBFC)]; exact hBFD
      have := adjacent_eq_of_right hD_L hE_L hb hB_L h1
      rw [← this]; exact h1
    · rw [angle_onRay_right ⟨hFD, hEF, ⟨L, hF_L, hD_L, hE_L⟩, fun h => hb (between_symm h)⟩
        (ne_of_between hBFC)]
      exact hBFD
  have hBEF_t : Triangle B E F := Triangle.of_line hE_L hF_L hEF hB_L |>.bca |>.bca
  have h17 := (BookI.Prop17 hBEF_t).1
  rw [hBEF, angle_symm hEF (ne_of_between hBFC), hBFE] at h17
  exact lt_irrefl _ h17

/-- A point D as far from A as from B is neither A nor B. -/
theorem Prop9.ne_ends {A B D : Point} (hAB : A ≠ B) (hDA : ‖D A‖ = ‖D B‖) : D ≠ A ∧ D ≠ B := by
  constructor
  · rintro rfl
    exact hAB (eq_of_len_eq_zero (by rw [← hDA, len_self]))
  · rintro rfl
    exact hAB (eq_of_len_eq_zero (by rw [len_symm, hDA, len_self]))

/-- A point other than B is not on both of the sides AB and BC of the triangle ABC. -/
theorem Prop9.not_two {A B C D : Point} (hABC : Triangle A B C) (hDB : D ≠ B)
    (h₁ : Collinear A B D) (h₂ : Collinear B C D) : False := by
  obtain ⟨L, hA, hB, hD⟩ := h₁
  obtain ⟨M, hB', hC, hD'⟩ := h₂
  exact hABC ⟨L, hA, hB, (line_unique hDB hD' hB' hD hB) ▸ hC⟩

/-- If the centre O is on both ED and FD, and these are not one straight line, then O
is D. -/
theorem Prop9.meet_at {E F D O : Point} (h₁ : Collinear E D O) (h₂ : Collinear F D O)
    (hap : ¬ Collinear E F D) : O = D := by
  refine Classical.byContradiction fun hOD => ?_
  obtain ⟨L, hE, hD, hO⟩ := h₁
  obtain ⟨M, hF, hD', hO'⟩ := h₂
  exact hap ⟨L, hE, (line_unique (Ne.symm hOD) hD' hO' hD hO) ▸ hF, hD⟩

/-- If a point be taken within a circle, and more than two equal straight lines fall from the point
on the circle, the point taken is the centre of the circle. -/
theorem Prop9 {A B C D : Point} {ABC : Circle} (hABC : ∃ O : Point, Centre O ABC)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hDA : ‖D A‖ = ‖D B‖) (hDB : ‖D B‖ = ‖D C‖) :
    Centre D ABC := by
  -- Let ABC be a circle and D a point within it, and from D let more than two equal straight
  -- lines, namely DA, DB, DC, fall on the circle ABC;
  obtain ⟨O, hO⟩ := hABC
  have hT : Triangle A B C := Triangle.of_onCircle hA hB hC hAB hBC hAC
  -- I say that the point D is the centre of the circle ABC.
  -- For let AB, BC be joined and bisected at the points E, F, and let ED, FD be joined and
  -- drawn through to the points G, K, H, L.
  obtain ⟨E, hAEB, hAE⟩ := BookI.Prop10 hAB
  obtain ⟨F, hBFC, hBF⟩ := BookI.Prop10 hBC
  /- This is J. G. Camerer's case (Heath, vol. 2, p. 22), where AB or BC passes through D.
     At most one of AB, BC, CA can, since D is none of A, B, C; so CA is bisected too, at
     an unlettered point, and `Prop9.centre_on` is used on the two that miss D. -/
  obtain ⟨hDA', hDB'⟩ := Prop9.ne_ends hAB hDA
  have hDC' : D ≠ C := (Prop9.ne_ends hBC hDB).2
  have hDCA : ‖D C‖ = ‖D A‖ := (hDA.trans hDB).symm
  by_cases hDAB : Collinear A B D
  · have hDBC : ¬ Collinear B C D := fun h => Prop9.not_two hT hDB' hDAB h
    have hDCA' : ¬ Collinear C A D := fun h => Prop9.not_two hT.cab hDA' h hDAB
    obtain ⟨X, hCXA, hCX⟩ := BookI.Prop10 hAC.symm
    obtain ⟨hBFD, hFDO⟩ := Prop9.centre_on hO hB hC hBFC hBF hDB hDBC
    obtain ⟨hCXD, hXDO⟩ := Prop9.centre_on hO hC hA hCXA hCX hDCA hDCA'
    have hap := Prop9.apart hT.bca hBFC hCXA hDBC hDCA' hBFD hCXD
    obtain rfl := Prop9.meet_at hFDO hXDO hap
    exact hO
  by_cases hDBC : Collinear B C D
  · have hDCA' : ¬ Collinear C A D := fun h => Prop9.not_two hT.bca hDC' hDBC h
    obtain ⟨X, hCXA, hCX⟩ := BookI.Prop10 hAC.symm
    obtain ⟨hCXD, hXDO⟩ := Prop9.centre_on hO hC hA hCXA hCX hDCA hDCA'
    obtain ⟨hAED, hEDO⟩ := Prop9.centre_on hO hA hB hAEB hAE hDA hDAB
    have hap := Prop9.apart hT.cab hCXA hAEB hDCA' hDAB hCXD hAED
    obtain rfl := Prop9.meet_at hXDO hEDO hap
    exact hO
  /- In Euclid's figure D is off both AB and BC. ED names GK, and FD names HL;
     their ends G, K, H, L need no further construction in Lean. -/
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hE_AB := on_line_of_between_ends hAEB hA_AB hB_AB
  have hD_AB : ¬ OnLine D AB := fun h => hDAB ⟨AB, hA_AB, hB_AB, h⟩
  have hEAD : Triangle E A D :=
    Triangle.of_line hE_AB hA_AB (ne_of_between hAEB).symm hD_AB
  have hEBD : Triangle E B D :=
    Triangle.of_line hE_AB hB_AB (ne_of_between (between_symm hAEB)).symm hD_AB
  -- Then, since AE is equal to EB,
  have hAE_BE : ‖A E‖ = ‖B E‖ := hAE.trans (len_symm E B)
  -- and ED is common,
  have hED : ‖E D‖ = ‖E D‖ := rfl
  -- the two sides AE, ED are equal to the two sides BE, ED;
  have hEA_EB : ‖E A‖ = ‖E B‖ := by rw [len_symm E A, hAE_BE, len_symm B E]
  -- and the base DA is equal to the base DB;
  have hAD_BD : ‖A D‖ = ‖B D‖ := by rw [len_symm A D, len_symm B D, hDA]
  -- therefore the angle AED is equal to the angle BED. [I. 8]
  have h8 : ∠ A E D = ∠ B E D := BookI.Prop8 hEAD hEBD hEA_EB hED hAD_BD
  -- Therefore each of the angles AED, BED is right; [I. Def. 10]
  have hAED : ∠ A E D = ∟ := Postulate4
    ⟨B, hAEB, hEAD.bac, h8.trans (angle_symm hEBD.ne₁₂.symm hEBD.ne₁₃.symm)⟩
  -- therefore GK cuts AB into two equal parts and at right angles.
  -- And since, if in a circle a straight line cut a straight line into two equal parts and at
  -- right angles, the centre of the circle is on the cutting straight line, [III. 1, Por.]
  -- the centre of the circle is on GK.
  have hEDO : Collinear E D O := Prop1.porism hO hA hB hAEB hAE hDAB hAED
  -- For the same reason
  -- the centre of the circle ABC is also on HL.
  obtain ⟨hBFD, hFDO⟩ := Prop9.centre_on hO hB hC hBFC hBF hDB hDBC
  -- And the straight lines GK, HL have no other point common but the point D;
  /- GK and HL are two straight lines (`Prop9.apart`), and two straight lines have at
     most one point in common. -/
  have hap := Prop9.apart hT hAEB hBFC hDAB hDBC hAED hBFD
  obtain rfl : O = D := Prop9.meet_at hEDO hFDO hap
  -- therefore the point D is the centre of the circle ABC.
  exact hO
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
