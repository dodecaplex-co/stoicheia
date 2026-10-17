import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop04
import Elements.BookI.Prop20
import Elements.BookI.Prop23
import Elements.BookI.Prop24

/-!
# Book III, Proposition 7

Euclid's text, in Heath's translation: [`heath/III/07.md`](../../heath/III/07.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If on the diameter of a circle a point be taken which is not the centre of the circle, and from
the point straight lines fall upon the circle, that will be greatest on which the centre is, the
remainder of the same diameter will be least, and of the rest the nearer to the straight line
through the centre is always greater than the more remote, and only two equal straight lines
will fall from the point on the circle, one on each side of the least straight line. -/
theorem Prop7 {A D E F : Point} {ABCD : Circle} (hE : Centre E ABCD) (hA : OnCircle A ABCD)
    (hD : OnCircle D ABCD) (hAED : Between A E D) (hEFD : Between E F D) :
    (∀ B : Point, OnCircle B ABCD → B ≠ A → ‖F B‖ < ‖F A‖) ∧
    (∀ G : Point, OnCircle G ABCD → G ≠ D → ‖F D‖ < ‖F G‖) ∧
    (∀ B C : Point, OnCircle B ABCD → OnCircle C ABCD → SameSideOf B C A D →
      ∠ A F B < ∠ A F C → ‖F C‖ < ‖F B‖) ∧
    (∀ G : Point, OnCircle G ABCD → ¬ Collinear A D G → ∃ H : Point, OnCircle H ABCD ∧
      OppositeSidesOf H G A D ∧ ‖F H‖ = ‖F G‖ ∧
      ∀ K : Point, OnCircle K ABCD → ‖F K‖ = ‖F G‖ → K = G ∨ K = H) := by
  -- Let ABCD be a circle, and let AD be a diameter of it;
  have hAD : A ≠ D := ne_of_between_ends hAED
  obtain ⟨L, hA_L, hD_L⟩ := Postulate1 A D hAD
  have hE_L : OnLine E L := on_line_of_between_ends hAED hA_L hD_L
  -- on AD let a point F be taken which is not the centre of the circle, let E be the centre of
  -- the circle,
  have hF_L : OnLine F L := on_line_of_between_ends hEFD hE_L hD_L
  have hEF : E ≠ F := ne_of_between hEFD
  have hAEF : Between A E F := between_cut hAED hEFD
  have hFA : F ≠ A := (ne_of_between_ends hAEF).symm
  have hF_in : InsideCircle F ABCD :=
    inside_of_between (Or.inl (centre_inside hE)) (Or.inr hD) hEFD
  /- A point of the circle on the diameter is `A` or `D` (System E, Circle 1). -/
  have hends : ∀ K, OnCircle K ABCD → OnLine K L → K ≠ A → K = D := by
    intro K hK hK_L hKA
    have hAEK : Between A E K :=
      between_of_inside_chord hE_L hA_L hK_L (centre_inside hE) hA hK hKA.symm
    exact (OnRay.of_between_between hAED hAEK).eq_of_len_eq (Definition15 hE hK hD)
  /- `FD` is less than `FA`: `FD` is less than `ED`, which is `EA`, less than `FA`. -/
  have hDA : ‖F D‖ < ‖F A‖ := by
    have h₁ : ‖D F‖ < ‖D E‖ := len_lt_of_between (between_symm hEFD)
    have h₂ : ‖A E‖ < ‖A F‖ := len_lt_of_between hAEF
    rw [len_symm D F, len_symm D E, Definition15 hE hD hA, len_symm E A] at h₁
    rw [len_symm A F] at h₂
    exact lt_trans h₁ h₂
  -- and from F let straight lines FB, FC, FG fall upon the circle ABCD;
  -- I say that FA is greatest, FD is least, and of the rest FB is greater than FC, and FC than
  -- FG.
  -- For let BE, CE, GE be joined.
  have hgreatest : ∀ B : Point, OnCircle B ABCD → B ≠ A → ‖F B‖ < ‖F A‖ := by
    intro B hB hBA
    by_cases hB_L : OnLine B L
    · rw [hends B hB hB_L hBA]
      exact hDA
    have hEBF : Triangle E B F := (Triangle.of_line hE_L hF_L hEF hB_L).acb
    -- Then, since in any triangle two sides are greater than the remaining one, [I. 20]
    -- EB, EF are greater than BF.
    have h20 : ‖B F‖ < ‖B E‖ + ‖E F‖ := (BookI.Prop20 hEBF).1
    -- But AE is equal to BE;
    have hAE : ‖A E‖ = ‖B E‖ := by rw [len_symm A E, len_symm B E]; exact Definition15 hE hA hB
    -- therefore AF is greater than BF.
    rw [← hAE, len_add_of_between hAEF, len_symm B F, len_symm A F] at h20
    exact h20
  have hnearer : ∀ B C : Point, OnCircle B ABCD → OnCircle C ABCD → SameSideOf B C A D →
      ∠ A F B < ∠ A F C → ‖F C‖ < ‖F B‖ := by
    intro B C hB hC hBC hlt
    -- Again, since BE is equal to CE,
    have hBE : ‖E B‖ = ‖E C‖ := Definition15 hE hB hC
    -- and FE is common,
    have hEF_common : ‖E F‖ = ‖E F‖ := rfl
    -- the two sides BE, EF are equal to the two sides CE, EF.
    -- But the angle BEF is also greater than the angle CEF;
    have hBC' : SameSideOf B C F E := SameSideOf.of_line hEF.symm hF_L hE_L (hBC.sameSide hA_L hD_L)
    have hBF : B ≠ F := fun e => inside_not_on hF_in (e ▸ hB)
    have hCF : C ≠ F := fun e => inside_not_on hF_in (e ▸ hC)
    /- Euclid reads it off the figure; Augustus De Morgan's gap (Heath, vol. 2, p. 15). The angle `EFB` is
       the angle `AFB`, `E` being on `FA`; so `FB` falls within the angle `EFC` (`BookI.Prop24.within`)
       and crosses `EC` at `M` (`crossbar`). -/
    have hEray : OnRay E F A := OnRay.of_between (between_symm hAEF)
    rw [← angle_onRay_left hEray hBF, ← angle_onRay_left hEray hCF] at hlt
    have hwithin : SameSideOf B E F C := BookI.Prop24.within hBC'.symm hlt
    obtain ⟨M, hEMC, hM⟩ := crossbar hBC' hwithin
    have hM_in : InsideCircle M ABCD := inside_of_between (Or.inl (centre_inside hE)) (Or.inr hC) hEMC
    /- `M` is between `F` and `B`: on the ray from `F` through `B`, and not beyond `B`, for
       then `B` would be within the circle (System E, Circle 2). -/
    have hFMB : Between F M B := by
      obtain ⟨-, hMF, ⟨N, hF_N, hB_N, hM_N⟩, hMFB⟩ := hM
      have hMB : M ≠ B := fun e => inside_not_on hM_in (e ▸ hB)
      rcases between_cases hMF.symm hMB hBF.symm hF_N hM_N hB_N with h | h | h
      · exact h
      · exact absurd h hMFB
      · exact absurd hB (inside_not_on (inside_of_between (Or.inl hF_in) (Or.inl hM_in) h))
    have hBFE : Triangle B F E := hBC'.triangle.cab
    have hang : ∠ C E F < ∠ B E F := by
      rw [← angle_onRay_left (OnRay.of_between hEMC) hEF.symm]
      exact angle_lt_of_between hBFE (between_symm hFMB)
    -- therefore the base BF is greater than the base CF. [I. 24]
    have hECF : Triangle E C F := hBC'.symm.triangle.bca
    have h24 : ‖C F‖ < ‖B F‖ := BookI.Prop24 hBFE.cab hECF hBE hEF_common hang
    rw [len_symm C F, len_symm B F] at h24
    exact h24
  -- For the same reason
  -- CF is also greater than FG.
  /- The Lean above was said of any two points `B`, `C` on one side of `AD`; `C`, `G` are
     such a pair. -/
  have hleast : ∀ G : Point, OnCircle G ABCD → G ≠ D → ‖F D‖ < ‖F G‖ := by
    intro G hG hGD
    by_cases hG_L : OnLine G L
    · have hGA : G = A := Classical.byContradiction fun h => hGD (hends G hG hG_L h)
      rw [hGA]
      exact hDA
    have hFGE : Triangle F G E := (Triangle.of_line hF_L hE_L hEF.symm hG_L).acb
    -- Again, since GF, FE are greater than EG,
    have h20 : ‖G E‖ < ‖G F‖ + ‖F E‖ := (BookI.Prop20 hFGE).1
    -- and EG is equal to ED,
    have hEG : ‖E G‖ = ‖E D‖ := Definition15 hE hG hD
    -- GF, FE are greater than ED.
    rw [len_symm G E, hEG] at h20
    -- Let EF be subtracted from each;
    -- therefore the remainder GF is greater than the remainder FD.
    rw [← len_add_of_between hEFD, len_symm F E, add_comm (‖G F‖)] at h20
    rw [len_symm F G]
    exact Magnitude.lt_of_add_lt_add_left h20
  -- Therefore FA is greatest, FD is least, and FB is greater than FC, and FC than FG.
  refine ⟨hgreatest, hleast, hnearer, ?_⟩
  -- I say also that from the point F only two equal straight lines will fall on the circle
  -- ABCD, one on each side of the least FD.
  intro G hG hG_AD
  have hG_L : ¬ OnLine G L := fun h => hG_AD ⟨L, hA_L, hD_L, h⟩
  -- For on the straight line EF, and at the point E on it, let the angle FEH be constructed
  -- equal to the angle GEF [I. 23], and let FH be joined.
  have hEFG : Triangle E F G := Triangle.of_line hE_L hF_L hEF hG_L
  obtain ⟨P, hPG, -⟩ := exists_point_opposite_side hG_L []
  have hP_EF : ¬ Collinear E F P := Triangle.of_line hE_L hF_L hEF hPG.1
  obtain ⟨H', F', hF', hH', hang⟩ := BookI.Prop23 hEF hEFG.cab hP_EF
  have hEH' : E ≠ H' := hH'.triangle.ne₁₃
  /- `H` where the straight line `EH'` meets the circle, on `H'`'s side of `E`
     (System E, Intersections 5, with `H'E` produced to `Q`). -/
  obtain ⟨N, hE_N, hH'_N⟩ := Postulate1 E H' hEH'
  obtain ⟨Q, hH'EQ⟩ := produce hEH'.symm
  have hQ_N : OnLine Q N := on_line_of_between hH'EQ hH'_N hE_N
  obtain ⟨H, hH, -, hHEQ⟩ :=
    line_circle_beyond (centre_inside hE) hE_N hQ_N (ne_of_between (between_symm hH'EQ))
  have hH_ray : OnRay H E H' := OnRay.of_between_between (between_symm hH'EQ) (between_symm hHEQ)
  /- `H` is on the other side of `AD` from `G`. -/
  have hHP : SameSideOf H P E F := SameSideOf.of_onRay hH_ray hH'
  have hHG_EF : OppositeSidesOf H G E F :=
    hHP.trans_opposite (OppositeSidesOf.of_line hEF hE_L hF_L hPG)
  have hHG : OppositeSidesOf H G A D :=
    OppositeSidesOf.of_line hAD hA_L hD_L (hHG_EF.oppositeSides hE_L hF_L)
  -- Then, since GE is equal to EH,
  have hEH : ‖E H‖ = ‖E G‖ := Definition15 hE hH hG
  -- and EF is common,
  have hEF_common : ‖E F‖ = ‖E F‖ := rfl
  -- the two sides GE, EF are equal to the two sides HE, EF;
  -- and the angle GEF is equal to the angle HEF;
  have hFEH : ∠ F E H = ∠ G E F :=
    (angle_eq_of_onRay hF'.symm hH_ray).trans ((angle_symm hF'.2.1 hEH'.symm).trans hang)
  have hEHF : Triangle E H F := hHG_EF.triangle.acb
  have hGEF_HEF : ∠ G E F = ∠ H E F := by
    rw [← hFEH, angle_symm hEF.symm hEHF.ne₁₂.symm]
  -- therefore the base FG is equal to the base FH. [I. 4]
  have hFG_FH : ‖G F‖ = ‖H F‖ := (BookI.Prop4 hEFG.acb hEHF hEH.symm hEF_common hGEF_HEF).1
  have hFH : ‖F H‖ = ‖F G‖ := by rw [len_symm F H, len_symm F G]; exact hFG_FH.symm
  -- I say again that another straight line equal to FG will not fall on the circle from the
  -- point F.
  refine ⟨H, hH, hHG, hFH, ?_⟩
  -- For, if possible, let FK so fall.
  intro K hK hFK
  -- Then, since FK is equal to FG, and FH to FG,
  -- FK is also equal to FH,
  have hFKH : ‖F K‖ = ‖F H‖ := hFK.trans hFH.symm
  -- the nearer to the straight line through the centre being thus equal to the more remote:
  -- which is impossible.
  /- On one side of `AD`, two points of the circle as far from `F` make one point: were
     they two, one would be the nearer, and greater. -/
  have hone : ∀ X Y : Point, OnCircle X ABCD → OnCircle Y ABCD → SameSideOf X Y A D →
      ‖F X‖ = ‖F Y‖ → X = Y := by
    intro X Y hX hY hXY hFXY
    rcases lt_trichotomy (∠ A F X) (∠ A F Y) with h | h | h
    · exact absurd hFXY (Magnitude.ne_of_lt (hnearer X Y hX hY hXY h)).symm
    · have hXY' : SameSideOf X Y F A :=
        SameSideOf.of_line hFA hF_L hA_L (hXY.sameSide hA_L hD_L)
      exact (onRay_of_angle_eq hXY' h).eq_of_len_eq hFXY
    · exact absurd hFXY (Magnitude.ne_of_lt (hnearer Y X hY hX hXY.symm h))
  by_cases hK_L : OnLine K L
  · /- `K` on the diameter is `A`, the greatest, or `D`, the least. -/
    have hGA : G ≠ A := fun e => hG_L (e ▸ hA_L)
    have hGD : G ≠ D := fun e => hG_L (e ▸ hD_L)
    by_cases hKA : K = A
    · subst hKA
      exact absurd hFK (Magnitude.ne_of_lt (hgreatest G hG hGA)).symm
    · have hKD := hends K hK hK_L hKA
      subst hKD
      exact absurd hFK (Magnitude.ne_of_lt (hleast G hG hGD))
  by_cases hKG : SameSideOf K G A D
  · exact Or.inl (hone K G hK hG hKG hFK)
  · have hKG' : OppositeSidesOf K G A D :=
      OppositeSidesOf.of_line hAD hA_L hD_L
        ⟨hK_L, hG_L, fun hs => hKG (SameSideOf.of_line hAD hA_L hD_L hs)⟩
    exact Or.inr (hone K H hK hH (OppositeSidesOf.sameSideOf hKG'.symm hHG.symm)
      hFKH)
  -- Therefore another straight line equal to GF will not fall from the point F upon the
  -- circle;
  -- therefore only one straight line will so fall.
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
