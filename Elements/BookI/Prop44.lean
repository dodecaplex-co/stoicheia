import Elements.Figure.Basics
import Elements.BookI.Prop02
import Elements.BookI.Prop04
import Elements.BookI.Prop15
import Elements.BookI.Prop23
import Elements.BookI.Prop29
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop42
import Elements.BookI.Prop43
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 44

Euclid's text, in Heath's translation: [`heath/I/44.md`](../../heath/I/44.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

"Let it be placed so that BE is in a straight line with AB": Euclid moves the
parallelogram I.42 has made. Lean cannot move a figure, so `Prop44.place` builds
an equal parallelogram where Euclid puts his, and the proof cites it at that
sentence.
-/

namespace Elements.BookI

open Tacit

/-- "Let it be placed so that BE is in a straight line with AB." Euclid moves the
parallelogram made by I.42 into place without a word, as if picking it up. Lean
cannot move a figure, so it builds an equal one where Euclid puts his. Given the
parallelogram `PQRS`, with its angle `RQP`, and a straight line `AB`: produce `AB` to
`E`, making `BE` equal to `QR` [I. 2]; at `B` on `BE` construct the angle `EBG` equal
to the angle `RQP`, on the side of `X` [I. 23], with `BG` equal to `QP` [I. 2];
through `G` and `E` draw parallels to `BE` and `BG` [I. 31], meeting at `F`
(`Prop30.meet`). Then `BEFG` is a parallelogram, and it is equal to `PQRS`, for each
is double a triangle [I. 34], and the triangles `GBE` and `PQR` are equal [I. 4]. -/
theorem Prop44.place {A B X P Q R S : Point} (hAB : A ≠ B) (hX : ¬ Collinear A B X)
    (h : Parallelogram P Q R S) :
    ∃ E F G : Point, Between A B E ∧ SameSideOf G X A B ∧ Parallelogram B E F G ∧
      ∠ E B G = ∠ R Q P ∧ quadArea B E F G = quadArea P Q R S := by
  have hPQR : Triangle P Q R := h.triangle
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hX_AB : ¬ OnLine X AB := fun hX' => hX ⟨AB, hA_AB, hB_AB, hX'⟩
  /- Produce `AB` to `E`, with `BE` equal to `QR`. -/
  obtain ⟨E₁, hABE₁⟩ := produce hAB
  obtain ⟨K₁, hBK₁⟩ := Prop2 B Q R hPQR.ne₂₃
  obtain ⟨E, hE, hBE⟩ := OnRay.exists_len_eq (ne_of_len_eq hBK₁ hPQR.ne₂₃)
    (ne_of_between (between_symm hABE₁)).symm
  have hABE : Between A B E := hE.between hABE₁
  have hBE_QR : ‖B E‖ = ‖Q R‖ := hBE.trans hBK₁
  have hE_AB : OnLine E AB := on_line_of_between hABE hA_AB hB_AB
  have hBE_ne : B ≠ E := (ne_of_between (between_symm hABE)).symm
  /- At `B` on `BE`, the angle `EBG` equal to the angle `RQP`, on `X`'s side, with `BG`
     equal to `QP`. -/
  have hX' : ¬ Collinear B E X := fun ⟨K, hB_K, hE_K, hX_K⟩ =>
    hX_AB ((line_unique hBE_ne hB_K hE_K hB_AB hE_AB) ▸ hX_K)
  obtain ⟨E₂, G₁, hE₂, hG₁, hang⟩ := Prop23 hBE_ne hPQR.cba hX'
  obtain ⟨K₂, hBK₂⟩ := Prop2 B Q P hPQR.ne₁₂.symm
  obtain ⟨G, hG, hBG⟩ :=
    OnRay.exists_len_eq (ne_of_len_eq hBK₂ hPQR.ne₁₂.symm) hG₁.triangle.ne₁₃
  have hBG_QP : ‖B G‖ = ‖Q P‖ := hBG.trans hBK₂
  have hGX : SameSideOf G X B E := SameSideOf.of_onRay hG hG₁
  have hEBG : ∠ E B G = ∠ R Q P := (angle_eq_of_onRay hE₂.symm hG).trans hang
  have hBEG : Triangle B E G := hGX.triangle
  /- Through `G` a parallel to `BE`, through `E` a parallel to `BG`, meeting at `F`. -/
  obtain ⟨ℓ₁, hG_ℓ₁, hℓ₁⟩ := Prop31.line (hBEG.off_line hB_AB hE_AB)
  obtain ⟨F, -, hGBEF⟩ := Prop31.parallelogram hℓ₁ hG_ℓ₁ hB_AB hE_AB hBE_ne
  have hBEFG : Parallelogram B E F G := hGBEF.rotate
  /- Each parallelogram is double a triangle, and the triangles are equal. -/
  have hGBE : ∠ G B E = ∠ P Q R := by
    rw [angle_symm hBEG.ne₁₃.symm hBE_ne.symm, hEBG, angle_symm hPQR.ne₂₃.symm hPQR.ne₁₂]
  have htri : △ B G E = △ Q P R := (Prop4 hBEG.acb hPQR.bac hBG_QP hBE_QR hGBE).2.1
  refine ⟨E, F, G, hABE, ?_, hBEFG, hEBG, ?_⟩
  · exact SameSideOf.of_line hAB hA_AB hB_AB (hGX.sameSide hB_AB hE_AB)
  · rw [← hBEFG.quadArea_rotate, ← quadArea_rotate₂ E F G B,
      Prop34.bisect hBEFG.rotate.rotate.rotate, Prop34.bisect h, area_bac G B E, htri,
      ← area_bac P Q R]

/-- To a given straight line to apply, in a given rectilineal angle, a parallelogram equal to a
given triangle. -/
theorem Prop44 {A B C₁ C₂ C₃ D₁ D D₂ P : Point} (hAB : A ≠ B) (hC : Triangle C₁ C₂ C₃)
    (hD : Triangle D₁ D D₂) (hP : ¬ Collinear A B P) :
    ∃ L M : Point, SameSideOf M P A B ∧ Parallelogram A B M L ∧
      ∠ A B M = ∠ D₁ D D₂ ∧ quadArea A B M L = △ C₁ C₂ C₃ := by
  -- Let AB be the given straight line, C the given triangle and D the given rectilineal angle;
  -- thus it is required to apply to the given straight line AB, in an angle equal to the angle
  -- D, a parallelogram equal to the given triangle C.
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  -- Let the parallelogram BEFG be constructed equal to the triangle C, in the angle EBG which
  -- is equal to D [I. 42];
  obtain ⟨E₀, F₀, G₀, -, -, h42, hang42, harea42⟩ := Prop42 hC hD
  -- let it be placed so that BE is in a straight line with AB;
  /- G goes on the side away from P, so that the complement will stand on P's side. -/
  obtain ⟨X, hXP, -⟩ := exists_oppositeSidesOf (show Triangle A B P from hP) []
  obtain ⟨E, F, G, hABE, hGX, hBEFG, hEBG, harea⟩ := Prop44.place hAB hXP.triangle h42
  have hE_AB : OnLine E AB := on_line_of_between hABE hA_AB hB_AB
  have hBE : B ≠ E := (ne_of_between (between_symm hABE)).symm
  have hBG : B ≠ G := hBEFG.2.2.1.symm
  obtain ⟨BG, hB_BG, hG_BG⟩ := Postulate1 B G hBG
  obtain ⟨EF, hE_EF, hF_EF⟩ := Postulate1 E F hBEFG.2.1
  obtain ⟨FG, hF_FG, hG_FG⟩ := Postulate1 F G hBEFG.1.2.1
  have hAB_FG : Parallel AB FG := hBEFG.1.parallel hB_AB hE_AB hF_FG hG_FG
  have hEF_BG : Parallel EF BG := hBEFG.2.parallel hE_EF hF_EF hG_BG hB_BG
  have hG_AB : ¬ OnLine G AB := hAB_FG.symm.not_onLine hG_FG
  -- let FG be drawn through to H, and let AH be drawn through A parallel to either BG or EF.
  -- [I. 31]
  have hA_BG : ¬ OnLine A BG := fun h =>
    hG_AB ((line_unique hAB.symm hB_BG h hB_AB hA_AB) ▸ hG_BG)
  obtain ⟨AH, hA_AH, hAH_BG⟩ := Prop31.line hA_BG
  have hFG_BG : FG ≠ BG := fun e => hAB_FG.not_onLine hB_AB (e ▸ hB_BG)
  obtain ⟨H, hH_FG, hH_AH⟩ := Prop30.meet hAH_BG hG_BG hG_FG hFG_BG
  have hHGF : Between H G F := hABE.of_sameSide hB_BG (hAH_BG.sameSide hH_AH hA_AH)
    (hEF_BG.sameSide hF_EF hE_EF) hG_BG ⟨FG, hH_FG, hG_FG, hF_FG⟩
  have hAE : A ≠ E := ne_of_between_ends hABE
  have hAH_EF_ne : AH ≠ EF := fun e =>
    hAB_FG.not_onLine ((line_unique hAE hA_AB hE_AB (e ▸ hA_AH) hE_EF) ▸ hF_EF) hF_FG
  have hAH_EF : Parallel AH EF := Prop30.parallel hAH_BG hEF_BG hAH_EF_ne
  have hAH : A ≠ H := fun e => hAB_FG.not_onLine hA_AB (e ▸ hH_FG)
  have hHF : H ≠ F := fun e => hAH_EF.not_onLine hH_AH (e ▸ hF_EF)
  -- Let HB be joined.
  have hHB : H ≠ B := fun e => hAB_FG.not_onLine hB_AB (e ▸ hH_FG)
  obtain ⟨HB, hH_HB, hB_HB⟩ := Postulate1 H B hHB
  -- Then, since the straight line HF falls upon the parallels AH, EF, the angles AHF, HFE are
  -- equal to two right angles. [I. 29]
  have hAE_FG : SameSide A E FG := hAB_FG.sameSide hA_AB hE_AB
  have hAHFE : AreParallel H A F E :=
    AreParallel.of_parallel hAH.symm hBEFG.2.1.symm hH_AH hA_AH hF_EF hE_EF hAH_EF
  have h29 : ∠ A H F + ∠ H F E = ∟ + ∟ :=
    Prop29.interior hAHFE (SameSideOf.of_line hHF hH_FG hF_FG hAE_FG)
  -- Therefore the angles BHG, GFE are less than two right angles;
  have hBE_AH : SameSide B E AH := pasch2 hABE hA_AH (fun h => hAH_BG.not_onLine h hB_BG)
  have hEF_AH : SameSide E F AH := hAH_EF.symm.sameSide hE_EF hF_EF
  have hBF_HA : SameSideOf B F H A :=
    SameSideOf.of_line hAH.symm hH_AH hA_AH (same_side_trans (same_side_symm hBE_AH) hEF_AH)
  have hBA_HF : SameSideOf B A H F :=
    SameSideOf.of_line hHF hH_FG hF_FG (hAB_FG.sameSide hB_AB hA_AB)
  have hAHF : ∠ A H F = ∠ A H B + ∠ B H F := angle_add_of_within hBF_HA hBA_HF
  have hlt : ∠ B H F + ∠ H F E < ∟ + ∟ :=
    calc ∠ B H F + ∠ H F E < (∠ B H F + ∠ H F E) + ∠ A H B :=
          CommonNotion5 hBF_HA.triangle.bac.angle_pos
      _ = ∟ + ∟ := by rw [← h29, hAHF]; ac_rfl
  have hBHG : ∠ B H G = ∠ B H F := angle_onRay_right (OnRay.of_between hHGF) hHB.symm
  have hGFE : ∠ G F E = ∠ H F E := angle_onRay_left (OnRay.of_between (between_symm hHGF)) hBEFG.2.1
  have hlt' : ∠ B H G + ∠ G F E < ∟ + ∟ := by rw [hBHG, hGFE]; exact hlt
  -- and straight lines produced indefinitely from angles less than two right angles meet;
  -- [Post. 5] therefore HB, FE, when produced, will meet.
  have hmeet : ∃ K : Point, OnLine K HB ∧ OnLine K EF ∧ SameSide K B FG :=
    Postulate5 hB_HB hH_HB hH_FG hF_FG hF_EF hE_EF hHF
      (hAB_FG.sameSide hB_AB hE_AB) (by rw [← hBHG, ← hGFE]; exact hlt')
  -- Let them be produced and meet at K;
  obtain ⟨K, hK_HB, hK_EF, hKB⟩ := hmeet
  have hH_AB : ¬ OnLine H AB := hAB_FG.symm.not_onLine hH_FG
  have hH_BG : ¬ OnLine H BG := hAH_BG.not_onLine hH_AH
  have hK_BG : ¬ OnLine K BG := hEF_BG.not_onLine hK_EF
  have hK_FG : ¬ OnLine K FG := not_on_line_of_same_side hKB
  have hK_AB : ¬ OnLine K AB := fun hK => by
    by_cases hKE : K = E
    · subst hKE
      exact hH_AB ((line_unique hBE hB_HB hK_HB hB_AB hK) ▸ hH_HB)
    · exact hAB_FG.not_onLine ((line_unique hKE hK_EF hE_EF hK hE_AB) ▸ hF_EF) hF_FG
  -- through the point K let KL be drawn parallel to either EA or FH, [I. 31]
  obtain ⟨KL, hK_KL, hKL_FG⟩ := Prop31.line hK_FG
  have hKL_AB : Parallel KL AB :=
    Prop30.parallel hKL_FG hAB_FG (fun e => hK_AB (e ▸ hK_KL))
  -- and let HA, GB be produced to the points L, M.
  have hAH_FG : AH ≠ FG := fun e => hAH_BG.not_onLine (e ▸ hG_FG) hG_BG
  obtain ⟨L, hL_AH, hL_KL⟩ := Prop30.meet hKL_FG hH_FG hH_AH hAH_FG
  obtain ⟨M, hM_BG, hM_KL⟩ := Prop30.meet hKL_FG hG_FG hG_BG hFG_BG.symm
  /- The parallels carry the order A, B, E to every crossing straight line. -/
  have hHBK : Between H B K := hHGF.of_sameSide hG_BG (same_side_refl hH_BG)
    (hEF_BG.sameSide hK_EF hF_EF) hB_BG ⟨HB, hH_HB, hB_HB, hK_HB⟩
  have hFEK : Between F E K := hHBK.of_sameSide hB_AB (hAB_FG.symm.sameSide hF_FG hH_FG)
    (same_side_refl hK_AB) hE_AB ⟨EF, hF_EF, hE_EF, hK_EF⟩
  have hKML : Between K M L := (between_symm hHBK).of_sameSide hB_BG (same_side_refl hK_BG)
    (hAH_BG.sameSide hL_AH hH_AH) hM_BG ⟨KL, hK_KL, hM_KL, hL_KL⟩
  have hLAH : Between L A H := (between_symm hHBK).of_sameSide hB_AB
    (hKL_AB.sameSide hL_KL hK_KL) (same_side_refl hH_AB) hA_AB ⟨AH, hL_AH, hA_AH, hH_AH⟩
  have hGBM : Between G B M := hHBK.of_sameSide hB_AB (hAB_FG.symm.sameSide hG_FG hH_FG)
    (hKL_AB.sameSide hM_KL hK_KL) hB_AB ⟨BG, hG_BG, hB_BG, hM_BG⟩
  -- Then HLKF is a parallelogram, HK is its diameter, and AG, ME are parallelograms, and LB,
  -- BF the so-called complements, about HK;
  have hKL : K ≠ L := fun e => hAH_EF.not_onLine (e ▸ hL_AH) hK_EF
  have hLH : L ≠ H := fun e => hKL_FG.not_onLine hL_KL (e ▸ hH_FG)
  have hHG : H ≠ G := fun e => hAH_BG.not_onLine hH_AH (e ▸ hG_BG)
  have hKM : K ≠ M := fun e => hK_BG (e ▸ hM_BG)
  have hMB : M ≠ B := fun e => hKL_AB.not_onLine hM_KL (e ▸ hB_AB)
  have hML : M ≠ L := fun e => hAH_BG.not_onLine (e ▸ hL_AH) hM_BG
  have hLA' : L ≠ A := fun e => hKL_AB.not_onLine hL_KL (e ▸ hA_AB)
  have hHLKF : Parallelogram H L K F :=
    ⟨AreParallel.of_parallel hLH.symm (ne_of_between_ends hFEK).symm
        hH_AH hL_AH hK_EF hF_EF hAH_EF,
      AreParallel.of_parallel hKL.symm hHF.symm hL_KL hK_KL hF_FG hH_FG hKL_FG⟩
  have hHABG : Parallelogram H A B G :=
    ⟨AreParallel.of_parallel hAH.symm hBG hH_AH hA_AH hB_BG hG_BG hAH_BG,
      AreParallel.of_parallel hAB hHG.symm hA_AB hB_AB hG_FG hH_FG hAB_FG⟩
  have hBMKE : Parallelogram B M K E :=
    ⟨AreParallel.of_parallel hMB.symm (ne_of_between (between_symm hFEK))
        hB_BG hM_BG hK_EF hE_EF hEF_BG.symm,
      AreParallel.of_parallel hKM.symm hBE.symm hM_KL hK_KL hE_AB hB_AB hKL_AB⟩
  have hABML : Parallelogram A B M L :=
    ⟨AreParallel.of_parallel hAB hML hA_AB hB_AB hM_KL hL_KL hKL_AB.symm,
      AreParallel.of_parallel hMB.symm hLA' hB_BG hM_BG hL_AH hA_AH hAH_BG.symm⟩
  -- therefore LB is equal to BF. [I. 43]
  have h43 : quadArea A L M B = quadArea G B E F :=
    Prop43 hHLKF hHBK (between_symm hLAH) (between_symm hKML) (between_symm hFEK)
      (between_symm hHGF) hHABG hBMKE
  have hLB_BF : quadArea A B M L = quadArea B E F G := by
    rw [← quadArea_reverse A B M L, h43, quadArea_rotate₂ E F G B, hBEFG.quadArea_rotate]
  -- But BF is equal to the triangle C;
  have hBF_C : quadArea B E F G = △ C₁ C₂ C₃ := harea.trans harea42
  -- therefore LB is also equal to C. [C.N. 1]
  have hLB_C : quadArea A B M L = △ C₁ C₂ C₃ := CommonNotion1 hLB_BF hBF_C.symm
  -- And, since the angle GBE is equal to the angle ABM, [I. 15]
  have hGBE_ABM : ∠ G B E = ∠ A B M := (Prop15 hABE hGBM fun ⟨ℓ, hA_ℓ, hE_ℓ, hG_ℓ⟩ =>
    hG_AB ((line_unique hAE hA_ℓ hE_ℓ hA_AB hE_AB) ▸ hG_ℓ)).2
  -- while the angle GBE is equal to D,
  have hGBE_D : ∠ G B E = ∠ D₁ D D₂ := by
    rw [angle_symm hBG.symm hBE.symm, hEBG, hang42]
  -- the angle ABM is also equal to the angle D.
  have hABM_D : ∠ A B M = ∠ D₁ D D₂ := hGBE_ABM.symm.trans hGBE_D
  -- Therefore the parallelogram LB equal to the given triangle C has been applied to the given
  -- straight line AB, in the angle ABM which is equal to D.
  have hGP : OppositeSidesOf G P A B := hGX.trans_opposite hXP
  have hGM : OppositeSidesOf G M A B :=
    OppositeSidesOf.of_between (Triangle.of_line hA_AB hB_AB hAB hG_AB) hGBM
  exact ⟨L, M, OppositeSidesOf.sameSideOf hGM hGP, hABML, hABM_D, hLB_C⟩
  -- Q. E. F.

end Elements.BookI
