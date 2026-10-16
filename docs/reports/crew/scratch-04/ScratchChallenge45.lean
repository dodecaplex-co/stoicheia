import Elements.BookI.Prop14
import Elements.BookI.Prop33
import Elements.BookI.Prop34
import Elements.BookI.Prop42
import Elements.BookI.Prop44
import Elements.BookI.HelpersParallels

namespace Elements.BookI
open Tacit

/-- Throwaway: I.45 against its statement, citing I.42 and I.44 as stated. -/
theorem X45 {A B C D E₁ E E₂ : Point} (hABD : Triangle A B D) (hDBC : Triangle D B C)
    (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = △ A B D + △ D B C := by
  /- FH equal to ABD, in the angle HKF equal to E [I. 42]; its corner H is D. -/
  obtain ⟨K, F, G, -, -, hFKHG, hHKF, harea₁⟩ := Prop42 hABD hE
  have hGHK : Triangle G D K := hFKHG.1.symm.swap_right.triangle.bac
  obtain ⟨P, hPK, -⟩ := exists_oppositeSidesOf hGHK []
  /- GM equal to DBC applied to GH, in the angle GHM equal to E [I. 44] -/
  obtain ⟨L, M, hMP, hGHML, hGHM, harea₂⟩ := Prop44 hGHK.ne₁₂ hDBC hE hPK.triangle
  have hMK : OppositeSidesOf M K G D := hMP.trans_opposite hPK
  /- FKH, KHG are two right angles [I. 29]; so KH is in a straight line with HM [I. 14] -/
  have hFG_KH : SameSideOf F G K D := hFKHG.rotate.sameSideOf.symm
  have h29a : ∠ F K D + ∠ K D G = ∟ + ∟ := Prop29.interior hFKHG.1.swap_left hFG_KH
  have hKD : K ≠ D := hFG_KH.1
  have hGD : G ≠ D := hGHK.ne₁₂
  have hFK : F ≠ K := hFKHG.1.1
  have hKHM : Between K D M := Prop14 hMK.symm (by
    rw [angle_symm hGD hKD, hGHM, ← hHKF, angle_symm hKD.symm hFK, add_comm]
    exact h29a)
  /- MHG, HGF alternate [I. 29]; MHG, HGL two right angles [I. 29]; FG in a straight
     line with GL [I. 14] -/
  have hFK_HG : SameSideOf F K D G := hFKHG.rotate.rotate.sameSideOf
  have hMD : M ≠ D := (ne_of_between (between_symm hKHM))
  obtain ⟨KM, hK_KM, hM_KM⟩ := Postulate1 K M (ne_of_between_ends hKHM)
  have hD_KM : OnLine D KM := on_line_of_between_ends hKHM hK_KM hM_KM
  obtain ⟨FG, hF_FG, hG_FG⟩ := Postulate1 F G hFKHG.2.2.1.symm
  have hKM_FG : Parallel KM FG := hFKHG.2.parallel hK_KM hD_KM hG_FG hF_FG
  have hMHGF : AreParallel M D G F :=
    AreParallel.of_parallel hMD hFKHG.2.2.1 hM_KM hD_KM hG_FG hF_FG hKM_FG
  have hMF : OppositeSidesOf M F D G := (hFK_HG.trans_opposite hMK.symm.swap).symm
  have h29b : ∠ M D G = ∠ D G F := Prop29.alternate hMHGF hMF
  have hML_HG : SameSideOf M L D G := hGHML.sameSideOf.swap
  have h29c : ∠ M D G + ∠ D G L = ∟ + ∟ := Prop29.interior hGHML.2.swap_right hML_HG
  have hFL : OppositeSidesOf F L D G :=
    (hFK_HG.trans_opposite (hML_HG.symm.trans_opposite hMK.swap).symm).symm.symm
  have hFGL : Between F G L := Prop14 hFL (by
    rw [← h29b]
    exact h29c)
  /- KF equal and parallel to ML [I. 34, I. 30]; KM, FL equal and parallel [I. 33] -/
  have h34a := Prop34 (A := F) (B := G) (C := K) (D := D) hFKHG
  have h34b := Prop34 (A := G) (B := L) (C := D) (D := M) hGHML
  obtain ⟨KF, hK_KF, hF_KF⟩ := Postulate1 K F hFK.symm
  obtain ⟨ML, hM_ML, hL_ML⟩ := Postulate1 M L hGHML.1.2.1
  obtain ⟨GD, hG_GD, hD_GD⟩ := Postulate1 G D hGD
  have hKF_GD : Parallel KF GD := hFKHG.1.swap_left.parallel hK_KF hF_KF hD_GD hG_GD
  have hML_GD : Parallel ML GD := hGHML.1.symm.parallel hM_ML hL_ML hG_GD hD_GD
  have hKF_ML : KF ≠ ML := fun e => by
    have hK_ML : OnLine K ML := e ▸ hK_KF
    have : ML = KM := line_unique (ne_of_between_ends hKHM) hK_ML hM_ML hK_KM hM_KM
    exact hML_GD.not_onLine (this ▸ hD_KM) hD_GD
  have hpar : AreParallel K F M L :=
    AreParallel.of_parallel hFK.symm hGHML.1.2.1 hK_KF hF_KF hM_ML hL_ML
      (Prop30.parallel hKF_GD hML_GD hKF_ML)
  have hlen : ‖K F‖ = ‖M L‖ := by
    rw [len_symm K F, h34a.2.1, h34b.2.1, len_symm L M]
  have hdir : SameSideOf F L K M := by
    have hF : SameSide F G KM := hFG_KH.sameSide hK_KM hD_KM
    have hL : SameSide L G KM := hGHML.rotate.sameSideOf.sameSide hD_KM hM_KM
    exact SameSideOf.of_line (ne_of_between_ends hKHM) hK_KM hM_KM
      (same_side_trans (same_side_symm hF) (same_side_symm hL))
  obtain ⟨-, h33⟩ := Prop33 hpar hlen hdir
  /- Therefore KFLM is a parallelogram. -/
  have hKFLM : Parallelogram K F L M := ⟨hpar.swap_right, h33.symm.swap_right⟩
  refine ⟨K, F, L, M, hKFLM, ?_, ?_⟩
  · rw [angle_onRay_right (OnRay.of_beyond hKHM) hFK, angle_symm hFK hKD.symm]
    exact hHKF
  · rw [quadArea_add_of_parallelograms hFKHG.rotate.reverse hGHML.rotate.reverse hKHM hFGL,
      quadArea_reverse K D G F, hFKHG.quadArea_rotate, harea₁,
      quadArea_reverse D M L G, hGHML.quadArea_rotate, harea₂]

end Elements.BookI
