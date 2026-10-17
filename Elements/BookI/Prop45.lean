import Elements.Figure.Basics
import Elements.BookI.Prop14
import Elements.BookI.Prop29
import Elements.BookI.Prop30
import Elements.BookI.Prop33
import Elements.BookI.Prop34
import Elements.BookI.Prop42
import Elements.BookI.Prop44
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 45

Euclid's text, in Heath's translation: [`heath/I/45.md`](../../heath/I/45.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- To construct, in a given rectilineal angle, a parallelogram equal to a given rectilineal figure. -/
theorem Prop45 {A B C D E₁ E E₂ : Point} (hABD : Triangle A B D) (hDBC : Triangle D B C)
    (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = △ A B D + △ D B C := by
  -- Let ABCD be the given rectilineal figure and E the given rectilineal angle; thus it is
  -- required to construct, in the given angle E, a parallelogram equal to the rectilineal
  -- figure ABCD.
  -- Let DB be joined, and let the parallelogram FH be constructed equal to the triangle ABD,
  -- in the angle HKF which is equal to E; [I. 42] let the parallelogram GM equal to the
  -- triangle DBC be applied to the straight line GH, in the angle GHM which is equal to
  -- E. [I. 44]
  /- I.42 builds on half of the triangle's own base, so KH lies along BD and H
     falls on D: the Lean writes D wherever Euclid writes H, and in our figure KFLM
     overlaps ABCD. K lies between B and D, and F is on A's side of BD. -/
  obtain ⟨K, F, G, hBKD, hFA, hFKHG, hHKF, hFH⟩ := Prop42 hABD hE
  have hGHK : Triangle G D K := hFKHG.1.symm.swap_right.triangle.bac
  /- I.44's point for the side is taken across GH from K, so that KH and HM are
     "not lying on the same side", as I.14 will ask. -/
  obtain ⟨P, hPK, -⟩ := exists_oppositeSidesOf hGHK []
  obtain ⟨L, M, hMP, hGHML, hGHM, hGM⟩ := Prop44 hGHK.ne₁₂ hDBC hE hPK.triangle
  have hMK : OppositeSidesOf M K G D := hMP.trans_opposite hPK
  have hKD : K ≠ D := hGHK.ne₂₃.symm
  have hGD : G ≠ D := hGHK.ne₁₂
  have hFK : F ≠ K := hFKHG.1.1
  -- Then, since the angle E is equal to each of the angles HKF, GHM, the angle HKF is also
  -- equal to the angle GHM. [C.N. 1]
  have hHKF_GHM : ∠ D K F = ∠ G D M := CommonNotion1 hHKF hGHM
  -- Let the angle KHG be added to each; therefore the angles FKH, KHG are equal to the angles
  -- KHG, GHM.
  have hsum₁ : ∠ F K D + ∠ K D G = ∠ K D G + ∠ G D M := by
    rw [angle_symm hFK hKD.symm, hHKF_GHM, add_comm]
  -- But the angles FKH, KHG are equal to two right angles; [I. 29] therefore the angles KHG,
  -- GHM are also equal to two right angles.
  have hFG_KH : SameSideOf F G K D := hFKHG.rotate.sameSideOf.symm
  have h29a : ∠ F K D + ∠ K D G = ∟ + ∟ := Prop29.interior hFKHG.1.swap_left hFG_KH
  have hKHG_GHM : ∠ K D G + ∠ G D M = ∟ + ∟ := hsum₁.symm.trans h29a
  -- Thus, with a straight line GH, and at the point H on it, two straight lines KH, HM not
  -- lying on the same side make the adjacent angles equal to two right angles; therefore KH is
  -- in a straight line with HM. [I. 14]
  have hKHM : Between K D M := Prop14 hMK.symm (by
    rw [angle_symm hGD hKD]
    exact hKHG_GHM)
  -- And, since the straight line HG falls upon the parallels KM, FG, the alternate angles MHG,
  -- HGF are equal to one another. [I. 29]
  have hFK_HG : SameSideOf F K D G := hFKHG.rotate.rotate.sameSideOf
  have hMD : M ≠ D := ne_of_between (between_symm hKHM)
  obtain ⟨KM, hK_KM, hM_KM⟩ := Postulate1 K M (ne_of_between_ends hKHM)
  have hD_KM : OnLine D KM := on_line_of_between_ends hKHM hK_KM hM_KM
  obtain ⟨FG, hF_FG, hG_FG⟩ := Postulate1 F G hFKHG.2.2.1.symm
  have hKM_FG : Parallel KM FG := hFKHG.2.parallel hK_KM hD_KM hG_FG hF_FG
  have hMHGF : AreParallel M D G F :=
    AreParallel.of_parallel hMD hFKHG.2.2.1 hM_KM hD_KM hG_FG hF_FG hKM_FG
  have hMF : OppositeSidesOf M F D G := (hFK_HG.trans_opposite hMK.symm.swap).symm
  have hMHG_HGF : ∠ M D G = ∠ D G F := Prop29.alternate hMHGF hMF
  -- Let the angle HGL be added to each; therefore the angles MHG, HGL are equal to the angles
  -- HGF, HGL. [C.N. 2]
  have hsum₂ : ∠ M D G + ∠ D G L = ∠ D G F + ∠ D G L := CommonNotion2 hMHG_HGF rfl
  -- But the angles MHG, HGL are equal to two right angles; [I. 29] therefore the angles HGF,
  -- HGL are also equal to two right angles. [C.N. 1]
  have hML_HG : SameSideOf M L D G := hGHML.sameSideOf.swap
  have h29c : ∠ M D G + ∠ D G L = ∟ + ∟ := Prop29.interior hGHML.2.swap_right hML_HG
  have hHGF_HGL : ∠ D G F + ∠ D G L = ∟ + ∟ := CommonNotion1 hsum₂.symm h29c.symm
  -- Therefore FG is in a straight line with GL. [I. 14]
  have hFL : OppositeSidesOf F L D G :=
    hFK_HG.trans_opposite (hML_HG.symm.trans_opposite hMK.swap).symm
  have hFGL : Between F G L := Prop14 hFL hHGF_HGL
  -- And, since FK is equal and parallel to HG, [I. 34] and HG to ML also, KF is also equal and
  -- parallel to ML; [C.N. 1; I. 30] and the straight lines KM, FL join them (at their
  -- extremities); therefore KM, FL are also equal and parallel. [I. 33]
  obtain ⟨-, hFK_GH, -, -, -⟩ := Prop34 (A := F) (B := G) (C := K) (D := D) hFKHG
  obtain ⟨-, hGH_LM, -, -, -⟩ := Prop34 (A := G) (B := L) (C := D) (D := M) hGHML
  have hlen : ‖K F‖ = ‖M L‖ :=
    CommonNotion1 ((len_symm K F).trans hFK_GH) (hGH_LM.trans (len_symm L M)).symm
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
  have hdir : SameSideOf F L K M := by
    have hF : SameSide F G KM := hFG_KH.sameSide hK_KM hD_KM
    have hL : SameSide L G KM := hGHML.rotate.sameSideOf.sameSide hD_KM hM_KM
    exact SameSideOf.of_line (ne_of_between_ends hKHM) hK_KM hM_KM
      (same_side_trans (same_side_symm hF) (same_side_symm hL))
  obtain ⟨-, h33⟩ := Prop33 hpar hlen hdir
  -- Therefore KFLM is a parallelogram.
  have hKFLM : Parallelogram K F L M := ⟨hpar.swap_right, h33.symm.swap_right⟩
  -- And, since the triangle ABD is equal to the parallelogram FH, and DBC to GM, the whole
  -- rectilineal figure ABCD is equal to the whole parallelogram KFLM.
  have hwhole : quadArea K F L M = △ A B D + △ D B C := by
    rw [quadArea_add_of_parallelograms hFKHG.rotate.reverse hGHML.rotate.reverse hKHM hFGL,
      quadArea_reverse K D G F, hFKHG.quadArea_rotate, hFH,
      quadArea_reverse D M L G, hGHML.quadArea_rotate, hGM]
  -- Therefore the parallelogram KFLM has been constructed equal to the given rectilineal
  -- figure ABCD, in the angle FKM which is equal to the given angle E.
  refine ⟨K, F, L, M, hKFLM, ?_, hwhole⟩
  rw [angle_onRay_right (OnRay.of_beyond hKHM) hFK, angle_symm hFK hKD.symm]
  exact hHKF
  -- Q. E. F.

end Elements.BookI
