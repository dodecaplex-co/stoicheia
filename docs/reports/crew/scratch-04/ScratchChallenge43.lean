import Elements.BookI.Prop34
import Elements.BookI.HelpersParallels

namespace Elements.BookI
open Tacit

/-- Throwaway: the complements of I.43 are parallelograms, from I.43's hypotheses alone. -/
theorem X43 {A B C D E F G H K : Point} (hABCD : Parallelogram A B C D) (hK : Between A K C)
    (hE : Between A E B) (hG : Between B G C) (hF : Between C F D) (hH : Between D H A)
    (hEH : Parallelogram A E K H) (hFG : Parallelogram K G C F) :
    Parallelogram E B G K ∧ Parallelogram H K F D := by
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hABCD.1.1
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hABCD.1.2.1
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABCD.2.1
  obtain ⟨DA, hD_DA, hA_DA⟩ := Postulate1 D A hABCD.2.2.1
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C (ne_of_between_ends hK)
  have hK_AC : OnLine K AC := on_line_of_between_ends hK hA_AC hC_AC
  have hE_AB : OnLine E AB := on_line_of_between_ends hE hA_AB hB_AB
  have hG_BC : OnLine G BC := on_line_of_between_ends hG hB_BC hC_BC
  have hF_CD : OnLine F CD := on_line_of_between_ends hF hC_CD hD_CD
  have hH_DA : OnLine H DA := on_line_of_between_ends hH hD_DA hA_DA
  have hAB_CD : Parallel AB CD := hABCD.1.parallel hA_AB hB_AB hC_CD hD_CD
  have hBC_DA : Parallel BC DA := hABCD.2.parallel hB_BC hC_BC hD_DA hA_DA
  have hC_AB : ¬ OnLine C AB := hAB_CD.symm.not_onLine hC_CD
  have hA_BC : ¬ OnLine A BC := hBC_DA.symm.not_onLine hA_DA
  have hK_AB : ¬ OnLine K AB := fun h =>
    hC_AB (on_line_of_between hK hA_AB h)
  have hK_BC : ¬ OnLine K BC := fun h =>
    hA_BC (on_line_of_between (between_symm hK) hC_BC h)
  have hK_CD : ¬ OnLine K CD := fun h =>
    hAB_CD.not_onLine hA_AB (on_line_of_between (between_symm hK) hC_CD h)
  have hK_DA : ¬ OnLine K DA := fun h =>
    hBC_DA.not_onLine hC_BC (on_line_of_between hK hA_DA h)
  /- the straight lines KG, KE, KH, KF of the two parallelograms about the diameter -/
  obtain ⟨KG, hK_KG, hG_KG⟩ := Postulate1 K G hFG.1.1
  obtain ⟨KE, hK_KE, hE_KE⟩ := Postulate1 K E hEH.2.1.symm
  obtain ⟨KH, hK_KH, hH_KH⟩ := Postulate1 K H hEH.1.2.1
  obtain ⟨KF, hK_KF, hF_KF⟩ := Postulate1 K F hFG.2.2.1.symm
  have hKG_CD : Parallel KG CD := hFG.1.parallel hK_KG hG_KG hC_CD hF_CD
  have hKE_DA : Parallel KE DA :=
    hEH.2.swap_left.parallel hK_KE hE_KE hH_DA hA_DA
  have hKH_AB : Parallel KH AB := hEH.1.symm.parallel hK_KH hH_KH hA_AB hE_AB
  have hKF_BC : Parallel KF BC := hFG.2.symm.swap_left.parallel hK_KF hF_KF hG_BC hC_BC
  /- by I.30, each is parallel to the side it runs beside -/
  have h₁ : Parallel AB KG := Prop30.parallel hAB_CD hKG_CD (fun e => hK_AB (e ▸ hK_KG))
  have h₂ : Parallel BC KE := Prop30.parallel hBC_DA hKE_DA (fun e => hK_BC (e ▸ hK_KE))
  have h₃ : Parallel KH CD := Prop30.parallel hKH_AB hAB_CD.symm (fun e => hK_CD (e ▸ hK_KH))
  have h₄ : Parallel KF DA := Prop30.parallel hKF_BC hBC_DA.symm (fun e => hK_DA (e ▸ hK_KF))
  exact ⟨⟨AreParallel.of_parallel (ne_of_between (between_symm hE)).symm hFG.1.1.symm
        hE_AB hB_AB hG_KG hK_KG h₁,
      AreParallel.of_parallel (ne_of_between hG) hEH.2.1.symm hB_BC hG_BC hK_KE hE_KE h₂⟩,
    ⟨AreParallel.of_parallel hEH.1.2.1.symm (ne_of_between (between_symm hF)).symm
        hH_KH hK_KH hF_CD hD_CD h₃,
      AreParallel.of_parallel hFG.2.2.1.symm (ne_of_between hH) hK_KF hF_KF hD_DA hH_DA h₄⟩⟩

end Elements.BookI
