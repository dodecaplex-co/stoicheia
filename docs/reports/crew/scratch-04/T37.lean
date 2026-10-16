import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop35
import Elements.BookI.Prop37
import Elements.BookI.HelpersParallels

namespace Elements.BookI
open Tacit

/-- Throwaway: I.37 as restated, proved along Euclid's route (I.31, I.35, I.34), with
no case split: "AD" is the parallel `L`, and `E`, `F` are taken on it. -/
theorem T37 {A B C D : Point} (hABC : Triangle A B C) (hDBC : Triangle D B C)
    (hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧ OnLine B M ∧ OnLine C M) :
    △ A B C = △ D B C := by
  obtain ⟨L, M, hLM, hA, hD, hB, hC⟩ := hpar
  -- through B let BE be drawn parallel to CA [I. 31]
  obtain ⟨U, V, hUBV, hUV⟩ := Prop31 hABC.ne₁₃.symm (fun ⟨K, hC_K, hA_K, hB_K⟩ =>
    hABC ⟨K, hA_K, hB_K, hC_K⟩)
  obtain ⟨P, hU_P, hV_P⟩ := Postulate1 U V hUV.1
  obtain ⟨N, hC_N, hA_N⟩ := Postulate1 C A hABC.ne₁₃.symm
  have hB_P : OnLine B P := on_line_of_between_ends hUBV hU_P hV_P
  have hPN : Parallel P N := hUV.parallel hU_P hV_P hC_N hA_N
  have hLN : L ≠ N := fun e => hLM.symm.not_onLine hC (e ▸ hC_N)
  obtain ⟨E, hE_L, hE_P⟩ := Prop30.meet hPN hA_N hA hLN
  have hEBCA : Parallelogram E B C A :=
    ⟨AreParallel.of_parallel (fun e => hLM.symm.not_onLine hB (e ▸ hE_L)) hABC.ne₁₃.symm
        hE_P hB_P hC_N hA_N hPN,
      AreParallel.of_parallel hABC.ne₂₃ (fun e => hPN.not_onLine hE_P (e ▸ hA_N))
        hB hC hA hE_L hLM.symm⟩
  -- and through C let CF be drawn parallel to BD [I. 31]
  obtain ⟨U', V', hU'CV', hU'V'⟩ := Prop31 hDBC.ne₁₂ hDBC
  obtain ⟨P', hU'_P', hV'_P'⟩ := Postulate1 U' V' hU'V'.1
  obtain ⟨N', hD_N', hB_N'⟩ := Postulate1 D B hDBC.ne₁₂
  have hC_P' : OnLine C P' := on_line_of_between_ends hU'CV' hU'_P' hV'_P'
  have hP'N' : Parallel P' N' := hU'V'.parallel hU'_P' hV'_P' hD_N' hB_N'
  have hLN' : L ≠ N' := fun e => hLM.symm.not_onLine hB (e ▸ hB_N')
  obtain ⟨F, hF_L, hF_P'⟩ := Prop30.meet hP'N' hD_N' hD hLN'
  have hDBCF : Parallelogram D B C F :=
    ⟨AreParallel.of_parallel hDBC.ne₁₂ (fun e => hLM.symm.not_onLine hC (e ▸ hF_L))
        hD_N' hB_N' hC_P' hF_P' hP'N'.symm,
      AreParallel.of_parallel hDBC.ne₂₃ (fun e => hP'N'.not_onLine hF_P' (e ▸ hD_N'))
        hB hC hF_L hD hLM.symm⟩
  -- EBCA, DBCF are equal [I. 35]
  have h35 : quadArea E B C A = quadArea D B C F := Prop35 hEBCA hDBCF ⟨L, hE_L, hA, hD, hF_L⟩
  -- the diameter AB bisects EBCA [I. 34]; the diameter DC bisects DBCF [I. 34]
  have h₁ : quadArea E B C A = △ B C A + △ B C A := by
    rw [← hEBCA.quadArea_rotate]
    exact Prop34.bisect hEBCA.rotate
  have h₂ : quadArea D B C F = △ D B C + △ D B C := Prop34.bisect hDBCF
  -- the halves of equal things are equal
  rw [area_bca A B C]
  exact Magnitude.eq_of_add_self_eq (h₁.symm.trans (h35.trans h₂))

/-- Throwaway: I.41 citing the restated I.37; no case for `E` at `A`. -/
theorem T41 {A B C D E : Point} (hABCD : Parallelogram A B C D) (hE : Collinear A D E) :
    quadArea A B C D = △ B E C + △ B E C := by
  obtain ⟨K, hA_K, hD_K, hE_K⟩ := hE
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C hABCD.2.1
  have hKBC : Parallel K BC := (hABCD.2.parallel hB hC hD_K hA_K).symm
  have hEBC : Triangle E B C := (Triangle.of_line hB hC hABCD.2.1 (hKBC.not_onLine hE_K)).cab
  -- the triangle ABC is equal to the triangle EBC [I. 37]
  have h37 : △ A B C = △ E B C := Prop37 hABCD.triangle hEBC ⟨K, BC, hKBC, hA_K, hE_K, hB, hC⟩
  -- the diameter AC bisects ABCD [I. 34]
  rw [Prop34.bisect hABCD, h37, area_bac E B C]

/-- Throwaway: I.39 citing the restated I.37; no case for `E` at `A`. -/
theorem T39 {A B C D : Point} (hABC : Triangle A B C) (hDBC : Triangle D B C)
    (heq : △ A B C = △ D B C) (hside : SameSideOf A D B C) (hAD : A ≠ D) :
    AreParallel A D B C := by
  refine Classical.byContradiction fun hnot => ?_
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C hABC.ne₂₃
  -- let AE be drawn through A parallel to BC [I. 31]
  obtain ⟨U, V, hUAV, hUV⟩ := Prop31 hABC.ne₂₃ hABC.bca
  obtain ⟨K, hU_K, hV_K⟩ := Postulate1 U V hUV.1
  have hA_K : OnLine A K := on_line_of_between_ends hUAV hU_K hV_K
  have hKBC : Parallel K BC := hUV.parallel hU_K hV_K hB hC
  /- `E`: where `AE` meets `BD` (`Prop30.meet`) -/
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hDBC.ne₁₂.symm
  have hD_BC : ¬ OnLine D BC := hDBC.bca.off_line hB hC
  have hBD_BC : BD ≠ BC := fun e => hD_BC (e ▸ hD_BD)
  obtain ⟨E, hE_BD, hE_K⟩ := Prop30.meet hKBC hB hB_BD hBD_BC
  have hED : E ≠ D := fun e =>
    hnot (AreParallel.of_parallel hAD hABC.ne₂₃ hA_K (e ▸ hE_K) hB hC hKBC)
  have hE_BC : ¬ OnLine E BC := hKBC.not_onLine hE_K
  have hEBC : Triangle E B C := (Triangle.of_line hB hC hABC.ne₂₃ hE_BC).cab
  -- the triangle ABC is equal to the triangle EBC [I. 37]
  have h37 : △ A B C = △ E B C := Prop37 hABC hEBC ⟨K, BC, hKBC, hA_K, hE_K, hB, hC⟩
  -- DBC is also equal to EBC [C.N. 1]
  have h1 : △ D B C = △ E B C := CommonNotion1 heq.symm h37.symm
  /- `E` lies on the ray from `B` through `D` -/
  have hEB : E ≠ B := fun e => hE_BC (e ▸ hB)
  have hED_side : SameSideOf E D B C :=
    (SameSideOf.of_line hABC.ne₂₃ hB hC (hKBC.sameSide hE_K hA_K)).trans hside
  have hray : OnRay E B D := OnRay.of_sameSideOf hED_side ⟨BD, hB_BD, hD_BD, hE_BD⟩ hEB
  -- the greater to the less
  rcases lt_trichotomy ‖B E‖ ‖B D‖ with hlt | heq' | hgt
  · have hBED : Between B E D :=
      hray.between_of_len_lt (OnRay.self hDBC.ne₁₂.symm) hlt
    have := area_lt_of_cut hDBC.cba hBED
    rw [← area_cba E B C, ← area_cba D B C, h1] at this
    exact Magnitude.ne_of_lt this rfl
  · exact hED (hray.eq_of_len_eq heq')
  · have hBDE : Between B D E :=
      (OnRay.self hDBC.ne₁₂.symm).between_of_len_lt hray hgt
    have := area_lt_of_cut hEBC.cba hBDE
    rw [← area_cba E B C, ← area_cba D B C, h1] at this
    exact Magnitude.ne_of_lt this rfl

end Elements.BookI
