import Elements.BookI.Prop10
import Elements.BookI.Prop23
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop36
import Elements.BookI.Prop38
import Elements.BookI.Prop41
import Elements.BookI.HelpersParallels

namespace Elements.BookI
open Tacit

/-- Throwaway: I.38 as restated, proved along Euclid's route. -/
theorem T38 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hbase : ‖B C‖ = ‖E F‖)
    (hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧
      OnLine B M ∧ OnLine C M ∧ OnLine E M ∧ OnLine F M) :
    △ A B C = △ D E F := by
  obtain ⟨L, M, hLM, hA, hD, hB, hC, hE, hF⟩ := hpar
  -- through B let BG be drawn parallel to CA [I. 31]
  obtain ⟨U, V, hUBV, hUV⟩ := Prop31 hABC.ne₁₃.symm (fun ⟨K, hC_K, hA_K, hB_K⟩ =>
    hABC ⟨K, hA_K, hB_K, hC_K⟩)
  obtain ⟨P, hU_P, hV_P⟩ := Postulate1 U V hUV.1
  obtain ⟨N, hC_N, hA_N⟩ := Postulate1 C A hABC.ne₁₃.symm
  have hB_P : OnLine B P := on_line_of_between_ends hUBV hU_P hV_P
  have hPN : Parallel P N := hUV.parallel hU_P hV_P hC_N hA_N
  have hLN : L ≠ N := fun e => hLM.symm.not_onLine hC (e ▸ hC_N)
  obtain ⟨G, hG_L, hG_P⟩ := Prop30.meet hPN hA_N hA hLN
  have hGBCA : Parallelogram G B C A :=
    ⟨AreParallel.of_parallel (fun e => hLM.symm.not_onLine hB (e ▸ hG_L)) hABC.ne₁₃.symm
        hG_P hB_P hC_N hA_N hPN,
      AreParallel.of_parallel hABC.ne₂₃ (fun e => hPN.not_onLine hG_P (e ▸ hA_N))
        hB hC hA hG_L hLM.symm⟩
  -- and through F let FH be drawn parallel to DE.
  obtain ⟨U', V', hU'FV', hU'V'⟩ := Prop31 hDEF.ne₁₂ (fun ⟨K, hD_K, hE_K, hF_K⟩ =>
    hDEF ⟨K, hD_K, hE_K, hF_K⟩)
  obtain ⟨P', hU'_P', hV'_P'⟩ := Postulate1 U' V' hU'V'.1
  obtain ⟨N', hD_N', hE_N'⟩ := Postulate1 D E hDEF.ne₁₂
  have hF_P' : OnLine F P' := on_line_of_between_ends hU'FV' hU'_P' hV'_P'
  have hP'N' : Parallel P' N' := hU'V'.parallel hU'_P' hV'_P' hD_N' hE_N'
  have hLN' : L ≠ N' := fun e => hLM.symm.not_onLine hE (e ▸ hE_N')
  obtain ⟨H, hH_L, hH_P'⟩ := Prop30.meet hP'N' hD_N' hD hLN'
  have hDEFH : Parallelogram D E F H :=
    ⟨AreParallel.of_parallel hDEF.ne₁₂ (fun e => hLM.symm.not_onLine hF (e ▸ hH_L))
        hD_N' hE_N' hF_P' hH_P' hP'N'.symm,
      AreParallel.of_parallel hDEF.ne₂₃ (fun e => hP'N'.not_onLine hH_P' (e ▸ hD_N'))
        hE hF hH_L hD hLM.symm⟩
  -- GBCA is equal to DEFH [I. 36]
  have h36 : quadArea G B C A = quadArea D E F H :=
    Prop36 hGBCA hDEFH hbase ⟨L, hG_L, hA, hD, hH_L⟩ ⟨M, hB, hC, hE, hF⟩
  -- the diameter AB bisects GBCA [I. 34]; the diameter DF bisects DEFH [I. 34]
  have h₁ : quadArea G B C A = △ B C A + △ B C A := by
    rw [← hGBCA.quadArea_rotate]
    exact Prop34.bisect hGBCA.rotate
  have h₂ : quadArea D E F H = △ D E F + △ D E F := Prop34.bisect hDEFH
  rw [area_bca A B C]
  exact Magnitude.eq_of_add_self_eq (h₁.symm.trans (h36.trans h₂))

/-- Throwaway: I.42 along Euclid's route, citing the restated I.38. -/
theorem T42 {A B C D₁ D D₂ : Point} (hABC : Triangle A B C) (hD : Triangle D₁ D D₂) :
    ∃ E F G : Point, Between B E C ∧ SameSideOf F A B C ∧ Parallelogram F E C G ∧
      ∠ C E F = ∠ D₁ D D₂ ∧ quadArea F E C G = △ A B C := by
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C hABC.ne₂₃
  have hA_BC : ¬ OnLine A BC := hABC.bca.off_line hB hC
  -- Let BC be bisected at E,
  obtain ⟨E, hBEC, hBE⟩ := Prop10 hABC.ne₂₃
  have hE : OnLine E BC := on_line_of_between_ends hBEC hB hC
  have hEC : E ≠ C := (ne_of_between (between_symm hBEC)).symm
  have hECA : ¬ Collinear E C A := fun ⟨K, hE_K, hC_K, hA_K⟩ =>
    hA_BC ((line_unique hEC hE_K hC_K hE hC) ▸ hA_K)
  -- at E on EC, the angle CEF equal to D [I. 23], on A's side
  obtain ⟨C₁, F₁, hC₁, hF₁, hang⟩ := Prop23 hEC hD hECA
  -- through A let AG be drawn parallel to EC [I. 31]
  obtain ⟨U, V, hUAV, hUV⟩ := Prop31 hEC hECA
  obtain ⟨K, hU_K, hV_K⟩ := Postulate1 U V hUV.1
  have hA_K : OnLine A K := on_line_of_between_ends hUAV hU_K hV_K
  have hKBC : Parallel K BC := hUV.parallel hU_K hV_K hE hC
  -- F: where AG meets EF₁
  have hEF₁ : E ≠ F₁ := hF₁.triangle.ne₁₃
  obtain ⟨EF, hE_EF, hF₁_EF⟩ := Postulate1 E F₁ hEF₁
  have hEF_BC : EF ≠ BC := fun e => (hF₁.triangle.off_line hE hC) (e ▸ hF₁_EF)
  obtain ⟨F, hF_EF, hF_K⟩ := Prop30.meet hKBC hE hE_EF hEF_BC
  have hFA : SameSide F A BC := hKBC.sameSide hF_K hA_K
  have hFE : F ≠ E := fun e => hKBC.not_onLine hF_K (e ▸ hE)
  have hFray : OnRay F E F₁ :=
    OnRay.of_sameSideOf ((SameSideOf.of_line hEC hE hC hFA).trans hF₁.symm)
      ⟨EF, hE_EF, hF₁_EF, hF_EF⟩ hFE
  have hCEF : ∠ C E F = ∠ D₁ D D₂ := (angle_eq_of_onRay hC₁.symm hFray).trans hang
  -- through C let CG be drawn parallel to EF
  have hEFC : ¬ Collinear E F C := fun ⟨K', hE_K', hF_K', hC_K'⟩ =>
    hFE ((line_unique hEC hE_K' hC_K' hE hC) ▸ hF_K' |> fun h => absurd h (hKBC.not_onLine hF_K))
  obtain ⟨U', V', hU'CV', hU'V'⟩ := Prop31 hFE.symm hEFC
  obtain ⟨K', hU'_K', hV'_K'⟩ := Postulate1 U' V' hU'V'.1
  have hC_K' : OnLine C K' := on_line_of_between_ends hU'CV' hU'_K' hV'_K'
  have hK'EF : Parallel K' EF := hU'V'.parallel hU'_K' hV'_K' hE_EF hF_EF
  have hK_EF : K ≠ EF := fun e => hKBC.not_onLine (e ▸ hE_EF) hE
  obtain ⟨G, hG_K, hG_K'⟩ := Prop30.meet hK'EF hF_EF hF_K hK_EF
  have hFG : F ≠ G := fun e => hK'EF.not_onLine hG_K' (e ▸ hF_EF)
  have hCG : C ≠ G := fun e => hKBC.not_onLine hG_K (e ▸ hC)
  have hFECG : Parallelogram F E C G :=
    ⟨AreParallel.of_parallel hFE (hCG) hF_EF hE_EF hC_K' hG_K' hK'EF.symm,
      AreParallel.of_parallel hEC hFG.symm hE hC hG_K hF_K hKBC.symm⟩
  -- the triangle ABE is equal to the triangle AEC [I. 38]
  have hABE : Triangle A B E :=
    Triangle.of_line hB hE (ne_of_between hBEC) hA_BC |>.cab
  have hAEC : Triangle A E C := Triangle.of_line hE hC hEC hA_BC |>.cab
  have h38 : △ A B E = △ A E C :=
    Prop38 hABE hAEC hBE ⟨K, BC, hKBC, hA_K, hA_K, hB, hE, hE, hC⟩
  -- FECG is double of AEC [I. 41]
  have h41 : quadArea F E C G = △ E A C + △ E A C := Prop41 hFECG ⟨K, hF_K, hG_K, hA_K⟩
  refine ⟨E, F, G, hBEC, SameSideOf.of_line hABC.ne₂₃ hB hC hFA, hFECG, hCEF, ?_⟩
  rw [h41, ← area_cut (A := A) hBEC, h38, ← area_bac A E C]

end Elements.BookI
