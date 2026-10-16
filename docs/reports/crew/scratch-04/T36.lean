import Elements.BookI.Prop33
import Elements.BookI.Prop34
import Elements.BookI.Prop35
import Elements.BookI.Prop43
import Elements.BookI.HelpersParallels

namespace Elements.BookI
open Tacit

/-- Throwaway: I.36, with the orientation split. -/
theorem T36 {A B C D E F G H : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E F G H)
    (hbase : ‖B C‖ = ‖F G‖)
    (hAH : ∃ L : Line, OnLine A L ∧ OnLine D L ∧ OnLine E L ∧ OnLine H L)
    (hBG : ∃ L : Line, OnLine B L ∧ OnLine C L ∧ OnLine F L ∧ OnLine G L) :
    quadArea A B C D = quadArea E F G H := by
  obtain ⟨L, hA, hD, hE, hH⟩ := hAH
  obtain ⟨M, hB, hC, hF, hG⟩ := hBG
  have hLM : Parallel L M := (h₁.2.parallel hB hC hD hA).symm
  have key : ∀ {E F G H : Point}, Parallelogram E F G H → ‖B C‖ = ‖F G‖ → OnLine E L →
      OnLine H L → OnLine F M → OnLine G M → SameSideOf C H B E →
      quadArea A B C D = quadArea E F G H := by
    intro E F G H h₂ hbase hE hH hF hG hdir
    have hEH : ‖E H‖ = ‖F G‖ := (Prop34 (A := E) (B := H) (C := F) (D := G) h₂).1
    have hpar : AreParallel B C E H :=
      AreParallel.of_parallel h₁.2.1 h₂.2.2.1.symm hB hC hE hH hLM.symm
    obtain ⟨-, h33⟩ := Prop33 hpar (hbase.trans hEH.symm) hdir
    have hEBCH : Parallelogram E B C H :=
      ⟨h33.swap_left, AreParallel.of_parallel h₁.2.1 h₂.2.2.1 hB hC hH hE hLM.symm⟩
    have e₁ : quadArea A B C D = quadArea E B C H := Prop35 h₁ hEBCH ⟨L, hA, hD, hE, hH⟩
    have e₂ : quadArea F E H G = quadArea B E H C :=
      Prop35 h₂.reverse.rotate.rotate.rotate hEBCH.reverse.rotate.rotate.rotate
        ⟨M, hF, hG, hB, hC⟩
    rw [e₁, ← hEBCH.quadArea_rotate, quadArea_reverse B E H C, ← e₂, quadArea_reverse F G H E,
      h₂.quadArea_rotate]
  have hEHBC : AreParallel E H B C :=
    AreParallel.of_parallel h₂.2.2.1.symm h₁.2.1 hE hH hB hC hLM
  rcases hEHBC.sameSideOf_or with hs | hs
  · exact key h₂ hbase hE hH hF hG hs.swap
  · rw [key h₂.reverse.rotate (hbase.trans (len_symm F G)) hH hE hG hF hs.swap,
      quadArea_reverse, quadArea_rotate₂, h₂.quadArea_rotate]

/-- Throwaway: the area algebra of I.43. -/
theorem T43 {A B C D E F G H K : Point} (hABCD : Parallelogram A B C D) (hK : Between A K C)
    (hE : Between A E B) (hG : Between B G C) (hF : Between C F D) (hH : Between D H A)
    (hEH : Parallelogram A E K H) (hFG : Parallelogram K G C F)
    (hEBGK : Parallelogram E B G K) (hHKFD : Parallelogram H K F D) :
    quadArea E B G K = quadArea H K F D := by
  -- the triangle ABC is equal to the triangle ACD [I. 34]
  have t₁ : △ B A C = △ D C A := (Prop34 (A := B) (B := A) (C := C) (D := D) hABCD.rotate).2.2.2.2
  -- the triangle AEK is equal to the triangle AHK
  have t₂ : △ E A K = △ H K A := (Prop34 (A := E) (B := A) (C := K) (D := H) hEH.rotate).2.2.2.2
  -- the triangle KFC is equal to KGC
  have t₃ : △ G K C = △ F C K := (Prop34 (A := G) (B := K) (C := C) (D := F) hFG.rotate).2.2.2.2
  -- the whole triangle ABC, and the whole ADC, cut into pieces
  have w₁ : △ B A C = △ E A K + quadArea E B G K + △ G K C := by
    rw [← hEBGK.quadArea_rotate]
    unfold quadArea
    rw [← area_cut (A := B) hK, area_cba B A K, ← area_cut (A := K) hE, area_bac B K C,
      ← area_cut (A := K) hG, area_cba K A E, area_cab K E B, area_bca K B G, area_bac K G C]
    ac_rfl
  have w₂ : △ D C A = △ H K A + quadArea H K F D + △ F C K := by
    rw [← hHKFD.quadArea_rotate]
    unfold quadArea
    rw [← area_cut (A := D) (between_symm hK), area_cba D C K, ← area_cut (A := K) hF,
      area_bac D K A, ← area_cut (A := K) hH, area_cba K C F, area_bac K H A]
    ac_rfl
  -- therefore the complement BK which remains is equal to the complement KD [C.N. 3]
  have hall := w₁.symm.trans (t₁.trans w₂)
  rw [t₂, t₃] at hall
  refine CommonNotion3 (c := △ H K A + △ F C K) (d := △ H K A + △ F C K) ?_ rfl
  calc quadArea E B G K + (△ H K A + △ F C K)
      = △ H K A + quadArea E B G K + △ F C K := by ac_rfl
    _ = △ H K A + quadArea H K F D + △ F C K := hall
    _ = quadArea H K F D + (△ H K A + △ F C K) := by ac_rfl

end Elements.BookI
