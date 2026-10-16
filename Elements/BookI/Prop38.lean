import Elements.Figure.Basics
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop36
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 38

Euclid's text, in Heath's translation: [`heath/I/38.md`](../../heath/I/38.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

"In the same parallels BF, AD": two parallel straight lines, one through the
vertices `A` and `D`, the other through the bases `BC` and `EF`. The two vertices
may be one point, as when I.42 cites this for the triangles `ABE` and `AEC`. So
under "let AD be produced in both directions to G, H", "AD" is the parallel
through the vertices itself, and `G` and `H` are taken on it.
-/

namespace Elements.BookI

open Tacit

/-- Triangles which are on equal bases and in the same parallels are equal to one another. -/
theorem Prop38 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hbase : ‖B C‖ = ‖E F‖)
    (hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧
      OnLine B M ∧ OnLine C M ∧ OnLine E M ∧ OnLine F M) :
    △ A B C = △ D E F := by
  -- Let ABC, DEF be triangles on equal bases BC, EF and in the same parallels BF, AD;
  obtain ⟨AD, BF, hAD_BF, hA, hD, hB, hC, hE, hF⟩ := hpar
  -- I say that the triangle ABC is equal to the triangle DEF.
  -- For let AD be produced in both directions to G, H; through B let BG be drawn parallel to
  -- CA, [I. 31] and through F let FH be drawn parallel to DE.
  obtain ⟨CA, hC_CA, hA_CA⟩ := Postulate1 C A hABC.ne₁₃.symm
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDEF.ne₁₂
  obtain ⟨B₁, B₂, hB₁BB₂, hB₁B₂⟩ := Prop31 hABC.ne₁₃.symm hABC.cab
  obtain ⟨BG, hB₁_BG, hB₂_BG⟩ := Postulate1 B₁ B₂ hB₁B₂.1
  have hB_BG : OnLine B BG := on_line_of_between_ends hB₁BB₂ hB₁_BG hB₂_BG
  have hBG_CA : Parallel BG CA := hB₁B₂.parallel hB₁_BG hB₂_BG hC_CA hA_CA
  obtain ⟨F₁, F₂, hF₁FF₂, hF₁F₂⟩ := Prop31 hDEF.ne₁₂ hDEF
  obtain ⟨FH, hF₁_FH, hF₂_FH⟩ := Postulate1 F₁ F₂ hF₁F₂.1
  have hF_FH : OnLine F FH := on_line_of_between_ends hF₁FF₂ hF₁_FH hF₂_FH
  have hFH_DE : Parallel FH DE := hF₁F₂.parallel hF₁_FH hF₂_FH hD_DE hE_DE
  /- G and H are where the parallels BG and FH meet AD (`Prop30.meet`). -/
  have hAD_CA : AD ≠ CA := fun e => hAD_BF.symm.not_onLine hC (e ▸ hC_CA)
  obtain ⟨G, hG, hG_BG⟩ := Prop30.meet hBG_CA hA_CA hA hAD_CA
  have hAD_DE : AD ≠ DE := fun e => hAD_BF.symm.not_onLine hE (e ▸ hE_DE)
  obtain ⟨H, hH, hH_FH⟩ := Prop30.meet hFH_DE hD_DE hD hAD_DE
  -- Then each of the figures GBCA, DEFH is a parallelogram; and GBCA is equal to DEFH; for
  -- they are on equal bases BC, EF and in the same parallels BF, GH. [I. 36]
  have hGBCA : Parallelogram G B C A :=
    ⟨AreParallel.of_parallel (fun e => hAD_BF.symm.not_onLine hB (e ▸ hG)) hABC.ne₁₃.symm
        hG_BG hB_BG hC_CA hA_CA hBG_CA,
      AreParallel.of_parallel hABC.ne₂₃ (fun e => hBG_CA.not_onLine hG_BG (e ▸ hA_CA))
        hB hC hA hG hAD_BF.symm⟩
  have hDEFH : Parallelogram D E F H :=
    ⟨AreParallel.of_parallel hDEF.ne₁₂ (fun e => hAD_BF.symm.not_onLine hF (e ▸ hH))
        hD_DE hE_DE hF_FH hH_FH hFH_DE.symm,
      AreParallel.of_parallel hDEF.ne₂₃ (fun e => hFH_DE.not_onLine hH_FH (e ▸ hD_DE))
        hE hF hH hD hAD_BF.symm⟩
  have h36 : quadArea G B C A = quadArea D E F H :=
    Prop36 hGBCA hDEFH hbase ⟨AD, hG, hA, hD, hH⟩ ⟨BF, hB, hC, hE, hF⟩
  -- Moreover the triangle ABC is half of the parallelogram GBCA; for the diameter AB bisects
  -- it. [I. 34]
  have h₁ : quadArea G B C A = △ A B C + △ A B C := by
    rw [← hGBCA.quadArea_rotate, area_bca A B C]
    exact Prop34.bisect hGBCA.rotate
  -- And the triangle FED is half of the parallelogram DEFH; for the diameter DF bisects
  -- it. [I. 34]
  have h₂ : quadArea D E F H = △ F E D + △ F E D := by
    rw [area_cba F E D]
    exact Prop34.bisect hDEFH
  -- [But the halves of equal things are equal to one another.]
  have heq : △ A B C = △ F E D := Magnitude.eq_of_add_self_eq (h₁.symm.trans (h36.trans h₂))
  -- Therefore the triangle ABC is equal to the triangle DEF.
  rw [heq, area_cba F E D]
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
