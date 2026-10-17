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
vertices A and D, the other through the bases BC and EF. The two vertices
may be one point, as when I.42 cites this for the triangles ABE and AEC. So
under "let AD be produced in both directions to G, H", "AD" is the parallel
through the vertices itself, and G and H are taken on it.
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
  /- G and H are where the parallels BG and FH meet AD (`Prop31.parallelogram`). -/
  obtain ⟨G, hG, hACBG⟩ := Prop31.parallelogram hAD_BF hA hC hB hABC.ne₂₃.symm
  obtain ⟨H, hH, hDEFH⟩ := Prop31.parallelogram hAD_BF hD hE hF hDEF.ne₂₃
  -- Then each of the figures GBCA, DEFH is a parallelogram; and GBCA is equal to DEFH; for
  -- they are on equal bases BC, EF and in the same parallels BF, GH. [I. 36]
  have hGBCA : Parallelogram G B C A := hACBG.reverse.rotate
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
