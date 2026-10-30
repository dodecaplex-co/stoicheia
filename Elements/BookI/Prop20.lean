import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop05
import Elements.BookI.Helpers
import Elements.BookI.Prop19

/-!
# Book I, Proposition 20

Euclid's text, in Heath's translation: [`heath/I/20.md`](../../heath/I/20.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid proves that BA, AC are greater than BC, and then says "similarly" for
the other two pairs of sides. So the Lean makes his argument once, for any
triangle, and uses it three times, naming the triangle from a different corner
each time.
-/

namespace Elements.BookI

open Tacit

/-- In any triangle two sides taken together in any manner are greater than the remaining one. -/
theorem Prop20 {A B C : Point} (hABC : Triangle A B C) :
    ‖B C‖ < ‖B A‖ + ‖A C‖ ∧ ‖A C‖ < ‖A B‖ + ‖B C‖ ∧ ‖A B‖ < ‖B C‖ + ‖C A‖ := by
  -- For let ABC be a triangle;
  -- I say that in the triangle ABC two sides taken together in any manner are greater than the
  -- remaining one, namely
  -- BA, AC greater than BC,
  -- AB, BC greater than AC,
  -- BC, CA greater than AB.
  /- Euclid proves the first, and says "similarly" for the other two. So we give his
     argument for every triangle, in his letters, and use it three times below. -/
  have greater : ∀ {A B C : Point}, Triangle A B C → ‖B C‖ < ‖B A‖ + ‖A C‖ := by
    intro A B C hABC
    have hB_A : B ≠ A := hABC.ne₁₂.symm
    have hA_C : A ≠ C := hABC.ne₁₃
    obtain ⟨BA, hB_BA, hA_BA⟩ := Postulate1 B A hB_A
    have hC_BA : ¬ OnLine C BA := hABC.bac.off_line hB_BA hA_BA
    -- For let BA be drawn through to the point D,
    /- Drawn through beyond A to a point X, far enough for I.3 to cut AD off from AX
       (`produce_longer`, as in I.11). -/
    obtain ⟨X, hBAX, hAC_AX⟩ := produce_longer hB_A hA_C
    -- let DA be made equal to CA, and let DC be joined.
    /- Heath gives no bracket here, but "let DA be made equal" is I.3's work, as in
       I.11 and I.16: cut off AD from AX. Then D lies between A and X, and so A lies
       between B and D (`between_cut`): BA drawn through reaches D. DC is named by
       its ends, as a side of the triangle ADC, so nothing is drawn for the join. -/
    obtain ⟨D, hADX, hAD_CA⟩ := Prop3 (A := A) (B := X) hA_C.symm
      (by rw [len_symm C A]; exact hAC_AX)
    have hBAD : Between B A D := between_cut hBAX hADX
    have hD_BA : OnLine D BA := on_line_of_between hBAD hB_BA hA_BA
    have hA_D : A ≠ D := ne_of_between hADX
    -- Then, since DA is equal to AC,
    have hDA_AC : ‖D A‖ = ‖A C‖ := by rw [len_symm D A, hAD_CA, len_symm C A]
    -- the angle ADC is also equal to the angle ACD; [I. 5]
    have hADC : Triangle A D C := Triangle.of_line hA_BA hD_BA hA_D hC_BA
    have hADC_ACD : ∠ A D C = ∠ A C D :=
      Prop5.base hADC (by rw [← len_symm D A]; exact hDA_AC)
    -- therefore the angle BCD is greater than the angle ADC. [C.N. 5]
    /- Greater than the angle ACD, which is equal to it: CA falls within the angle
       BCD, since A lies between B and D, so that the angle BCD is made up of the
       angles BCA and ACD (`angle_add_of_between`); the angle BCA, an angle of the
       triangle ABC, is something (`Triangle.angle_pos`); and the whole is greater
       than the part. -/
    have hBDC : Triangle B D C :=
      Triangle.of_line hB_BA hD_BA (ne_of_between_ends hBAD) hC_BA
    have hADC_BCD : ∠ A D C < ∠ B C D := by
      rw [hADC_ACD, angle_add_of_between hBDC hBAD, add_comm]
      exact CommonNotion5 hABC.bca.angle_pos
    -- And, since DCB is a triangle having the angle BCD greater than the angle BDC,
    /- The angle BDC is the angle ADC, since A lies on the ray from D through B
       (`angle_onRay_left`). -/
    have hDCB : Triangle D C B := hBDC.bca
    have hD_C : D ≠ C := fun e => hC_BA (e ▸ hD_BA)
    have hBDC_BCD : ∠ B D C < ∠ B C D := by
      rw [← angle_onRay_left (OnRay.of_between (between_symm hBAD)) hD_C.symm]
      exact hADC_BCD
    -- and the greater angle is subtended by the greater side, [I. 19]
    /- I.19 for the triangle BCD, named from B: the angle at C is greater than the
       angle at D, so the side BD, opposite C, is greater than the side BC, opposite
       D. -/
    have hBC_BD : ‖B C‖ < ‖B D‖ :=
      Prop19 hDCB.cba (by rw [angle_symm hD_C.symm (ne_of_between_ends hBAD)]; exact hBDC_BCD)
    -- therefore DB is greater than BC.
    have hBC_DB : ‖B C‖ < ‖D B‖ := by rw [len_symm D B]; exact hBC_BD
    -- But DA is equal to AC;
    /- And DB is BA and AD together, since A lies between B and D (System E,
       Diagram-segment 1); so DB is BA and AC together. -/
    have hDB : ‖D B‖ = ‖B A‖ + ‖A C‖ := by
      rw [← hDA_AC, len_symm D A, len_add_of_between hBAD, len_symm D B]
    -- therefore BA, AC are greater than BC.
    rw [← hDB]
    exact hBC_DB
  /- Euclid's argument, in his own figure: BA, AC are greater than BC. -/
  have hBC : ‖B C‖ < ‖B A‖ + ‖A C‖ := greater hABC
  -- Similarly we can prove that AB, BC are also greater than CA, and BC, CA than AB.
  /- The same argument for the triangle BAC, with AB drawn through beyond B, and for
     the triangle CBA, with BC drawn through beyond C. -/
  have hAC : ‖A C‖ < ‖A B‖ + ‖B C‖ := greater hABC.bac
  have hAB : ‖A B‖ < ‖B C‖ + ‖C A‖ := by
    rw [len_symm A B]
    exact greater hABC.cba
  -- Therefore etc.
  exact ⟨hBC, hAC, hAB⟩
  -- Q. E. D.

end Elements.BookI
