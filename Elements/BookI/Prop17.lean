import Elements.Figure.Basics
import Elements.BookI.Prop13
import Elements.BookI.Prop16

/-!
# Book I, Proposition 17

Euclid's text, in Heath's translation: [`heath/I/17.md`](../../heath/I/17.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid proves that the angles ABC, BCA are less than two right angles, and
then says "similarly" for the other two pairs. So the Lean makes the argument
once, for any triangle, and uses it three times: in the triangle ABC, in the
triangle BAC (with AC produced), and in the triangle CAB (with AB
produced). Nothing more is read off the figure than Book Zero already says, so
there are no helper theorems.
-/

namespace Elements.BookI

open Tacit

/-- In any triangle two angles taken together in any manner are less than two right angles. -/
theorem Prop17 {A B C : Point} (hABC : Triangle A B C) :
    ∠ A B C + ∠ B C A < ∟ + ∟ ∧ ∠ B A C + ∠ A C B < ∟ + ∟ ∧ ∠ C A B + ∠ A B C < ∟ + ∟ := by
  -- Let ABC be a triangle;
  -- I say that two angles of the triangle ABC taken together in any manner are less than two
  -- right angles.
  /- "In any manner": any two of the three angles, so three sums. Euclid's argument is
     for the angles ABC, BCA; we give it for every triangle, in his letters, and use
     it for each pair below. -/
  have less : ∀ {A B C : Point}, Triangle A B C → ∠ A B C + ∠ B C A < ∟ + ∟ := by
    intro A B C hABC
    have hA_B : A ≠ B := hABC.ne₁₂
    have hB_C : B ≠ C := hABC.ne₂₃
    have hA_C : A ≠ C := hABC.ne₁₃
    -- For let BC be produced to D. [Post. 2]
    obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hB_C
    obtain ⟨D, hD_BC, hBCD, -⟩ := Postulate2 hB_BC hC_BC hB_C []
    -- Then, since the angle ACD is an exterior angle of the triangle ABC,
    -- it is greater than the interior and opposite angle ABC. [I. 16]
    /- I.16 names the interior angle from C, as CBA; it is the angle ABC read the
       other way round (`angle_symm`). -/
    have hABC_ACD : ∠ A B C < ∠ A C D := by
      rw [angle_symm hA_B hB_C.symm]
      exact (Prop16 hABC hBCD).1
    -- Let the angle ACB be added to each;
    /- The same angle added to a greater and a less leaves the first sum greater: no
       Common Notion says so, but a tacit rule of magnitude does (`add_lt_add_right`,
       System E §3.5). -/
    have hadded : ∠ A B C + ∠ A C B < ∠ A C D + ∠ A C B := add_lt_add_right (∠ A C B) hABC_ACD
    -- therefore the angles ACD, ACB are greater than the angles ABC, BCA.
    /- The angle ACB, added to ABC, is the angle BCA read the other way round. -/
    have hgreater : ∠ A B C + ∠ B C A < ∠ A C D + ∠ A C B := by
      rw [angle_symm hB_C hA_C]
      exact hadded
    -- But the angles ACD, ACB are equal to two right angles. [I. 13]
    /- AC stands on BD, which is BC produced; A is off it, since ABC is a triangle
       (`Triangle.off_line`, `Triangle.of_line`). I.13 names the two angles BCA, ACD. -/
    have hA_BC : ¬ OnLine A BC := hABC.bca.off_line hB_BC hC_BC
    have hBDA : Triangle B D A := Triangle.of_line hB_BC hD_BC (ne_of_between_ends hBCD) hA_BC
    have htwo : ∠ A C D + ∠ A C B = ∟ + ∟ := by
      rw [add_comm (∠ A C D), angle_symm hA_C hB_C]
      exact Prop13 hBCD hBDA
    -- Therefore the angles ABC, BCA are less than two right angles.
    rw [← htwo]
    exact hgreater
  /- This is Euclid's own figure, with the angles ABC, BCA. -/
  have hABC_BCA : ∠ A B C + ∠ B C A < ∟ + ∟ := less hABC
  -- Similarly we can prove that the angles BAC, ACB are also less than two right angles, and
  -- so are the angles CAB, ABC as well.
  /- The same argument in the triangle BAC: AC is produced, and the exterior angle at C
     is greater than the angle BAC. And in the triangle CAB: AB is produced, and the
     exterior angle at B is greater than the angle CAB. -/
  have hBAC_ACB : ∠ B A C + ∠ A C B < ∟ + ∟ := less hABC.bac
  have hCAB_ABC : ∠ C A B + ∠ A B C < ∟ + ∟ := less hABC.cab
  -- Therefore etc.
  exact ⟨hABC_BCA, hBAC_ACB, hCAB_ABC⟩
  -- Q. E. D.

end Elements.BookI
