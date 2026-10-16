import Elements.Figure.Basics
import Elements.BookI.Prop34
import Elements.BookI.Prop37

/-!
# Book I, Proposition 41

Euclid's text, in Heath's translation: [`heath/I/41.md`](../../heath/I/41.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If a parallelogram have the same base with a triangle and be in the same parallels, the
parallelogram is double of the triangle. -/
theorem Prop41 {A B C D E : Point} (hABCD : Parallelogram A B C D) (hE : Collinear A D E) :
    quadArea A B C D = △ B E C + △ B E C := by
  -- For let the parallelogram ABCD have the same base BC with the triangle EBC,
  -- and let it be in the same parallels BC, AE;
  obtain ⟨AE, hA_AE, hD_AE, hE_AE⟩ := hE
  obtain ⟨BC, hB, hC⟩ := Postulate1 B C hABCD.2.1
  have hpar : Parallel AE BC := (hABCD.2.parallel hB hC hD_AE hA_AE).symm
  -- I say that the parallelogram ABCD is double of the triangle BEC.
  -- For let AC be joined.
  /- The area `quadArea A B C D` already measures ABCD by its diameter AC,
     as the triangles ABC and ACD together. -/
  -- Then the triangle ABC is equal to the triangle EBC;
  -- for it is on the same base BC with it and in the same parallels BC, AE. [I. 37]
  have hEBC : Triangle E B C :=
    (Triangle.of_line hB hC hABCD.2.1 (hpar.not_onLine hE_AE)).cab
  have h37 : △ A B C = △ E B C :=
    Prop37 hABCD.triangle hEBC ⟨AE, BC, hpar, hA_AE, hE_AE, hB, hC⟩
  -- But the parallelogram ABCD is double of the triangle ABC;
  -- for the diameter AC bisects it; [I. 34]
  have h34 : quadArea A B C D = △ A B C + △ A B C := Prop34.bisect hABCD
  -- so that the parallelogram ABCD is also double of the triangle EBC.
  rw [h34, h37, area_bac E B C]
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
