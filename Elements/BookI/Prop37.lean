import Elements.Figure.Basics
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop35
import Elements.BookI.HelpersParallels

/-!
# Book I, Proposition 37

Euclid's text, in Heath's translation: [`heath/I/37.md`](../../heath/I/37.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

"In the same parallels AD, BC": two parallel straight lines, one through the
vertices `A` and `D`, the other through the base `BC`, as in I.38. The two vertices
may be one point, and then the two triangles are one. So under "let AD be produced
in both directions to E, F", "AD" is the parallel through the vertices itself, and
`E` and `F` are taken on it.
-/

namespace Elements.BookI

open Tacit

/-- Triangles which are on the same base and in the same parallels are equal to one another. -/
theorem Prop37 {A B C D : Point} (hABC : Triangle A B C) (hDBC : Triangle D B C)
    (hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧ OnLine B M ∧ OnLine C M) :
    △ A B C = △ D B C := by
  -- Let ABC, DBC be triangles on the same base BC and in the same parallels AD, BC;
  obtain ⟨AD, BC, hAD_BC, hA, hD, hB, hC⟩ := hpar
  -- I say that the triangle ABC is equal to the triangle DBC.
  -- Let AD be produced in both directions to E, F; through B let BE be drawn parallel to
  -- CA, [I. 31] and through C let CF be drawn parallel to BD. [I. 31]
  /- E and F are where the parallels BE and CF meet the whole straight line AD
     (`Prop31.parallelogram`, which cites I.30 for the meeting). -/
  obtain ⟨E, hE, hACBE⟩ := Prop31.parallelogram hAD_BC hA hC hB hABC.ne₂₃.symm
  obtain ⟨F, hF, hDBCF⟩ := Prop31.parallelogram hAD_BC hD hB hC hDBC.ne₂₃
  -- Then each of the figures EBCA, DBCF is a parallelogram; and they are equal, for they are
  -- on the same base BC and in the same parallels BC, EF. [I. 35]
  have hEBCA : Parallelogram E B C A := hACBE.reverse.rotate
  have h35 : quadArea E B C A = quadArea D B C F :=
    Prop35 hEBCA hDBCF ⟨AD, hE, hA, hD, hF⟩
  -- Moreover the triangle ABC is half of the parallelogram EBCA; for the diameter AB bisects
  -- it. [I. 34]
  have h₁ : quadArea E B C A = △ A B C + △ A B C := by
    rw [← hEBCA.quadArea_rotate, area_bca A B C]
    exact Prop34.bisect hEBCA.rotate
  -- And the triangle DBC is half of the parallelogram DBCF; for the diameter DC bisects
  -- it. [I. 34]
  have h₂ : quadArea D B C F = △ D B C + △ D B C := Prop34.bisect hDBCF
  -- [But the halves of equal things are equal to one another.]
  have heq : △ A B C = △ D B C := Magnitude.eq_of_add_self_eq (h₁.symm.trans (h35.trans h₂))
  -- Therefore the triangle ABC is equal to the triangle DBC.
  exact heq
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
