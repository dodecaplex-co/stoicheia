import Elements.Figure.Basics
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
  obtain ⟨CA, hC_CA, hA_CA⟩ := Postulate1 C A hABC.ne₁₃.symm
  obtain ⟨BD, hD_BD, hB_BD⟩ := Postulate1 D B hDBC.ne₁₂
  obtain ⟨B₁, B₂, hB₁BB₂, hB₁B₂⟩ := Prop31 hABC.ne₁₃.symm hABC.cab
  obtain ⟨BE, hB₁_BE, hB₂_BE⟩ := Postulate1 B₁ B₂ hB₁B₂.1
  have hB_BE : OnLine B BE := on_line_of_between_ends hB₁BB₂ hB₁_BE hB₂_BE
  have hBE_CA : Parallel BE CA := hB₁B₂.parallel hB₁_BE hB₂_BE hC_CA hA_CA
  obtain ⟨C₁, C₂, hC₁CC₂, hC₁C₂⟩ := Prop31 hDBC.ne₁₂ hDBC
  obtain ⟨CF, hC₁_CF, hC₂_CF⟩ := Postulate1 C₁ C₂ hC₁C₂.1
  have hC_CF : OnLine C CF := on_line_of_between_ends hC₁CC₂ hC₁_CF hC₂_CF
  have hCF_BD : Parallel CF BD := hC₁C₂.parallel hC₁_CF hC₂_CF hD_BD hB_BD
  /- E and F are where the parallels BE and CF meet the whole straight line AD. -/
  have hAD_CA : AD ≠ CA := fun e => hAD_BC.symm.not_onLine hC (e ▸ hC_CA)
  obtain ⟨E, hE, hE_BE⟩ := Prop30.meet hBE_CA hA_CA hA hAD_CA
  have hAD_BD : AD ≠ BD := fun e => hAD_BC.symm.not_onLine hB (e ▸ hB_BD)
  obtain ⟨F, hF, hF_CF⟩ := Prop30.meet hCF_BD hD_BD hD hAD_BD
  -- Then each of the figures EBCA, DBCF is a parallelogram; and they are equal, for they are
  -- on the same base BC and in the same parallels BC, EF. [I. 35]
  have hEBCA : Parallelogram E B C A :=
    ⟨AreParallel.of_parallel (fun e => hAD_BC.symm.not_onLine hB (e ▸ hE)) hABC.ne₁₃.symm
        hE_BE hB_BE hC_CA hA_CA hBE_CA,
      AreParallel.of_parallel hABC.ne₂₃ (fun e => hBE_CA.not_onLine hE_BE (e ▸ hA_CA))
        hB hC hA hE hAD_BC.symm⟩
  have hDBCF : Parallelogram D B C F :=
    ⟨AreParallel.of_parallel hDBC.ne₁₂ (fun e => hAD_BC.symm.not_onLine hC (e ▸ hF))
        hD_BD hB_BD hC_CF hF_CF hCF_BD.symm,
      AreParallel.of_parallel hDBC.ne₂₃ (fun e => hCF_BD.not_onLine hF_CF (e ▸ hD_BD))
        hB hC hF hD hAD_BC.symm⟩
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
  have := Magnitude.eq_of_add_self_eq (h₁.symm.trans (h35.trans h₂))
  -- Therefore the triangle ABC is equal to the triangle DBC.
  exact this
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
