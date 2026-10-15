import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop29
import Elements.BookI.Prop34

/-!
# Book I, Proposition 35

Euclid's text, in Heath's translation: [`heath/I/35.md`](../../heath/I/35.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Parallelograms which are on the same base and in the same parallels are equal to one another. -/
theorem Prop35 {A B C D E F : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E B C F)
    (hAF : ∃ L : Line, OnLine A L ∧ OnLine D L ∧ OnLine E L ∧ OnLine F L) :
    quadArea A B C D = quadArea E B C F := by
  -- Let ABCD, EBCF be parallelograms on the same base BC and in the same parallels AF, BC;
  -- I say that ABCD is equal to the parallelogram EBCF.
  -- For, since ABCD is a parallelogram,
  -- AD is equal to BC. [I. 34]
  -- For the same reason also
  -- EF is equal to BC,
  -- so that AD is also equal to EF; [C.N. 1]
  -- and DE is common;
  -- therefore the whole AE is equal to the whole DF. [C.N. 2]
  -- But AB is also equal to DC; [I. 34]
  -- therefore the two sides EA, AB are equal to the two sides FD, DC respectively,
  -- and the angle FDC is equal to the angle EAB, the exterior to the interior; [I. 29]
  -- therefore the base EB is equal to the base FC,
  -- and the triangle EAB will be equal to the triangle FDC. [I. 4]
  -- Let DGE be subtracted from each;
  -- therefore the trapezium ABGD which remains is equal to the trapezium EGCF which
  -- remains. [C.N. 3]
  -- Let the triangle GBC be added to each;
  -- therefore the whole parallelogram ABCD is equal to the whole parallelogram EBCF. [C.N. 2]
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
