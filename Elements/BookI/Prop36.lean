import Elements.Figure.Basics
import Elements.BookI.Prop33
import Elements.BookI.Prop34
import Elements.BookI.Prop35

/-!
# Book I, Proposition 36

Euclid's text, in Heath's translation: [`heath/I/36.md`](../../heath/I/36.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Parallelograms which are on equal bases and in the same parallels are equal to one another. -/
theorem Prop36 {A B C D E F G H : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E F G H)
    (hbase : ‖B C‖ = ‖F G‖)
    (hAH : ∃ L : Line, OnLine A L ∧ OnLine D L ∧ OnLine E L ∧ OnLine H L)
    (hBG : ∃ L : Line, OnLine B L ∧ OnLine C L ∧ OnLine F L ∧ OnLine G L) :
    quadArea A B C D = quadArea E F G H := by
  -- Let ABCD, EFGH be parallelograms which are on equal bases BC, FG and in the same parallels
  -- AH, BG;
  -- I say that the parallelogram ABCD is equal to EFGH.
  -- For let BE, CH be joined.
  -- Then, since BC is equal to FG,
  -- while FG is equal to EH,
  -- BC is also equal to EH. [C.N. 1]
  -- But they are also parallel.
  -- And EB, HC join them;
  -- but straight lines joining equal and parallel straight lines (at the extremities which
  -- are) in the same directions (respectively) are equal and parallel. [I. 33]
  -- Therefore EBCH is a parallelogram. [I. 34]
  -- And it is equal to ABCD;
  -- for it has the same base BC with it, and is in the same parallels BC, AH with it. [I. 35]
  -- For the same reason also EFGH is equal to the same EBCH; [I. 35]
  -- so that the parallelogram ABCD is also equal to EFGH. [C.N. 1]
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
