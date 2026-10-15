import Elements.Figure.Basics
import Elements.BookI.Prop01
import Elements.BookI.Prop04
import Elements.BookI.Prop09

/-!
# Book I, Proposition 10

Euclid's text, in Heath's translation: [`heath/I/10.md`](../../heath/I/10.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid never says why the bisector `CD` meets `AB` between `A` and `B`. I.9 says
that it falls within the angle `ACB`, and `crossbar` (Book Zero) does the rest.
-/

namespace Elements.BookI

open Tacit

/-- To bisect a given finite straight line. -/
theorem Prop10 {A B : Point} (hAB : A ≠ B) :
    ∃ D : Point, Between A D B ∧ ‖A D‖ = ‖D B‖ := by
  -- Let AB be the given finite straight line.
  -- Thus it is required to bisect the finite straight line AB.
  -- Let the equilateral triangle ABC be constructed on it, [I. 1]
  -- and let the angle ACB be bisected by the straight line CD; [I. 9]
  -- I say that the straight line AB has been bisected at the point D.
  -- For, since AC is equal to CB,
  -- and CD is common,
  -- the two sides AC, CD are equal to the two sides BC, CD respectively;
  -- and the angle ACD is equal to the angle BCD;
  -- therefore the base AD is equal to the base BD. [I. 4]
  -- Therefore the given finite straight line AB has been bisected at D.
  -- Q. E. F.
  sorry

end Elements.BookI
