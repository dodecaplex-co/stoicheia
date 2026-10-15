import Elements.Figure.Basics
import Elements.BookI.Prop13

/-!
# Book I, Proposition 14

Euclid's text, in Heath's translation: [`heath/I/14.md`](../../heath/I/14.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If with any straight line, and at a point on it, two straight lines not lying on the same side
make the adjacent angles equal to two right angles, the two straight lines will be in a straight
line with one another. -/
theorem Prop14 {A B C D : Point} (hCD : OppositeSidesOf C D A B) (h : ∠ A B C + ∠ A B D = ∟ + ∟) :
    Between C B D := by
  -- For with any straight line AB, and at the point B on it, let the two straight lines BC, BD
  -- not lying on the same side make the adjacent angles ABC, ABD equal to two right angles;
  -- I say that BD is in a straight line with CB.
  -- For, if BD is not in a straight line with BC, let BE be in a straight line with CB.
  -- Then, since the straight line AB stands on the straight line CBE,
  -- the angles ABC, ABE are equal to two right angles. [I. 13]
  -- But the angles ABC, ABD are also equal to two right angles;
  -- therefore the angles CBA, ABE are equal to the angles CBA, ABD. [Post. 4 and C.N. 1]
  -- Let the angle CBA be subtracted from each;
  -- therefore the remaining angle ABE is equal to the remaining angle ABD, [C.N. 3]
  -- the less to the greater: which is impossible.
  -- Therefore BE is not in a straight line with CB.
  -- Similarly we can prove that neither is any other straight line except BD.
  -- Therefore CB is in a straight line with BD.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
