import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop05
import Elements.BookI.Prop16
import Elements.BookI.Prop19
import Elements.BookIII.Prop01

/-!
# Book III, Proposition 2

Euclid's text, in Heath's translation: [`heath/III/02.md`](../../heath/III/02.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If on the circumference of a circle two points be taken at random, the straight line joining the
points will fall within the circle. -/
theorem Prop2 {A B : Point} {ABC : Circle} (hABC : ∃ D : Point, Centre D ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) :
    ∀ E : Point, Between A E B → InsideCircle E ABC := by
  -- Let ABC be a circle, and let two points A, B be taken at random on its circumference;
  -- I say that the straight line joined from A to B will fall within the circle.
  -- For suppose it does not, but, if possible, let it fall outside, as AEB;
  -- let the centre of the circle ABC be taken [III. 1], and let it be D; let DA, DB be joined,
  -- and let DFE be drawn through.
  -- Then, since DA is equal to DB,
  -- the angle DAE is also equal to the angle DBE. [I. 5]
  -- And, since one side AEB of the triangle DAE is produced,
  -- the angle DEB is greater than the angle DAE. [I. 16]
  -- But the angle DAE is equal to the angle DBE;
  -- therefore the angle DEB is greater than the angle DBE.
  -- And the greater angle is subtended by the greater side; [I. 19]
  -- therefore DB is greater than DE.
  -- But DB is equal to DF;
  -- therefore DF is greater than DE,
  -- the less than the greater: which is impossible.
  -- Therefore the straight line joined from A to B will not fall outside the circle.
  -- Similarly we can prove that neither will it fall on the circumference itself;
  -- therefore it will fall within.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
