import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop47
import Elements.BookII.Prop04

/-!
# Book II, Proposition 12

Euclid's text, in Heath's translation: [`heath/II/12.md`](../../heath/II/12.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- In obtuse-angled triangles the square on the side subtending the obtuse angle is greater than
the squares on the sides containing the obtuse angle by twice the rectangle contained by one of
the sides about the obtuse angle, namely that on which the perpendicular falls, and the straight
line cut off outside by the perpendicular towards the obtuse angle. -/
theorem Prop12 {A B C D : Point} (hABC : Triangle A B C) (hBAC : IsObtuse B A C)
    (hD : Collinear C A D) (hBD : ∀ P : Point, Collinear C A P → P ≠ D → ∠ B D P = ∟) :
    sq B C = sq B A + sq A C + (rect C A A D + rect C A A D) := by
  -- Let ABC be an obtuse-angled triangle having the angle BAC obtuse, and let BD be drawn from
  -- the point B perpendicular to CA produced;
  -- I say that the square on BC is greater than the squares on BA, AC by twice the rectangle
  -- contained by CA, AD.
  -- For, since the straight line CD has been cut at random at the point A,
  -- the square on DC is equal to the squares on CA, AD and twice the rectangle contained by
  -- CA, AD. [II. 4]
  -- Let the square on DB be added to each;
  -- therefore the squares on CD, DB are equal to the squares on CA, AD, DB and twice the
  -- rectangle CA, AD.
  -- But the square on CB is equal to the squares on CD, DB, for the angle at D is
  -- right; [I. 47]
  -- and the square on AB is equal to the squares on AD, DB; [I. 47]
  -- therefore the square on CB is equal to the squares on CA, AB and twice the rectangle
  -- contained by CA, AD;
  -- so that the square on CB is greater than the squares on CA, AB by twice the rectangle
  -- contained by CA, AD.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookII
