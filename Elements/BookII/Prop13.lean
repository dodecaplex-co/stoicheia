import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop47
import Elements.BookII.Prop07

/-!
# Book II, Proposition 13

Euclid's text, in Heath's translation: [`heath/II/13.md`](../../heath/II/13.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- In acute-angled triangles the square on the side subtending the acute angle is less than the
squares on the sides containing the acute angle by twice the rectangle contained by one of the
sides about the acute angle, namely that on which the perpendicular falls, and the straight line
cut off within by the perpendicular towards the acute angle. -/
theorem Prop13 {A B C D : Point} (hABC : Triangle A B C) (hB : IsAcute A B C) (hC : IsAcute A C B)
    (hD : Collinear B C D) (hAD : ∀ P : Point, Collinear B C P → P ≠ D → ∠ A D P = ∟) :
    sq A C + (rect C B B D + rect C B B D) = sq C B + sq B A := by
  -- Let ABC be an acute-angled triangle having the angle at B acute, and let AD be drawn from
  -- the point A perpendicular to BC;
  -- I say that the square on AC is less than the squares on CB, BA by twice the rectangle
  -- contained by CB, BD.
  -- For, since the straight line CB has been cut at random at D,
  -- the squares on CB, BD are equal to twice the rectangle contained by CB, BD and the square
  -- on DC. [II. 7]
  -- Let the square on DA be added to each;
  -- therefore the squares on CB, BD, DA are equal to twice the rectangle contained by CB, BD
  -- and the squares on AD, DC.
  -- But the square on AB is equal to the squares on BD, DA, for the angle at D is
  -- right; [I. 47]
  -- and the square on AC is equal to the squares on AD, DC;
  -- therefore the squares on CB, BA are equal to the square on AC and twice the rectangle CB,
  -- BD,
  -- so that the square on AC alone is less than the squares on CB, BA by twice the rectangle
  -- contained by CB, BD.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookII
