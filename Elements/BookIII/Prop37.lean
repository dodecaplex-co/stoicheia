import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop08
import Elements.BookIII.Prop16
import Elements.BookIII.Prop18
import Elements.BookIII.Prop36

/-!
# Book III, Proposition 37

Euclid's text, in Heath's translation: [`heath/III/37.md`](../../heath/III/37.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If a point be taken outside a circle and from the point there fall on the circle two straight
lines, if one of them cut the circle, and the other fall on it, and if further the rectangle
contained by the whole of the straight line which cuts the circle and the straight line
intercepted on it outside between the point and the convex circumference be equal to the square
on the straight line which falls on the circle, the straight line which falls on it will touch
the circle. -/
theorem Prop37 {A B C D : Point} {ABC : Circle} (hABC : ∃ F : Point, Centre F ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hDCA : Between D C A) (h : rect A D D C = sq D B) :
    Touches D B ABC := by
  -- For let a point D be taken outside the circle ABC; from D let the two straight lines DCA,
  -- DB fall on the circle ACB; let DCA cut the circle and DB fall on it; and let the rectangle
  -- AD, DC be equal to the square on DB.
  -- I say that DB touches the circle ABC.
  -- For let DE be drawn touching ABC; let the centre of the circle ABC be taken, and let it be
  -- F; let FE, FB, FD be joined.
  -- Thus the angle FED is right. [III. 18]
  -- Now, since DE touches the circle ABC, and DCA cuts it,
  -- the rectangle AD, DC is equal to the square on DE. [III. 36]
  -- But the rectangle AD, DC was also equal to the square on DB;
  -- therefore the square on DE is equal to the square on DB;
  -- therefore DE is equal to DB.
  -- And FE is equal to FB;
  -- therefore the two sides DE, EF are equal to the two sides DB, BF;
  -- and FD is the common base of the triangles;
  -- therefore the angle DEF is equal to the angle DBF. [I. 8]
  -- But the angle DEF is right;
  -- therefore the angle DBF is also right.
  -- And FB produced is a diameter;
  -- and the straight line drawn at right angles to the diameter of a circle, from its
  -- extremity, touches the circle; [III. 16, Por.]
  -- therefore DB touches the circle.
  -- Similarly this can be proved to be the case even if the centre be on AC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
