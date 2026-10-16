import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop20

/-!
# Book III, Proposition 12

Euclid's text, in Heath's translation: [`heath/III/12.md`](../../heath/III/12.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If two circles touch one another externally, the straight line joining their centres will pass
through the point of contact. -/
theorem Prop12 {A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)
    (htouch : TouchesExternally ABC ADE A) :
    Between F A G := by
  -- For let the two circles ABC, ADE touch one another externally at the point A, and let the
  -- centre F of ABC, and the centre G of ADE, be taken;
  -- I say that the straight line joined from F to G will pass through the point of contact at
  -- A.
  -- For suppose it does not, but, if possible, let it pass as FCDG, and let AF, AG be joined.
  -- Then, since the point F is the centre of the circle ABC,
  -- FA is equal to FC.
  -- Again, since the point G is the centre of the circle ADE,
  -- GA is equal to GD.
  -- But FA was also proved equal to FC;
  -- therefore FA, AG are equal to FC, GD,
  -- so that the whole FG is greater than FA, AG;
  -- but it is also less [I. 20]: which is impossible.
  -- Therefore the straight line joined from F to G will not fail to pass through the point of
  -- contact at A;
  -- therefore it will pass through it.
  -- Therefore etc.
  -- Q. E. D.]
  sorry

end Elements.BookIII
