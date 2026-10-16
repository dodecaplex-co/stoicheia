import Elements.Figure.Basics
import Elements.BookIII.Squares

/-!
# Book III, Proposition 11

Euclid's text, in Heath's translation: [`heath/III/11.md`](../../heath/III/11.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If two circles touch one another internally, and their centres be taken, the straight line
joining their centres, if it be also produced, will fall on the point of contact of the circles. -/
theorem Prop11 {A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)
    (htouch : TouchesInternally ABC ADE A) :
    Between F G A := by
  -- For let the two circles ABC, ADE touch one another internally at the point A, and let the
  -- centre F of the circle ABC, and the centre G of ADE, be taken;
  -- I say that the straight line joined from G to F and produced will fall on A.
  -- For suppose it does not, but, if possible, let it fall as FGH, and let AF, AG be joined.
  -- Then, since AG, GF are greater than FA, that is, than FH,
  -- let FG be subtracted from each;
  -- therefore the remainder AG is greater than the remainder GH.
  -- But AG is equal to GD;
  -- therefore GD is also greater than GH,
  -- the less than the greater: which is impossible.
  -- Therefore the straight line joined from F to G will not fall outside;
  -- therefore it will fall at A on the point of contact.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
