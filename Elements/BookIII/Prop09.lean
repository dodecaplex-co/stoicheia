import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop08
import Elements.BookIII.Prop01

/-!
# Book III, Proposition 9

Euclid's text, in Heath's translation: [`heath/III/09.md`](../../heath/III/09.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If a point be taken within a circle, and more than two equal straight lines fall from the point
on the circle, the point taken is the centre of the circle. -/
theorem Prop9 {A B C D : Point} {ABC : Circle} (hABC : ∃ O : Point, Centre O ABC)
    (hD : InsideCircle D ABC) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hDA : ‖D A‖ = ‖D B‖) (hDB : ‖D B‖ = ‖D C‖) :
    Centre D ABC := by
  -- Let ABC be a circle and D a point within it, and from D let more than two equal straight
  -- lines, namely DA, DB, DC, fall on the circle ABC;
  -- I say that the point D is the centre of the circle ABC.
  -- For let AB, BC be joined and bisected at the points E, F, and let ED, FD be joined and
  -- drawn through to the points G, K, H, L.
  -- Then, since AE is equal to EB,
  -- and ED is common,
  -- the two sides AE, ED are equal to the two sides BE, ED;
  -- and the base DA is equal to the base DB;
  -- therefore the angle AED is equal to the angle BED. [I. 8]
  -- Therefore each of the angles AED, BED is right; [I. Def. 10]
  -- therefore GK cuts AB into two equal parts and at right angles.
  -- And since, if in a circle a straight line cut a straight line into two equal parts and at
  -- right angles, the centre of the circle is on the cutting straight line, [III. 1, Por.]
  -- the centre of the circle is on GK.
  -- For the same reason
  -- the centre of the circle ABC is also on HL.
  -- And the straight lines GK, HL have no other point common but the point D;
  -- therefore the point D is the centre of the circle ABC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
