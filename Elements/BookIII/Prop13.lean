import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop02
import Elements.BookIII.Prop11

/-!
# Book III, Proposition 13

Euclid's text, in Heath's translation: [`heath/III/13.md`](../../heath/III/13.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- A circle does not touch a circle at more points than one, whether it touch it internally or
externally. -/
theorem Prop13 {A B C D : Point} {ABDC EBFD ACK : Circle} (hABDC : ∃ G : Point, Centre G ABDC)
    (hEBFD : ∃ H : Point, Centre H EBFD) (hACK : ∃ O : Point, Centre O ACK) :
    ((TouchesInternally ABDC EBFD D ∨ TouchesInternally EBFD ABDC D) →
      OnCircle B ABDC → OnCircle B EBFD → B = D) ∧
    (TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC → C = A) := by
  -- For, if possible, let the circle ABDC touch the circle EBFD, first internally, at more
  -- points than one, namely D, B.
  -- Let the centre G of the circle ABDC, and the centre H of EBFD, be taken.
  -- Therefore the straight line joined from G to H will fall on B, D. [III. 11]
  -- Let it so fall, as BGHD.
  -- Then, since the point G is the centre of the circle ABCD,
  -- BG is equal to GD;
  -- therefore BG is greater than HD;
  -- therefore BH is much greater than HD.
  -- Again, since the point H is the centre of the circle EBFD,
  -- BH is equal to HD;
  -- but it was also proved much greater than it: which is impossible.
  -- Therefore a circle does not touch a circle internally at more points than one.
  -- I say further that neither does it so touch it externally.
  -- For, if possible, let the circle ACK touch the circle ABDC at more points than one, namely
  -- A, C,
  -- and let AC be joined.
  -- Then, since on the circumference of each of the circles ABDC, ACK two points A, C have
  -- been taken at random, the straight line joining the points will fall within each
  -- circle; [III. 2]
  -- but it fell within the circle ABCD and outside ACK [III. Def. 3]: which is absurd.
  -- Therefore a circle does not touch a circle externally at more points than one.
  -- And it was proved that neither does it so touch it internally.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
