import Elements.Figure.Basics
import Elements.BookI.Prop13

/-!
# Book I, Proposition 15

Euclid's text, in Heath's translation: [`heath/I/15.md`](../../heath/I/15.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If two straight lines cut one another, they make the vertical angles equal to one another. -/
theorem Prop15 {A B C D E : Point} (hAEB : Between A E B) (hCED : Between C E D)
    (hC : ¬ Collinear A B C) :
    ∠ A E C = ∠ D E B ∧ ∠ C E B = ∠ A E D := by
  -- For let the straight lines AB, CD cut one another at the point E;
  -- I say that the angle AEC is equal to the angle DEB,
  -- and the angle CEB to the angle AED.
  -- For, since the straight line AE stands on the straight line CD, making the angles CEA,
  -- AED,
  -- the angles CEA, AED are equal to two right angles. [I. 13]
  -- Again, since the straight line DE stands on the straight line AB, making the angles AED,
  -- DEB,
  -- the angles AED, DEB are equal to two right angles. [I. 13]
  -- But the angles CEA, AED were also proved equal to two right angles;
  -- therefore the angles CEA, AED are equal to the angles AED, DEB. [Post. 4 and C.N. 1]
  -- Let the angle AED be subtracted from each;
  -- therefore the remaining angle CEA is equal to the remaining angle BED. [C.N. 3]
  -- Similarly it can be proved that the angles CEB, DEA are also equal.
  -- Therefore etc.
  -- Q. E. D.
  -- [PORISM. From this it is manifest that, if two straight lines cut one another, they will
  -- make the angles at the point of section equal to four right angles.]
  sorry

end Elements.BookI
