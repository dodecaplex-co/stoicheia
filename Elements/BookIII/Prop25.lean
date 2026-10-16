import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop06
import Elements.BookIII.Prop09

/-!
# Book III, Proposition 25

Euclid's text, in Heath's translation: [`heath/III/25.md`](../../heath/III/25.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- Given a segment of a circle, to describe the complete circle of which it is a segment. -/
theorem Prop25 {A C : Point} {ABC : Circle} (hABC : ∃ E : Point, Centre E ABC) (hA : OnCircle A ABC)
    (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C) := by
  -- Let ABC be the given segment of a circle;
  -- thus it is required to describe the complete circle belonging to the segment ABC, that is,
  -- of which it is a segment.
  -- For let AC be bisected at D, let DB be drawn from the point D at right angles to AC, and
  -- let AB be joined;
  -- the angle ABD is then greater than, equal to, or less than the angle BAD.
  -- First let it be greater;
  -- and on the straight line BA, and at the point A on it, let the angle BAE be constructed
  -- equal to the angle ABD; let DB be drawn through to E, and let EC be joined.
  -- Then, since the angle ABE is equal to the angle BAE,
  -- the straight line EB is also equal to EA. [I. 6]
  -- And, since AD is equal to DC,
  -- and DE is common,
  -- the two sides AD, DE are equal to the two sides CD, DE respectively;
  -- and the angle ADE is equal to the angle CDE, for each is right;
  -- therefore the base AE is equal to the base CE.
  -- But AE was proved equal to BE;
  -- therefore BE is also equal to CE;
  -- therefore the three straight lines AE, EB, EC are equal to one another.
  -- Therefore the circle drawn with centre E and distance one of the straight lines AE, EB, EC
  -- will also pass through the remaining points and will have been completed. [III. 9]
  -- Therefore, given a segment of a circle, the complete circle has been described.
  -- And it is manifest that the segment ABC is less than a semicircle, because the centre E
  -- happens to be outside it.
  -- Similarly, even if the angle ABD be equal to the angle BAD,
  -- AD being equal to each of the two BD, DC,
  -- the three straight lines DA, DB, DC will be equal to one another,
  -- D will be the centre of the completed circle,
  -- and ABC will clearly be a semicircle.
  -- But, if the angle ABD be less than the angle BAD,
  -- and if we construct, on the straight line BA and at the point A on it, an angle equal to
  -- the angle ABD, the centre will fall on DB within the segment ABC, and the segment ABC will
  -- clearly be greater than a semicircle.
  -- Therefore, given a segment of a circle, the complete circle has been described.
  -- Q. E. F.
  sorry

end Elements.BookIII
