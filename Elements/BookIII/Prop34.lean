import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop23
import Elements.BookIII.Prop32

/-!
# Book III, Proposition 34

Euclid's text, in Heath's translation: [`heath/III/34.md`](../../heath/III/34.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- From a given circle to cut off a segment admitting an angle equal to a given rectilineal angle. -/
theorem Prop34 {D₁ D D₂ : Point} {ABC : Circle} (hABC : ∃ O : Point, Centre O ABC)
    (hD : Triangle D₁ D D₂) :
    ∃ A B C : Point, OnCircle A ABC ∧ OnCircle B ABC ∧ OnCircle C ABC ∧ Triangle B A C ∧
      ∠ B A C = ∠ D₁ D D₂ := by
  -- Let ABC be the given circle, and the angle at D the given rectilineal angle;
  -- thus it is required to cut off from the circle ABC a segment admitting an angle equal to
  -- the given rectilineal angle, the angle at D.
  -- Let EF be drawn touching ABC at the point B, and on the straight line FB, and at the point
  -- B on it, let the angle FBC be constructed equal to the angle at D. [I. 23]
  -- Then, since a straight line EF touches the circle ABC,
  -- and BC has been drawn across from the point of contact at B,
  -- the angle FBC is equal to the angle constructed in the alternate segment BAC. [III. 32]
  -- But the angle FBC is equal to the angle at D;
  -- therefore the angle in the segment BAC is equal to the angle at D.
  -- Therefore from the given circle ABC the segment BAC has been cut off admitting an angle
  -- equal to the given rectilineal angle, the angle at D.
  -- Q. E. F.
  sorry

end Elements.BookIII
