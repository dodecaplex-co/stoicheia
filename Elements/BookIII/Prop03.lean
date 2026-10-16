import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop05
import Elements.BookI.Prop08
import Elements.BookI.Prop26

/-!
# Book III, Proposition 3

Euclid's text, in Heath's translation: [`heath/III/03.md`](../../heath/III/03.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If in a circle a straight line through the centre bisect a straight line not through the centre,
it also cuts it at right angles; and if it cut it at right angles, it also bisects it. -/
theorem Prop3 {A B E F : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hAFB : Between A F B) (hE_AB : ¬ Collinear A B E) :
    (‖A F‖ = ‖F B‖ → ∠ A F E = ∟ ∧ ∠ B F E = ∟) ∧ (∠ A F E = ∟ → ‖A F‖ = ‖F B‖) := by
  -- Let ABC be a circle, and in it let a straight line CD through the centre bisect a straight
  -- line AB not through the centre at the point F;
  -- I say that it also cuts it at right angles.
  -- For let the centre of the circle ABC be taken, and let it be E; let EA, EB be joined.
  -- Then, since AF is equal to FB,
  -- and FE is common,
  -- two sides are equal to two sides;
  -- and the base EA is equal to the base EB;
  -- therefore the angle AFE is equal to the angle BFE. [I. 8]
  -- But, when a straight line set up on a straight line makes the adjacent angles equal to one
  -- another, each of the equal angles is right; [I. Def. 10]
  -- therefore each of the angles AFE, BFE is right.
  -- Therefore CD, which is through the centre, and bisects AB which is not through the centre,
  -- also cuts it at right angles.
  -- Again, let CD cut AB at right angles;
  -- I say that it also bisects it, that is, that AF is equal to FB.
  -- For, with the same construction,
  -- since EA is equal to EB,
  -- the angle EAF is also equal to the angle EBF. [I. 5]
  -- But the right angle AFE is equal to the right angle BFE,
  -- therefore EAF, EBF are two triangles having two angles equal to two angles and one side
  -- equal to one side, namely EF, which is common to them, and subtends one of the equal
  -- angles;
  -- therefore they will also have the remaining sides equal to the remaining sides; [I. 26]
  -- therefore AF is equal to FB.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
