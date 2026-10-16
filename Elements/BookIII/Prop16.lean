import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop05
import Elements.BookI.Prop17
import Elements.BookI.Prop19

/-!
# Book III, Proposition 16

Euclid's text, in Heath's translation: [`heath/III/16.md`](../../heath/III/16.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- The straight line drawn at right angles to the diameter of a circle from its extremity will fall
outside the circle, and into the space between the straight line and the circumference another
straight line cannot be interposed; further the angle of the semicircle is greater, and the
remaining angle less, than any acute rectilineal angle. -/
theorem Prop16 {A B D E : Point} {ABC : Circle} (hD : Centre D ABC) (hA : OnCircle A ABC)
    (hADB : Between A D B) (hE : ¬ Collinear A B E) (hBAE : ∠ B A E = ∟) :
    (∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC) ∧
    (∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC) := by
  -- Let ABC be a circle about D as centre and AB as diameter;
  -- I say that the straight line drawn from A at right angles to AB from its extremity will
  -- fall outside the circle.
  -- For suppose it does not, but, if possible, let it fall within as CA, and let DC be joined.
  -- Since DA is equal to DC,
  -- the angle DAC is also equal to the angle ACD. [I. 5]
  -- But the angle DAC is right;
  -- therefore the angle ACD is also right:
  -- thus, in the triangle ACD, the two angles DAC, ACD are equal to two right angles; which is
  -- impossible. [I. 17]
  -- Therefore the straight line drawn from the point A at right angles to BA will not fall
  -- within the circle.
  -- Similarly we can prove that neither will it fall on the circumference;
  -- therefore it will fall outside.
  -- Let it fall as AE;
  -- I say next that into the space between the straight line AE and the circumference CHA
  -- another straight line cannot be interposed.
  -- For, if possible, let another straight line be so interposed, as FA, and let DG be drawn
  -- from the point D perpendicular to FA.
  -- Then, since the angle AGD is right,
  -- and the angle DAG is less than a right angle,
  -- AD is greater than DG. [I. 19]
  -- But DA is equal to DH;
  -- therefore DH is greater than DG, the less than the greater: which is impossible.
  -- Therefore another straight line cannot be interposed into the space between the straight
  -- line and the circumference.
  -- I say further that the angle of the semicircle contained by the straight line BA and the
  -- circumference CHA is greater than any acute rectilineal angle,
  -- and the remaining angle contained by the circumference CHA and the straight line AE is
  -- less than any acute rectilineal angle.
  -- For, if there is any rectilineal angle greater than the angle contained by the straight
  -- line BA and the circumference CHA, and any rectilineal angle less than the angle contained
  -- by the circumference CHA and the straight line AE, then into the space between the
  -- circumference and the straight line AE a straight line will be interposed such as will
  -- make an angle contained by straight lines which is greater than the angle contained by the
  -- straight line BA and the circumference CHA, and another angle contained by straight lines
  -- which is less than the angle contained by the circumference CHA and the straight line AE.
  -- But such a straight line cannot be interposed;
  -- therefore there will not be any acute angle contained by straight lines which is greater
  -- than the angle contained by the straight line BA and the circumference CHA, nor yet any
  -- acute angle contained by straight lines which is less than the angle contained by the
  -- circumference CHA and the straight line AE.—
  -- PORISM. From this it is manifest that the straight line drawn at right angles to the
  -- diameter of a circle from its extremity touches the circle.
  -- Q. E. D.
  sorry

/-- The Porism to III.16: "the straight line drawn at right angles to the diameter of a
circle from its extremity touches the circle." The diameter through `A` is the
straight line `AD`, `D` the centre, and `AE` is drawn at right angles to it. III.17,
III.33 and III.37 cite it, and Book IV after them. -/
theorem Prop16.porism {A D E : Point} {ABC : Circle} (hD : Centre D ABC) (hA : OnCircle A ABC)
    (hE : ¬ Collinear D A E) (hDAE : ∠ D A E = ∟) :
    Touches A E ABC := by
  sorry

end Elements.BookIII
