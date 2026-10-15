import Elements.Figure.Basics

/-!
# Book I, Proposition 4

Euclid's text, in Heath's translation: [`heath/I/04.md`](../../heath/I/04.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If two triangles have the two sides equal to two sides respectively, and have the angles
contained by the equal straight lines equal, they will also have the base equal to the base, the
triangle will be equal to the triangle, and the remaining angles will be equal to the remaining
angles respectively, namely those which the equal sides subtend. -/
theorem Prop4 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (hA : ∠ B A C = ∠ E D F) :
    ‖B C‖ = ‖E F‖ ∧ △ A B C = △ D E F ∧ ∠ A B C = ∠ D E F ∧ ∠ A C B = ∠ D F E := by
  -- Let ABC, DEF be two triangles having the two sides AB, AC equal to the two sides DE, DF
  -- respectively, namely AB to DE and AC to DF, and the angle BAC equal to the angle EDF.
  -- I say that the base BC is also equal to the base EF, the triangle ABC will be equal to the
  -- triangle DEF, and the remaining angles will be equal to the remaining angles respectively,
  -- namely those which the equal sides subtend, that is, the angle ABC to the angle DEF, and
  -- the angle ACB to the angle DFE.
  -- For, if the triangle ABC be applied to the triangle DEF,
  -- and if the point A be placed on the point D
  -- and the straight line AB on DE,
  -- then the point B will also coincide with E, because AB is equal to DE.
  -- Again, AB coinciding with DE,
  -- the straight line AC will also coincide with DF, because the angle BAC is equal to the
  -- angle EDF;
  -- hence the point C will also coincide with the point F, because AC is again equal to DF.
  -- But B also coincided with E;
  -- hence the base BC will coincide with the base EF.
  -- [For if, when B coincides with E and C with F, the base BC does not coincide with the base
  -- EF, two straight lines will enclose a space: which is impossible.
  -- Therefore the base BC will coincide with EF] and will be equal to it. [C.N. 4]
  -- Thus the whole triangle ABC will coincide with the whole triangle DEF,
  -- and will be equal to it.
  -- And the remaining angles will also coincide with the remaining angles and will be equal to
  -- them,
  -- the angle ABC to the angle DEF,
  -- and the angle ACB to the angle DFE.
  -- Therefore etc.
  -- (Being) what it was required to prove.
  sorry

end Elements.BookI
