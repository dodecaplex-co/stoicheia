import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop26
import Elements.BookI.Prop29

/-!
# Book I, Proposition 34

Euclid's text, in Heath's translation: [`heath/I/34.md`](../../heath/I/34.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- In parallelogrammic areas the opposite sides and angles are equal to one another, and the
diameter bisects the areas. -/
theorem Prop34 {A B C D : Point} (h : Parallelogram A C D B) :
    ‖A B‖ = ‖C D‖ ∧ ‖A C‖ = ‖B D‖ ∧ ∠ B A C = ∠ C D B ∧ ∠ A B D = ∠ A C D ∧
      △ A B C = △ D C B := by
  -- Let ACDB be a parallelogrammic area, and BC its diameter;
  -- I say that the opposite sides and angles of the parallelogram ACDB are equal to one
  -- another, and the diameter BC bisects it.
  -- For, since AB is parallel to CD,
  -- and the straight line BC has fallen upon them,
  -- the alternate angles ABC, BCD are equal to one another. [I. 29]
  -- Again, since AC is parallel to BD,
  -- and BC has fallen upon them,
  -- the alternate angles ACB, CBD are equal to one another. [I. 29]
  -- Therefore ABC, DCB are two triangles having the two angles ABC, BCA equal to the two
  -- angles DCB, CBD respectively, and one side equal to one side, namely that adjoining the
  -- equal angles and common to both of them, BC;
  -- therefore they will also have the remaining sides equal to the remaining sides
  -- respectively, and the remaining angle to the remaining angle; [I. 26]
  -- therefore the side AB is equal to CD,
  -- and AC to BD,
  -- and further the angle BAC is equal to the angle CDB.
  -- And, since the angle ABC is equal to the angle BCD,
  -- and the angle CBD to the angle ACB,
  -- the whole angle ABD is equal to the whole angle ACD. [C.N. 2]
  -- And the angle BAC was also proved equal to the angle CDB.
  -- Therefore in parallelogrammic areas the opposite sides and angles are equal to one
  -- another.
  -- I say, next, that the diameter also bisects the areas.
  -- For, since AB is equal to CD,
  -- and BC is common,
  -- the two sides AB, BC are equal to the two sides DC, CB respectively;
  -- and the angle ABC is equal to the angle BCD;
  -- therefore the base AC is also equal to DB,
  -- and the triangle ABC is equal to the triangle DCB. [I. 4]
  -- Therefore the diameter BC bisects the parallelogram ACDB.
  -- Q. E. D.
  sorry

end Elements.BookI
