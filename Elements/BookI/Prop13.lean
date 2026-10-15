import Elements.Figure.Basics
import Elements.BookI.Prop11

/-!
# Book I, Proposition 13

Euclid's text, in Heath's translation: [`heath/I/13.md`](../../heath/I/13.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- If a straight line set up on a straight line make angles, it will make either two right angles
or angles equal to two right angles. -/
theorem Prop13 {A B C D : Point} (hCBD : Between C B D) (hA : ¬ Collinear C D A) :
    ∠ C B A + ∠ A B D = ∟ + ∟ := by
  -- For let any straight line AB set up on the straight line CD make the angles CBA, ABD;
  -- I say that the angles CBA, ABD are either two right angles or equal to two right angles.
  -- Now, if the angle CBA is equal to the angle ABD,
  -- they are two right angles. [Def. 10]
  -- But, if not, let BE be drawn from the point B at right angles to CD; [I. 11]
  -- therefore the angles CBE, EBD are two right angles.
  -- Then, since the angle CBE is equal to the two angles CBA, ABE,
  -- let the angle EBD be added to each;
  -- therefore the angles CBE, EBD are equal to the three angles CBA, ABE, EBD. [C.N. 2]
  -- Again, since the angle DBA is equal to the two angles DBE, EBA,
  -- let the angle ABC be added to each;
  -- therefore the angles DBA, ABC are equal to the three angles DBE, EBA, ABC. [C.N. 2]
  -- But the angles CBE, EBD were also proved equal to the same three angles;
  -- and things which are equal to the same thing are also equal to one another; [C.N. 1]
  -- therefore the angles CBE, EBD are also equal to the angles DBA, ABC.
  -- But the angles CBE, EBD are two right angles;
  -- therefore the angles DBA, ABC are also equal to two right angles.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
