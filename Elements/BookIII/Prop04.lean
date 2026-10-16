import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop01
import Elements.BookIII.Prop03

/-!
# Book III, Proposition 4

Euclid's text, in Heath's translation: [`heath/III/04.md`](../../heath/III/04.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If in a circle two straight lines cut one another which are not through the centre, they do not
bisect one another. -/
theorem Prop4 {A B C D E : Point} {ABCD : Circle} (hABCD : ∃ F : Point, Centre F ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hD : OnCircle D ABCD) (hAEC : Between A E C) (hBED : Between B E D)
    (hB_AC : ¬ Collinear A C B) (hAC : ∀ F : Point, Centre F ABCD → ¬ Collinear A C F)
    (hBD : ∀ F : Point, Centre F ABCD → ¬ Collinear B D F) :
    ¬ (‖A E‖ = ‖E C‖ ∧ ‖B E‖ = ‖E D‖) := by
  -- Let ABCD be a circle, and in it let the two straight lines AC, BD, which are not through
  -- the centre, cut one another at E;
  -- I say that they do not bisect one another.
  -- For, if possible, let them bisect one another, so that AE is equal to EC, and BE to ED;
  -- let the centre of the circle ABCD be taken [III. 1], and let it be F; let FE be joined.
  -- Then, since a straight line FE through the centre bisects a straight line AC not through
  -- the centre,
  -- it also cuts it at right angles; [III. 3]
  -- therefore the angle FEA is right.
  -- Again, since a straight line FE bisects a straight line BD,
  -- it also cuts it at right angles; [III. 3]
  -- therefore the angle FEB is right.
  -- But the angle FEA was also proved right;
  -- therefore the angle FEA is equal to the angle FEB, the less to the greater: which is
  -- impossible.
  -- Therefore AC, BD do not bisect one another.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
