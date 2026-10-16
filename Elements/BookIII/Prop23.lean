import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop16

/-!
# Book III, Proposition 23

Euclid's text, in Heath's translation: [`heath/III/23.md`](../../heath/III/23.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- On the same straight line there cannot be constructed two similar and unequal segments of
circles on the same side. -/
theorem Prop23 {A B C D : Point} {ACB ADB : Circle} (hACB : ∃ O : Point, Centre O ACB)
    (hADB : ∃ O : Point, Centre O ADB) (hA₁ : OnCircle A ACB) (hB₁ : OnCircle B ACB)
    (hC : OnCircle C ACB) (hA₂ : OnCircle A ADB) (hB₂ : OnCircle B ADB)
    (hD : OnCircle D ADB) (hCD : SameSideOf C D A B) (hsim : ∠ A C B = ∠ A D B) :
    ACB = ADB := by
  -- For, if possible, on the same straight line AB let two similar and unequal segments of
  -- circles ACB, ADB be constructed on the same side;
  -- let ACD be drawn through, and let CB, DB be joined.
  -- Then, since the segment ACB is similar to the segment ADB,
  -- and similar segments of circles are those which admit equal angles, [III. Def. 11]
  -- the angle ACB is equal to the angle ADB, the exterior to the interior: which is
  -- impossible. [I. 16]
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
