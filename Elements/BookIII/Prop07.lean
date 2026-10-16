import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop04
import Elements.BookI.Prop20
import Elements.BookI.Prop23
import Elements.BookI.Prop24

/-!
# Book III, Proposition 7

Euclid's text, in Heath's translation: [`heath/III/07.md`](../../heath/III/07.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If on the diameter of a circle a point be taken which is not the centre of the circle, and from
the point straight lines fall upon the circle, that will be greatest on which the centre is, the
remainder of the same diameter will be least, and of the rest the nearer to the straight line
through the centre is always greater than the more remote, and only two equal straight lines
will fall from the point on the circle, one on each side of the least straight line. -/
theorem Prop7 {A D E F : Point} {ABCD : Circle} (hE : Centre E ABCD) (hA : OnCircle A ABCD)
    (hD : OnCircle D ABCD) (hAED : Between A E D) (hEFD : Between E F D) :
    (∀ B : Point, OnCircle B ABCD → B ≠ A → ‖F B‖ < ‖F A‖) ∧
    (∀ G : Point, OnCircle G ABCD → G ≠ D → ‖F D‖ < ‖F G‖) ∧
    (∀ B C : Point, OnCircle B ABCD → OnCircle C ABCD → SameSideOf B C A D →
      ∠ A F B < ∠ A F C → ‖F C‖ < ‖F B‖) ∧
    (∀ G : Point, OnCircle G ABCD → ¬ Collinear A D G → ∃ H : Point, OnCircle H ABCD ∧
      OppositeSidesOf H G A D ∧ ‖F H‖ = ‖F G‖ ∧
      ∀ K : Point, OnCircle K ABCD → ‖F K‖ = ‖F G‖ → K = G ∨ K = H) := by
  -- Let ABCD be a circle, and let AD be a diameter of it;
  -- on AD let a point F be taken which is not the centre of the circle, let E be the centre of
  -- the circle,
  -- and from F let straight lines FB, FC, FG fall upon the circle ABCD;
  -- I say that FA is greatest, FD is least, and of the rest FB is greater than FC, and FC than
  -- FG.
  -- For let BE, CE, GE be joined.
  -- Then, since in any triangle two sides are greater than the remaining one, [I. 20]
  -- EB, EF are greater than BF.
  -- But AE is equal to BE;
  -- therefore AF is greater than BF.
  -- Again, since BE is equal to CE,
  -- and FE is common,
  -- the two sides BE, EF are equal to the two sides CE, EF.
  -- But the angle BEF is also greater than the angle CEF;
  -- therefore the base BF is greater than the base CF. [I. 24]
  -- For the same reason
  -- CF is also greater than FG.
  -- Again, since GF, FE are greater than EG,
  -- and EG is equal to ED,
  -- GF, FE are greater than ED.
  -- Let EF be subtracted from each;
  -- therefore the remainder GF is greater than the remainder FD.
  -- Therefore FA is greatest, FD is least, and FB is greater than FC, and FC than FG.
  -- I say also that from the point F only two equal straight lines will fall on the circle
  -- ABCD, one on each side of the least FD.
  -- For on the straight line EF, and at the point E on it, let the angle FEH be constructed
  -- equal to the angle GEF [I. 23], and let FH be joined.
  -- Then, since GE is equal to EH,
  -- and EF is common,
  -- the two sides GE, EF are equal to the two sides HE, EF;
  -- and the angle GEF is equal to the angle HEF;
  -- therefore the base FG is equal to the base FH. [I. 4]
  -- I say again that another straight line equal to FG will not fall on the circle from the
  -- point F.
  -- For, if possible, let FK so fall.
  -- Then, since FK is equal to FG, and FH to FG,
  -- FK is also equal to FH,
  -- the nearer to the straight line through the centre being thus equal to the more remote:
  -- which is impossible.
  -- Therefore another straight line equal to GF will not fall from the point F upon the
  -- circle;
  -- therefore only one straight line will so fall.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
