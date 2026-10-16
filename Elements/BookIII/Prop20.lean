import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop05
import Elements.BookI.Prop32

/-!
# Book III, Proposition 20

Euclid's text, in Heath's translation: [`heath/III/20.md`](../../heath/III/20.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In a circle the angle at the centre is double of the angle at the circumference, when the angles
have the same circumference as base. -/
theorem Prop20 {A B C E : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hEA : SameSideOf E A B C) :
    ∠ B E C = ∠ B A C + ∠ B A C := by
  -- Let ABC be a circle, let the angle BEC be an angle at its centre, and the angle BAC an
  -- angle at the circumference, and let them have the same circumference BC as base;
  -- I say that the angle BEC is double of the angle BAC.
  -- For let AE be joined and drawn through to F.
  -- Then, since EA is equal to EB,
  -- the angle EAB is also equal to the angle EBA; [I. 5]
  -- therefore the angles EAB, EBA are double of the angle EAB.
  -- But the angle BEF is equal to the angles EAB, EBA; [I. 32]
  -- therefore the angle BEF is also double of the angle EAB.
  -- For the same reason
  -- the angle FEC is also double of the angle EAC.
  -- Therefore the whole angle BEC is double of the whole angle BAC.
  -- Again let another straight line be inflected, and let there be another angle BDC; let DE
  -- be joined and produced to G.
  -- Similarly then we can prove that the angle GEC is double of the angle EDC,
  -- of which the angle GEB is double of the angle EDB;
  -- therefore the angle BEC which remains is double of the angle BDC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
