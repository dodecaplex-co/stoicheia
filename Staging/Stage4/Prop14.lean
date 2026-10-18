import Staging.Stage4.Foot

/-!
# Staging: III.14 with diameters

Brief 0006, stage 4. A companion of `Elements.BookIII.Prop14`, which stays as Euclid's
worked configuration: two straight lines in the circle, neither through the centre, each
with its perpendicular from the centre. His enunciation speaks of any straight lines in a
circle. `Prop14.general` takes each straight line's foot (`Foot`), so that a diameter, at
no distance from the centre, is included. It moves into `Elements/BookIII/Prop14.lean` when
proved, as "III.14 general".
-/

namespace Elements.BookIII

open Tacit

/-- **III.14, general** (companion of III.14). In a circle, straight lines AB, CD are equal
exactly when they are equally distant from the centre E: EF and EG are equal, F and G being
the feet of the perpendiculars from E. Two straight lines not through the centre are
Euclid's case [III. 14]; two diameters are equal, and both at no distance; and of a diameter
and a straight line not through the centre, the diameter is the greater [I. 20], and the
other is at some distance from the centre. -/
theorem Prop14.general {A B C D E F G : Point} {ABDC : Circle} (hE : Centre E ABDC)
    (hA : OnCircle A ABDC) (hB : OnCircle B ABDC) (hC : OnCircle C ABDC)
    (hD : OnCircle D ABDC) (hAB : A ≠ B) (hCD : C ≠ D) (hF : Foot E A B F)
    (hG : Foot E C D G) :
    ‖A B‖ = ‖C D‖ ↔ ‖E F‖ = ‖E G‖ := by
  sorry

/-- The check: today's statement of III.14 follows from `Prop14.general` for two straight
lines not through the centre (checked by Lean). -/
example : type_of% @Elements.BookIII.Prop14 := by
  intro A B C D E F G ABDC hE hA hB hC hD hE_AB hE_CD hF hEF hG hEG
  exact Prop14.general hE hA hB hC hD (Triangle.ne₁₂ hE_AB) (Triangle.ne₁₂ hE_CD)
    ⟨hF, fun h => absurd h hE_AB, fun _ => hEF⟩ ⟨hG, fun h => absurd h hE_CD, fun _ => hEG⟩

end Elements.BookIII
