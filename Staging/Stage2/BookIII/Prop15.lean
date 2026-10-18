import Staging.Stage2.BookIII.Foot

/-!
# Staging: III.15, its two clauses for every straight line in the circle

Brief 0006, stage 4. Companions of `Elements.BookIII.Prop15`, which stays as Euclid's
worked configuration: a diameter AD and two straight lines BC, FG, neither through the
centre. His enunciation has two clauses. "The diameter is greatest" is
`Prop15.le_diameter`, for every straight line in the circle, with its equality case: no
straight line is greater than the diameter, and only one through the centre is equal to it.
"Of the rest the nearer to the centre is always greater than the more remote" is
`Prop15.nearer`, with distances measured to the feet of the perpendiculars (`Foot`), so that
the nearer may be a diameter. They move into `Elements/BookIII/Prop15.lean` when proved, as
"III.15 le_diameter" and "III.15 nearer".
-/

namespace Elements.BookIII

open Tacit

/-- **III.15, the diameter is greatest** (companion of III.15). Of the straight lines in a
circle, none is greater than the diameter AD, and a straight line BC in it is equal to the
diameter exactly when it passes through the centre E: when it is a diameter too. If BC is
not through the centre, BE, EC together are greater than BC [I. 20], and they are equal to
AD. BC may be a point, and then it is nothing. -/
theorem Prop15.le_diameter {A B C D E : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) :
    ‖B C‖ ≤ ‖A D‖ ∧ (‖B C‖ = ‖A D‖ ↔ Between B E C) := by
  sorry

/-- **III.15, the nearer is greater** (companion of III.15). Of two straight lines BC, FG in
a circle, the one nearer to the centre E is the greater: if EH is less than EK, H and K being
the feet of the perpendiculars from E, then FG is less than BC. The nearer, BC, may be a
diameter, at no distance; the more remote cannot be. -/
theorem Prop15.nearer {B C E F G H K : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hF : OnCircle F ABCD)
    (hG : OnCircle G ABCD) (hBC : B ≠ C) (hH : Foot E B C H) (hK : Foot E F G K)
    (hnearer : ‖E H‖ < ‖E K‖) :
    ‖F G‖ < ‖B C‖ := by
  sorry

/-- The check: today's statement of III.15 follows from `Prop15.le_diameter` and
`Prop15.nearer`, exactly. BC is not through the centre, so it is less than the diameter. -/
example : type_of% @Elements.BookIII.Prop15 := by
  intro A B C D E F G H K ABCD hE hA hD hAED hB hC hF hG hE_BC hE_FG hH hEH hK hEK hnearer
  obtain ⟨hle, hiff⟩ := Prop15.le_diameter hE hA hD hAED hB hC
  refine ⟨?_, Prop15.nearer hE hB hC hF hG (Triangle.ne₁₂ hE_BC)
    ⟨hH, fun h => absurd h hE_BC, fun _ => hEH⟩ ⟨hK, fun h => absurd h hE_FG, fun _ => hEK⟩
    hnearer⟩
  have hne : ‖B C‖ ≠ ‖A D‖ := fun h => by
    obtain ⟨L, hB_L, hE_L, hC_L⟩ := collinear_of_between (hiff.mp h)
    exact hE_BC ⟨L, hB_L, hC_L, hE_L⟩
  rcases lt_trichotomy ‖B C‖ ‖A D‖ with h | h | h
  · exact h
  · exact absurd h hne
  · exact absurd h hle

end Elements.BookIII
