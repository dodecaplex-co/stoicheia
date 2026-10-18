import Elements.BookIII.Prop17

/-!
# Staging: III.17, from a point not within the circle

Brief 0007, stage 4b. A companion of `Elements.BookIII.Prop17`, which stays as Euclid's
worked configuration: the given point A outside the circle, and B the point of contact. His
enunciation says "a given point"; from a point within the circle no straight line touches
it, and a point on the circumference Euclid leaves to III.16's porism, as Heath explains
(vol. 2, p. 44). `Prop17.general` takes every point not within the circle: outside it, by
Euclid's construction, or on it, where the straight line drawn at right angles to the
radius touches [III. 16, Por.].

The conclusion is `∃ X, Touches A X BCD`: a straight line AX touching the circle. Today's
form, a point B of the circle with `Touches A B BCD`, cannot hold for A on the circle,
since the point of contact is then A itself and `Touches` (Definition III.2) asks for two
different points to name its straight line. `Touches` already says that the straight line
meets the circle, and its witness is the point of contact, which may be A.

Not being within the circle is the condition for the problem to have a solution, and
`Prop17.inside` states the other half: from a point within the circle, no straight line
touches it. They move into `Elements/BookIII/Prop17.lean` when proved, as "III.17 general"
and "III.17 inside".
-/

namespace Elements.BookIII

open Tacit

/-- **III.17, general** (companion of III.17). Given a circle BCD with a centre, and a point
A not within it, there is a point X such that the straight line AX touches the circle: it
meets the circle, and does not cut it. A may be outside the circle, and then the point of
contact is another point (Euclid's case [III. 17]); or on it, and then the point of contact
is A, and AX is at right angles to the radius at A [III. 16, Por.]. -/
theorem Prop17.general {A : Point} {BCD : Circle} (hBCD : ∃ E : Point, Centre E BCD)
    (hA : ¬ InsideCircle A BCD) :
    ∃ X : Point, Touches A X BCD := by
  sorry

/-- **III.17, inside** (companion of III.17). From a point A within the circle BCD, no
straight line touches it: every straight line AX meets the circle at two points. So a point
not within the circle is exactly the condition under which `Prop17.general` draws a
straight line touching it. -/
theorem Prop17.inside {A : Point} {BCD : Circle} (hA : InsideCircle A BCD) :
    ¬ ∃ X : Point, Touches A X BCD := by
  sorry

/-- The check: today's statement of III.17 follows from `Prop17.general` (checked by Lean).
A is outside the circle, so the point where AX meets the circle is not A, and the straight
line it names with A is AX. -/
example : type_of% @Elements.BookIII.Prop17 := by
  intro A BCD hBCD hA
  obtain ⟨X, hAX, hX⟩ := Prop17.general hBCD hA.1
  obtain ⟨L, hA_L, hX_L⟩ := Postulate1 A X hAX
  obtain ⟨⟨B, hB_L, hB⟩, -⟩ := hX L hA_L hX_L
  have hAB : A ≠ B := fun e => hA.2 (e ▸ hB)
  refine ⟨B, hB, hAB, fun M hA_M hB_M => ?_⟩
  obtain rfl : L = M := line_unique hAB hA_L hB_L hA_M hB_M
  exact hX L hA_L hX_L

end Elements.BookIII
