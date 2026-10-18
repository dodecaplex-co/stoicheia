import Elements.BookIII.Prop17

/-!
# Staging: III.17, from a point not within the circle

Brief 0007, stage 4b. A companion of `Elements.BookIII.Prop17`, which stays as Euclid's
worked configuration: the given point A outside the circle, and B the point of contact. His
enunciation says "a given point"; from a point within the circle no straight line touches
it, and a point on the circumference Euclid leaves to III.16's porism, as Heath explains
(vol. 2, p. 44). `Prop17.general` takes every point not within the circle: outside it, by
Euclid's construction, or on it, where the straight line drawn at right angles to the
radius touches by III.16's porism.

The conclusion is `∃ X, Touches A X BCD`: a straight line AX touching the circle. Today's
form, a point B of the circle with `Touches A B BCD`, cannot hold for A on the circle,
since the point of contact is then A itself and `Touches` (Definition III.2) asks for two
different points to name its straight line. `Touches` already says that the straight line
meets the circle, and its witness is the point of contact, which may be A.

For a circle with a centre, not being within the circle is the condition for the problem
to have a solution, and `Prop17.inside` states the other half: from a point within the
circle, no straight line touches it. It is a lemma, not a companion, since it generalizes
no clause of the enunciation; the record and the page state "not within" as the condition
for a solution. When proved, `Prop17.general` moves into `Elements/BookIII/Prop17.lean` as
"III.17 general", and `Prop17.inside` after it, with no certificate entry of its own.
-/

namespace Elements.BookIII

open Tacit

/-- **III.17, general** (companion of III.17). Given a circle BCD with a centre, and a point
A not within it, there is a point X such that the straight line AX touches the circle: it
meets the circle, and does not cut it. A may be outside the circle, and then the point of
contact is another point (Euclid's case, today's `Prop17`); or on it, and then the point of
contact is A itself: the proof draws AX at right angles to the radius EA (I.11), and it
touches by III.16's porism. Euclid leaves that case out, Heath explains, because III.16's
porism so directly indicates its construction (vol. 2, p. 44); the construction is not on
Euclid's page. -/
theorem Prop17.general {A : Point} {BCD : Circle} (hBCD : ∃ E : Point, Centre E BCD)
    (hA : ¬ InsideCircle A BCD) :
    ∃ X : Point, Touches A X BCD := by
  by_cases hon : OnCircle A BCD
  · /- A is on the circle. Its centre E is within it, so E is not A. -/
    obtain ⟨E, hE⟩ := hBCD
    have hEA : E ≠ A := (ne_of_centre_of_on hE hon).symm
    obtain ⟨L, hE_L, hA_L⟩ := Postulate1 E A hEA
    /- Choose Q off EA, then draw AX at right angles to EA on Q's side by I.11. -/
    obtain ⟨Q, hQ, -⟩ := exists_off_line hEA []
    obtain ⟨X, hXQ, hX⟩ := BookI.Prop11 hEA ⟨L, hE_L, hA_L, hA_L⟩ hQ
    have hEAX : ∠ E A X = ∟ := hX E ⟨L, hE_L, hA_L, hE_L⟩ hEA
    /- X is off EA, since it lies on Q's side; AX touches the circle by III.16's porism. -/
    exact ⟨X, Prop16.porism hE hon hXQ.triangle hEAX⟩
  · /- A is outside the circle, so III.17 gives its point of contact B. -/
    obtain ⟨B, -, hB⟩ := Prop17 hBCD ⟨hA, hon⟩
    exact ⟨B, hB⟩

/-- **III.17, from a point within** (a lemma beside III.17). From a point A within the
circle BCD, no point X makes the straight line AX touch the circle, since a straight line
through a point within a circle cuts it (`Touches.not_inside`). So, for a circle with a
centre, a point not within it is exactly the condition under which `Prop17.general` draws a
straight line touching it. -/
theorem Prop17.inside {A : Point} {BCD : Circle} (hA : InsideCircle A BCD) :
    ¬ ∃ X : Point, Touches A X BCD := by
  rintro ⟨X, hAX⟩
  /- A lies on AX, and no point of a straight line that touches a circle lies within it. -/
  obtain ⟨L, hA_L, hX_L⟩ := Postulate1 A X hAX.1
  exact hAX.not_inside ⟨L, hA_L, hX_L, hA_L⟩ hA

/-- The check: today's statement of III.17 follows from `Prop17.general` (checked by Lean).
`Prop17.general` is proved above, so the check derives today's III.17 from the companion,
and shows that the two statements fit. A is outside the circle,
so the point where AX meets the circle is not A, and the straight line it names with A is
AX. -/
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
