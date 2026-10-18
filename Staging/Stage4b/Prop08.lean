import Elements.BookIII.Prop08

/-!
# Staging: III.8, nearer and more remote on either side of the diameter

Brief 0007, stage 4b. A companion of `Elements.BookIII.Prop8`, which stays as Euclid's
worked configuration: there the nearer and the more remote are compared only when both lie
on one side of the straight line DA. `Prop8.general` compares any two, on one side or on
opposite sides, within each of Euclid's two classes, and never across them.

The classes are read as today's statement reads them. A point E of the circle is on the
concave circumference when a straight line from D meets the circle at some point before
reaching E: some point H of the circle is between D and E. A point K is on the convex
circumference when the straight line from D through K meets the circle again beyond K: K
is between D and some point C of the circle. "Nearer" is the less angle at D with the ray
DA, the ray through the centre. On the concave circumference the less angle has the greater
straight line; on the convex, the less angle has the less. The two orders are kept
apart, for they disagree: the two points where one straight line from D meets the circle
make the same angle with DA, and are at different distances from D.

A straight line touching the circle from D falls on neither class: its point of contact
has no point of the circle between it and D, and none beyond it. This is a convention,
read from Euclid's "drawn through to the circle", and the comparisons say nothing of the
point of contact. The last clause, kept from today's statement, does: every point of the
circle off DA, a point of contact included, has one partner on the other side as far from
D, and no third.

`Prop8.partner` is the step the route needs: the partner on the other side makes the same
angle with DA, and is in the same class. Equal distance alone does not carry a comparison
across DA: the comparison on one side asks for the angle and the class, and the step
proves both of the partner. They move into
`Elements/BookIII/Prop08.lean` when proved, as "III.8 general", with `Prop8.partner` as a
helper before it.
-/

namespace Elements.BookIII

open Tacit

/-- **III.8, the partner equally inclined and in the same class** (a step of III.8
general). D is outside the circle ABC, and the straight line DA passes through the centre,
meeting the circle first at G and again at A. If K and B are points of the circle on
opposite sides of DA, and DB is equal to DK, then the angles ADB and ADK are equal; B is on
the convex circumference exactly when K is (the straight line from D meets the circle again
beyond it); and B is on the concave circumference exactly when K is (it meets the circle
before reaching it). Euclid's construction of B, the angle DMB made equal to KMD at the
centre M [I. 23], gives the equal angles at D by I.4, and his last step shows that no other
point is B. -/
theorem Prop8.partner {A D G K B : Point} {ABC : Circle} (hABC : ∃ M : Point, Centre M ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A)
    (hK : OnCircle K ABC) (hB : OnCircle B ABC) (hBK : OppositeSidesOf B K D A)
    (hDB : ‖D B‖ = ‖D K‖) :
    ∠ A D B = ∠ A D K ∧
    ((∃ C : Point, OnCircle C ABC ∧ Between D B C) ↔
      (∃ C : Point, OnCircle C ABC ∧ Between D K C)) ∧
    ((∃ H : Point, OnCircle H ABC ∧ Between D H B) ↔
      (∃ H : Point, OnCircle H ABC ∧ Between D H K)) := by
  sorry

/-- **III.8, general** (companion of III.8). D is outside the circle ABC, and the straight
line DA passes through the centre, meeting the circle first at G and again at A. Of the
straight lines from D to the circle, DA is greater than every other, and DG less than every
other. Of any two points E, F of the concave circumference (each with a point of the circle
between it and D) off DA, on one side of it or on opposite sides, the one making the less
angle with the ray DA at D is the farther: if the angle ADE is less than the angle ADF, then
DF is less than DE. Of any two points K, L of the convex circumference (each with a point of
the circle beyond it) off DA, the one making the less angle is the nearer: if the angle ADK
is less than the angle ADL, then DK is less than DL. Neither comparison takes a point where
a straight line from D touches the circle, for it has no point of the circle before it or
beyond it. Each point K of the circle off DA
has one partner B on the other side with DB equal to DK, and no third point of the circle is
as far from D. -/
theorem Prop8.general {A D G : Point} {ABC : Circle} (hABC : ∃ M : Point, Centre M ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A) :
    (∀ E : Point, OnCircle E ABC → E ≠ A → ‖D E‖ < ‖D A‖) ∧
    (∀ E F : Point, OnCircle E ABC → OnCircle F ABC →
      (∃ H : Point, OnCircle H ABC ∧ Between D H E) →
      (∃ L : Point, OnCircle L ABC ∧ Between D L F) →
      ¬ Collinear D A E → ¬ Collinear D A F → ∠ A D E < ∠ A D F → ‖D F‖ < ‖D E‖) ∧
    (∀ K : Point, OnCircle K ABC → K ≠ G → ‖D G‖ < ‖D K‖) ∧
    (∀ K L : Point, OnCircle K ABC → OnCircle L ABC →
      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →
      (∃ F : Point, OnCircle F ABC ∧ Between D L F) →
      ¬ Collinear D A K → ¬ Collinear D A L → ∠ A D K < ∠ A D L → ‖D K‖ < ‖D L‖) ∧
    (∀ K : Point, OnCircle K ABC → ¬ Collinear D A K → ∃ B : Point, OnCircle B ABC ∧
      OppositeSidesOf B K D A ∧ ‖D B‖ = ‖D K‖ ∧
      ∀ N : Point, OnCircle N ABC → ‖D N‖ = ‖D K‖ → N = K ∨ N = B) := by
  sorry

/-- The check: today's statement of III.8 follows from `Prop8.general` (checked by Lean).
Two points on one side of DA are off it. -/
example : type_of% @Elements.BookIII.Prop8 := by
  intro A D G ABC hABC hD hA hG hDGA hGA
  obtain ⟨hgreatest, hconcave, hleast, hconvex, hpartner⟩ :=
    Prop8.general hABC hD hA hG hDGA hGA
  exact ⟨hgreatest,
    fun E F hE hF hHE hLF hEF hlt =>
      hconcave E F hE hF hHE hLF hEF.triangle hEF.symm.triangle hlt,
    hleast,
    fun K L hK hL hKC hLF hKL hlt =>
      hconvex K L hK hL hKC hLF hKL.triangle hKL.symm.triangle hlt,
    hpartner⟩

end Elements.BookIII
