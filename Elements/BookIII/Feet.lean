import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop17
import Elements.BookI.Prop19
import Elements.BookIII.Prop02

/-!
# Book III: the perpendicular from the centre falls within

The propositions that compare the squares on straight lines in a circle (III.14, III.35,
III.36), and III.15 after III.14, draw a perpendicular from the centre to a straight line in
the circle, and read off the figure that it falls within the straight line, between its
ends, before III.3 bisects it there. That is said once, here (`foot_between`).

It stands after III.2, and not among the shared steps of `Elements/BookIII/Squares.lean`,
which III.1 and III.2 import. Its last step, that a point within the circle on a straight
line through two points of the circle lies between them, is System E's Circle 1, an
assumption until 26 October 2026 and since then proved after III.2, from it, in
`Elements/BookIII/Prop02.lean`, by the owner's decision of 25 October 2026; so a step that
uses it comes after III.2 too, and cites it.

The docstring ends with the propositions the step cites; the certificate walks through it
and records them.
-/

namespace Elements

open Tacit BookI

/-- **The perpendicular from the centre falls within.** The perpendicular drawn from the
centre E to a straight line AB in the circle, not through the centre, falls between
A and B. Its foot F is nearer the centre than any other point P of the straight
line: in the triangle EFP the angle at F is right, so the angle at P is less than a
right angle [I. 17], and EP, opposite the greater angle, is greater than EF [I. 19].
So F is nearer than A or than B, which are on the circle; it is within the circle,
and so between them (System E, Circle 1, proved from III.2). Euclid reads it off the
figure in III.14, III.35 and III.36, before III.3 bisects the straight line there.
[I. 17, I. 19, III. 2] -/
theorem foot_between {A B E F : Point} {α : Circle} (hE : Centre E α) (hA : OnCircle A α)
    (hB : OnCircle B α) (hE_AB : ¬ Collinear A B E) (hF : Collinear A B F)
    (hEF : ∀ P : Point, Collinear A B P → P ≠ F → ∠ E F P = ∟) : Between A F B := by
  have hAB : A ≠ B := Triangle.ne₁₂ hE_AB
  obtain ⟨M, hA_M, hB_M, hF_M⟩ := hF
  have hE_M : ¬ OnLine E M := Triangle.off_line hE_AB hA_M hB_M
  /- Any other point P of the straight line is farther from E than F is. -/
  have nearer : ∀ P : Point, OnLine P M → P ≠ F → ‖E F‖ < ‖E P‖ := by
    intro P hP_M hPF
    have hFPE : Triangle F P E := Triangle.of_line hF_M hP_M hPF.symm hE_M
    have hEFP : Triangle E F P := hFPE.cab
    have hright : ∠ E F P = ∟ := hEF P ⟨M, hA_M, hB_M, hP_M⟩ hPF
    /- The angles EFP, FPE are less than two right angles [I. 17]. -/
    have h17 := (BookI.Prop17 hEFP).1
    rw [hright] at h17
    have hP : ∠ F P E < ∠ E F P := hright ▸ Magnitude.lt_of_add_lt_add_left h17
    /- The greater angle is subtended by the greater side [I. 19]. -/
    exact BookI.Prop19 hEFP hP
  /- F is within the circle: nearer the centre than A, or than B. -/
  have hF_in : InsideCircle F α := by
    by_cases hAF : A = F
    · have hBF : B ≠ F := fun e => hAB (hAF.trans e.symm)
      exact inside_of_len_lt hE hB (nearer B hB_M hBF)
    · exact inside_of_len_lt hE hA (nearer A hA_M hAF)
  exact between_of_inside_chord hF_M hA_M hB_M hF_in hA hB hAB

end Elements
