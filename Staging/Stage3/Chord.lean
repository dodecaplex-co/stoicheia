import Elements.Figure.Basics
import Staging.Stage3.Definitions

/-!
# Stage 3, staged: Book Zero facts for arcs

Statements before proofs (brief 0006, stage 3). Facts every arc needs, proved (or to be
proved) from the foundations alone; destined for a Book Zero file (`Elements/Figure/`), which
cites no proposition.
-/

namespace Elements

open Tacit

/-- **A straight line in a circle, along its own line.** For two different points A, B of a
circle and a point P of the straight line AB: P is on the circle exactly when it is A or B,
and within the circle exactly when it lies between them. Proved from `Triangle.of_onCircle`
and System E's rules for a straight line in a circle (Circle 1 and 2). III.24 uses it for the
points of the base. -/
theorem chord_cases {A B P : Point} {α : Circle} (hA : OnCircle A α) (hB : OnCircle B α)
    (hAB : A ≠ B) (hP : Collinear A B P) :
    (OnCircle P α ↔ P = A ∨ P = B) ∧ (InsideCircle P α ↔ Between A P B) := by
  refine ⟨⟨fun hPα => Classical.byContradiction fun hne => ?_, ?_⟩,
    ⟨fun hin => ?_, fun h => inside_of_between (Or.inr hA) (Or.inr hB) h⟩⟩
  · exact Triangle.of_onCircle hA hB hPα hAB (fun e => hne (Or.inr e.symm))
      (fun e => hne (Or.inl e.symm)) hP
  · rintro (h | h)
    · rw [h]; exact hA
    · rw [h]; exact hB
  · obtain ⟨L, hA_L, hB_L, hP_L⟩ := hP
    exact between_of_inside_chord hP_L hA_L hB_L hin hA hB hAB

/-- **A straight line from within the base meets the arc.** For a drawn arc, a ray from a point
X between the ends of the base, through a point Y on the arc's side, meets the arc.

To be proved: X is within the circle (System E, Circle 2), so the straight line XY, produced
beyond X backwards and then forwards, meets the circle on Y's side (Intersections 5, with
Pasch 3 for the side). III.25's construction core reads this off the segment it is given. -/
theorem Arc.meets {a : Arc} (ha : a.Drawn) {X Y : Point} (hX : Between a.B X a.C)
    (hY : SameSideOf Y a.K a.B a.C) : ∃ Q : Point, OnArc Q a ∧ OnRay Q X Y := by
  sorry

end Elements
