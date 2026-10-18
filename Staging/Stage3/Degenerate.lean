import Elements.Figure.Basics
import Elements.BookI.Prop20

/-!
# Stage 3, staged: I.20's degenerate case

Statements before proofs (brief 0006, stage 3). These are shared steps that cite I.20, so
they go in a Book I helper file at or after I.20. `Elements/BookI/Helpers.lean` imports
only I.5 and is imported by I.7, so it cannot take them without a cycle: they want a new
helper file (proposed: `Elements/BookI/HelpersTriangles.lean`, named after nothing later
than I.20). Stage 4's `Prop15.le_diameter` needs `Prop20.collinear_iff` too.

`placement` uses them to carry "on the straight line AB" and "between A and B" across: both
are decided by the three distances alone.
-/

namespace Elements.BookI

open Tacit

/-- **I.20's degenerate case.** Three points lie on one straight line exactly when one of the
three distances between them is the other two together: when the triangle "collapses", I.20's
"greater" becomes "equal". (The points may coincide; then the equality holds trivially.)

To be proved from I.20 for three points off one straight line, and from `between_cases` and
`len_add_of_between` (Transfer, Diagram-segment 1) for three on one. -/
theorem Prop20.collinear_iff {A B P : Point} :
    Collinear A B P ↔
      ‖A B‖ = ‖A P‖ + ‖P B‖ ∨ ‖A P‖ = ‖A B‖ + ‖B P‖ ∨ ‖B P‖ = ‖B A‖ + ‖A P‖ := by
  sorry

/-- **Collinearity carried across.** If `AB`, `AP`, `BP` are equal to `CD`, `CQ`, `DQ`, then
`P` is on the straight line `AB` exactly when `Q` is on the straight line `CD`. Proved from
`Prop20.collinear_iff`. -/
theorem Prop20.collinear_congr {A B P C D Q : Point} (hAB : ‖A B‖ = ‖C D‖)
    (hAP : ‖A P‖ = ‖C Q‖) (hBP : ‖B P‖ = ‖D Q‖) : Collinear A B P ↔ Collinear C D Q := by
  rw [Prop20.collinear_iff, Prop20.collinear_iff, hAB, hAP, len_symm P B, hBP, len_symm B A,
    hAB, len_symm Q D, len_symm D C]

/-- **Between, by distances.** `P` lies between `A` and `B` exactly when it is neither end
and `AP`, `PB` together make `AB`. To be proved from `len_add_of_between` one way, and the
other way from `Prop20.collinear_iff` and `between_cases`, the other two orders making
something nothing. -/
theorem Prop20.between_iff {A B P : Point} :
    Between A P B ↔ ‖A P‖ ≠ 0 ∧ ‖P B‖ ≠ 0 ∧ ‖A P‖ + ‖P B‖ = ‖A B‖ := by
  sorry

/-- **Between carried across.** If `AB`, `AP`, `BP` are equal to `CD`, `CQ`, `DQ`, then `P`
is between `A` and `B` exactly when `Q` is between `C` and `D`. Proved from
`Prop20.between_iff`. -/
theorem Prop20.between_congr {A B P C D Q : Point} (hAB : ‖A B‖ = ‖C D‖)
    (hAP : ‖A P‖ = ‖C Q‖) (hBP : ‖B P‖ = ‖D Q‖) : Between A P B ↔ Between C Q D := by
  rw [Prop20.between_iff, Prop20.between_iff, hAB, hAP, len_symm P B, hBP, len_symm Q D]

end Elements.BookI
