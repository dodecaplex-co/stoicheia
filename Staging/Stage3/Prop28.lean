import Elements.Figure.Basics
import Elements.BookIII.Circumferences
import Staging.Stage3.Definitions
import Staging.Stage3.Prop26

/-!
# Stage 3, staged: III.28 upgraded

Statements before proofs (brief 0006, stage 3). When frozen, this statement replaces
`Elements.BookIII.Prop28`; here it is `Elements.BookIII.Staging.Prop28`. Each clause now
concludes, besides the equal measures, that the circumferences are congruent; the proof goes
through the upgraded III.26, as Euclid's does. The `.1` call in Prop30 is updated with it.
-/

namespace Elements.BookIII.Staging

open Tacit

/-- In equal circles equal straight lines cut off equal circumferences, the greater equal to the
greater and the less to the less. -/
theorem Prop28 {A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hCG : OppositeSidesOf C G A B) (hFH : OppositeSidesOf F H D E) (hAB : ‖A B‖ = ‖D E‖)
    (hABC : circumference ABC A G B ≤ circumference ABC A C B)
    (hDEF : circumference DEF D H E ≤ circumference DEF D F E) :
    (circumference ABC A C B = circumference DEF D F E ∧
        Arc.Congruent ⟨ABC, A, B, C⟩ ⟨DEF, D, E, F⟩) ∧
      (circumference ABC A G B = circumference DEF D H E ∧
        Arc.Congruent ⟨ABC, A, B, G⟩ ⟨DEF, D, E, H⟩) := by
  sorry

end Elements.BookIII.Staging
