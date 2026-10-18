import Elements.Figure.Basics
import Elements.BookIII.Circumferences
import Staging.Stage3.Definitions
import Staging.Stage3.Prop24

/-!
# Stage 3, staged: III.26 upgraded

Statements before proofs (brief 0006, stage 3). When frozen, this statement replaces
`Elements.BookIII.Prop26`; here it is `Elements.BookIII.Staging.Prop26`. Each clause now
concludes, besides the equal measures it concludes today, that the circumferences are
congruent, so that "in equal circles" does real work. The proof is planned through III.24 on
the remaining segments, a mild departure from Euclid's "whole minus part", noted where it
happens. The `.1` calls in Prop27, Prop28 and Prop30 are updated with it.
-/

namespace Elements.BookIII.Staging

open Tacit

/-- In equal circles equal angles stand on equal circumferences, whether they stand at the centres
or at the circumferences. -/
theorem Prop26 {A B C D E F G H K L : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :
    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩) ∧
    (∠ B A C = ∠ E D F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩) := by
  sorry

end Elements.BookIII.Staging
