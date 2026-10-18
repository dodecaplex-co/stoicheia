import Elements.Figure.Basics
import Elements.BookIII.Circumferences
import Elements.BookIII.Prop26
import Staging.Stage3.Definitions
import Staging.Stage3.Chord
import Staging.Stage3.Prop24

/-!
# Stage 3, staged: III.26 upgraded

Statements before proofs (brief 0006, stage 3). When frozen, this statement replaces
`Elements.BookIII.Prop26`; here it is `Elements.BookIII.Staging.Prop26`. Each clause now
concludes, besides the equal measures it concludes today, that the circumferences are
congruent, so that "in equal circles" does real work. "Equal circumferences" is read as equal
in measure and congruent, which says more than Heath's words; equal, for arcs, is read through
Common Notion 4 (brief 0006).

The proof is planned along Euclid's route for the measures: the segments BAC, EDF are
congruent [III. 24], so their circumferences are equal in measure (`Prop24.equalMeasure`),
and the remainders BKC, ELF are equal in measure, the wholes being equal [C.N. 3]. The
congruence of the remainders cannot come by subtraction: it comes from III.24 applied to the
remaining segments, which are similar, their angles making two right angles with the equal
angles at A and D [III. 22], with `Arc.Congruent.congr_side` for the naming points K and L. That
is a mild departure from Euclid's "whole minus part", noted where it happens. The `.1` calls in
Prop27 and Prop28 are updated with it.
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

/-- The check: today's statement of III.26 follows from the upgraded one, by the equal
measures in each clause (checked by Lean). -/
example : type_of% @Elements.BookIII.Prop26 :=
  fun hcircles hG hH hA hB hC hD hE hF hAK hDL =>
    ⟨fun hGK hHL h => ((Prop26 hcircles hG hH hA hB hC hD hE hF hAK hDL).1 hGK hHL h).1,
      fun h => ((Prop26 hcircles hG hH hA hB hC hD hE hF hAK hDL).2 h).1⟩

end Elements.BookIII.Staging
