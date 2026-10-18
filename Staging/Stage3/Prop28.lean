import Elements.Figure.Basics
import Elements.BookIII.Circumferences
import Elements.BookIII.Prop28
import Staging.Stage3.Definitions
import Staging.Stage3.Prop26

/-!
# Stage 3, staged: III.28 upgraded

Statements before proofs (brief 0006, stage 3). When frozen, this statement replaces
`Elements.BookIII.Prop28`; here it is `Elements.BookIII.Staging.Prop28`. Each clause now
concludes, besides the equal measures, that the circumferences are congruent: equal, for arcs,
read through Common Notion 4, which says more than Heath's words (brief 0006).

The proof is planned along Euclid's route where it can be: the angles AKB, DLE at the centres
are equal [I. 8], so the less circumferences are equal in measure and congruent [III. 26], and
the greater are equal in measure as the remainders [C.N. 3]. Two steps depart from it, as
III.26's own congruence does. The congruence of the greater circumferences cannot come by
subtraction; it comes from III.24, or III.26's clause for angles at the circumference, applied
to the greater segments. And when AB passes through the centre, the four circumferences are
semicircles and there is no angle at the centre for III.26 to use; the angle in each semicircle
is right (`Prop24.angle_type`, since III.31 comes later), and III.24 gives the congruence. The
`.1` call in Prop30 is updated with it.
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

/-- The check: today's statement of III.28 follows from the upgraded one, by the equal
measures in each clause (checked by Lean). -/
example : type_of% @Elements.BookIII.Prop28 :=
  fun hcircles hA hB hD hE hCG hFH hAB hABC hDEF =>
    ⟨(Prop28 hcircles hA hB hD hE hCG hFH hAB hABC hDEF).1.1,
      (Prop28 hcircles hA hB hD hE hCG hFH hAB hABC hDEF).2.1⟩

end Elements.BookIII.Staging
