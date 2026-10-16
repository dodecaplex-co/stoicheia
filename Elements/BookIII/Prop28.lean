import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop08
import Elements.BookIII.Prop26

/-!
# Book III, Proposition 28

Euclid's text, in Heath's translation: [`heath/III/28.md`](../../heath/III/28.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In equal circles equal straight lines cut off equal circumferences, the greater equal to the
greater and the less to the less. -/
theorem Prop28 {A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hCG : OppositeSidesOf C G A B) (hFH : OppositeSidesOf F H D E) (hAB : ‖A B‖ = ‖D E‖)
    (hABC : circumference ABC A G B ≤ circumference ABC A C B)
    (hDEF : circumference DEF D H E ≤ circumference DEF D F E) :
    circumference ABC A C B = circumference DEF D F E ∧
      circumference ABC A G B = circumference DEF D H E := by
  -- Let ABC, DEF be equal circles, and in the circles let AB, DE be equal straight lines
  -- cutting off ACB, DFE as greater circumferences and AGB, DHE as lesser;
  -- I say that the greater circumference ACB is equal to the greater circumference DFE, and
  -- the less circumference AGB to DHE.
  -- For let the centres K, L of the circles be taken, and let AK, KB, DL, LE be joined.
  -- Now, since the circles are equal,
  -- the radii are also equal;
  -- therefore the two sides AK, KB are equal to the two sides DL, LE;
  -- and the base AB is equal to the base DE;
  -- therefore the angle AKB is equal to the angle DLE. [I. 8]
  -- But equal angles stand on equal circumferences, when they are at the centres; [III. 26]
  -- therefore the circumference AGB is equal to DHE.
  -- And the whole circle ABC is also equal to the whole circle DEF;
  -- therefore the circumference ACB which remains is also equal to the circumference DFE which
  -- remains.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
