import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookIII.Prop24

/-!
# Book III, Proposition 26

Euclid's text, in Heath's translation: [`heath/III/26.md`](../../heath/III/26.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- In equal circles equal angles stand on equal circumferences, whether they stand at the centres
or at the circumferences. -/
theorem Prop26 {A B C D E F G H K L : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :
    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      circumference ABC B K C = circumference DEF E L F) ∧
    (∠ B A C = ∠ E D F → circumference ABC B K C = circumference DEF E L F) := by
  -- Let ABC, DEF be equal circles, and in them let there be equal angles, namely at the
  -- centres the angles BGC, EHF, and at the circumferences the angles BAC, EDF;
  -- I say that the circumference BKC is equal to the circumference ELF.
  -- For let BC, EF be joined.
  -- Now, since the circles ABC, DEF are equal,
  -- the radii are equal.
  -- Thus the two straight lines BG, GC are equal to the two straight lines EH, HF;
  -- and the angle at G is equal to the angle at H;
  -- therefore the base BC is equal to the base EF. [I. 4]
  -- And, since the angle at A is equal to the angle at D,
  -- the segment BAC is similar to the segment EDF; [III. Def. 11]
  -- and they are upon equal straight lines.
  -- But similar segments of circles on equal straight lines are equal to one
  -- another; [III. 24]
  -- therefore the segment BAC is equal to EDF.
  -- But the whole circle ABC is also equal to the whole circle DEF;
  -- therefore the circumference BKC which remains is equal to the circumference ELF.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
