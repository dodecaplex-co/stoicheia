import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop43
import Elements.BookI.Prop46

/-!
# Book II, Proposition 7

Euclid's text, in Heath's translation: [`heath/II/07.md`](../../heath/II/07.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut at random, the square on the whole and that on one of the segments
both together are equal to twice the rectangle contained by the whole and the said segment and
the square on the remaining segment. -/
theorem Prop7 {A B C : Point} (hACB : Between A C B) :
    sq A B + sq B C = rect A B B C + rect A B B C + sq C A := by
  -- For let a straight line AB be cut at random at the point C;
  -- I say that the squares on AB, BC are equal to twice the rectangle contained by AB, BC and
  -- the square on CA.
  -- For let the square ADEB be described on AB, [I. 46]
  -- and let the figure be drawn.
  -- Then, since AG is equal to GE, [I. 43]
  -- let CF be added to each;
  -- therefore the whole AF is equal to the whole CE.
  -- Therefore AF, CE are double of AF.
  -- But AF, CE are the gnomon KLM and the square CF;
  -- therefore the gnomon KLM and the square CF are double of AF.
  -- But twice the rectangle AB, BC is also double of AF; for BF is equal to BC;
  -- therefore the gnomon KLM and the square CF are equal to twice the rectangle AB, BC.
  -- Let DG, which is the square on AC, be added to each;
  -- therefore the gnomon KLM and the squares BG, GD are equal to twice the rectangle contained
  -- by AB, BC and the square on AC.
  -- But the gnomon KLM and the squares BG, GD are the whole ADEB and CF,
  -- which are squares described on AB, BC;
  -- therefore the squares on AB, BC are equal to twice the rectangle contained by AB, BC
  -- together with the square on AC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookII
