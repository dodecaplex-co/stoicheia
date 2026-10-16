import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop31
import Elements.BookI.Prop46

/-!
# Book II, Proposition 2

Euclid's text, in Heath's translation: [`heath/II/02.md`](../../heath/II/02.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut at random, the rectangle contained by the whole and both of the
segments is equal to the square on the whole. -/
theorem Prop2 {A B C : Point} (hACB : Between A C B) :
    rect A B B C + rect B A A C = sq A B := by
  -- For let the straight line AB be cut at random at the point C;
  -- I say that the rectangle contained by AB, BC together with the rectangle contained by BA,
  -- AC is equal to the square on AB.
  -- For let the square ADEB be described on AB [I. 46], and let CF be drawn through C parallel
  -- to either AD or BE. [I. 31]
  -- Then AE is equal to AF, CE.
  -- Now AE is the square on AB;
  -- AF is the rectangle contained by BA, AC, for it is contained by DA, AC, and AD is equal to
  -- AB;
  -- and CE is the rectangle AB, BC, for BE is equal to AB.
  -- Therefore the rectangle BA, AC together with the rectangle AB, BC is equal to the square
  -- on AB.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookII
