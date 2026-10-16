import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop31
import Elements.BookI.Prop46

/-!
# Book II, Proposition 3

Euclid's text, in Heath's translation: [`heath/II/03.md`](../../heath/II/03.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut at random, the rectangle contained by the whole and one of the
segments is equal to the rectangle contained by the segments and the square on the aforesaid
segment. -/
theorem Prop3 {A B C : Point} (hACB : Between A C B) :
    rect A B B C = rect A C C B + sq B C := by
  -- For let the straight line AB be cut at random at C;
  -- I say that the rectangle contained by AB, BC is equal to the rectangle contained by AC, CB
  -- together with the square on BC.
  -- For let the square CDEB be described on CB; [I. 46]
  -- let ED be drawn through to F,
  -- and through A let AF be drawn parallel to either CD or BE. [I. 31]
  -- Then AE is equal to AD, CE.
  -- Now AE is the rectangle contained by AB, BC, for it is contained by AB, BE, and BE is
  -- equal to BC;
  -- AD is the rectangle AC, CB, for DC is equal to CB;
  -- and DB is the square on CB.
  -- Therefore the rectangle contained by AB, BC is equal to the rectangle contained by AC, CB
  -- together with the square on BC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookII
