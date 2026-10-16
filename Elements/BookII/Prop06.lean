import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop31
import Elements.BookI.Prop36
import Elements.BookI.Prop43
import Elements.BookI.Prop46

/-!
# Book II, Proposition 6

Euclid's text, in Heath's translation: [`heath/II/06.md`](../../heath/II/06.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be bisected and a straight line be added to it in a straight line, the
rectangle contained by the whole with the added straight line and the added straight line
together with the square on the half is equal to the square on the straight line made up of the
half and the added straight line. -/
theorem Prop6 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖)
    (hABD : Between A B D) :
    rect A D D B + sq C B = sq C D := by
  -- For let a straight line AB be bisected at the point C, and let a straight line BD be added
  -- to it in a straight line;
  -- I say that the rectangle contained by AD, DB together with the square on CB is equal to
  -- the square on CD.
  -- For let the square CEFD be described on CD, [I. 46]
  -- and let DE be joined;
  -- through the point B let BG be drawn parallel to either EC or DF,
  -- through the point H let KM be drawn parallel to either AB or EF,
  -- and further through A let AK be drawn parallel to either CL or DM. [I. 31]
  -- Then, since AC is equal to CB,
  -- AL is also equal to CH. [I. 36]
  -- But CH is equal to HF. [I. 43]
  -- Therefore AL is also equal to HF.
  -- Let CM be added to each;
  -- therefore the whole AM is equal to the gnomon NOP.
  -- But AM is the rectangle AD, DB,
  -- for DM is equal to DB;
  -- therefore the gnomon NOP is also equal to the rectangle AD, DB.
  -- Let LG, which is equal to the square on BC, be added to each;
  -- therefore the rectangle contained by AD, DB together with the square on CB is equal to the
  -- gnomon NOP and LG.
  -- But the gnomon NOP and LG are the whole square CEFD, which is described on CD;
  -- therefore the rectangle contained by AD, DB together with the square on CB is equal to the
  -- square on CD.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookII
