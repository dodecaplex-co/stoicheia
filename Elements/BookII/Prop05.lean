import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop31
import Elements.BookI.Prop36
import Elements.BookI.Prop43
import Elements.BookI.Prop46

/-!
# Book II, Proposition 5

Euclid's text, in Heath's translation: [`heath/II/05.md`](../../heath/II/05.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut into equal and unequal segments, the rectangle contained by the
unequal segments of the whole together with the square on the straight line between the points
of section is equal to the square on the half. -/
theorem Prop5 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖) (hADB : Between A D B)
    (hDC : D ≠ C) :
    rect A D D B + sq C D = sq C B := by
  -- For let a straight line AB be cut into equal segments at C and into unequal segments at D;
  -- I say that the rectangle contained by AD, DB together with the square on CD is equal to
  -- the square on CB.
  -- For let the square CEFB be described on CB, [I. 46]
  -- and let BE be joined;
  -- through D let DG be drawn parallel to either CE or BF,
  -- through H again let KM be drawn parallel to either AB or EF,
  -- and again through A let AK be drawn parallel to either CL or BM. [I. 31]
  -- Then, since the complement CH is equal to the complement HF, [I. 43]
  -- let DM be added to each;
  -- therefore the whole CM is equal to the whole DF.
  -- But CM is equal to AL,
  -- since AC is also equal to CB; [I. 36]
  -- therefore AL is also equal to DF.
  -- Let CH be added to each;
  -- therefore the whole AH is equal to the gnomon NOP.
  -- But AH is the rectangle AD, DB, for DH is equal to DB,
  -- therefore the gnomon NOP is also equal to the rectangle AD, DB.
  -- Let LG, which is equal to the square on CD, be added to each;
  -- therefore the gnomon NOP and LG are equal to the rectangle contained by AD, DB and the
  -- square on CD.
  -- But the gnomon NOP and LG are the whole square CEFB, which is described on CB;
  -- therefore the rectangle contained by AD, DB together with the square on CD is equal to the
  -- square on CB.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookII
