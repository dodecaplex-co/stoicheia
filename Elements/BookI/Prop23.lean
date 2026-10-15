import Elements.Figure.Basics
import Elements.BookI.Prop08
import Elements.BookI.Prop20
import Elements.BookI.Prop22

/-!
# Book I, Proposition 23

Euclid's text, in Heath's translation: [`heath/I/23.md`](../../heath/I/23.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

The angle is constructed on the ray from `A` through `B` (the point `F` is on it)
and on the side of `AB` where the given point `P` is, so that later propositions
can place it: I.24 on the side of `F`, I.31 on the side away from `C`.

I.22 builds the triangle `AFG` with its corner at `A` and `AF` along `AB`, from
lengths `A₁A₂ := CE`, `B₁B₂ := CD`, `C₁C₂ := DE` (so its `G` and `K` are our
`F` and `G`). It asks that two of these taken together be greater than the
third; they are the sides of the triangle `DCE`, so that is I.20, as the bracket
in I.22's enunciation says.
-/

namespace Elements.BookI

open Tacit

/-- On a given straight line and at a point on it to construct a rectilineal angle equal to a given
rectilineal angle. -/
theorem Prop23 {A B C D E P : Point} (hAB : A ≠ B) (hDCE : Triangle D C E) (hP : ¬ Collinear A B P) :
    ∃ F G : Point, OnRay F A B ∧ SameSideOf G P A B ∧ ∠ F A G = ∠ D C E := by
  -- Let AB be the given straight line, A the point on it, and the angle DCE the given
  -- rectilineal angle;
  -- thus it is required to construct on the given straight line AB, and at the point A on it,
  -- a rectilineal angle equal to the given rectilineal angle DCE.
  -- On the straight lines CD, CE respectively let the points D, E be taken at random;
  -- let DE be joined,
  -- and out of three straight lines which are equal to the three straight lines CD, DE, CE let
  -- the triangle AFG be constructed in such a way that CD is equal to AF, CE to AG, and
  -- further DE to FG. [I. 22]
  -- Then, since the two sides DC, CE are equal to the two sides FA, AG respectively,
  -- and the base DE is equal to the base FG,
  -- the angle DCE is equal to the angle FAG. [I. 8]
  -- Therefore on the given straight line AB, and at the point A on it, the rectilineal angle
  -- FAG has been constructed equal to the given rectilineal angle DCE.
  -- Q. E. F.
  sorry

end Elements.BookI
