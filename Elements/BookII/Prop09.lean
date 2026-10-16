import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop06
import Elements.BookI.Prop29
import Elements.BookI.Prop32
import Elements.BookI.Prop34
import Elements.BookI.Prop47

/-!
# Book II, Proposition 9

Euclid's text, in Heath's translation: [`heath/II/09.md`](../../heath/II/09.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut into equal and unequal segments, the squares on the unequal segments
of the whole are double of the square on the half and of the square on the straight line between
the points of section. -/
theorem Prop9 {A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖) (hADB : Between A D B)
    (hDC : D ≠ C) :
    sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D) := by
  -- For let a straight line AB be cut into equal segments at C, and into unequal segments at
  -- D;
  -- I say that the squares on AD, DB are double of the squares on AC, CD.
  -- For let CE be drawn from C at right angles to AB, and let it be made equal to either AC or
  -- CB;
  -- let EA, EB be joined,
  -- let DF be drawn through D parallel to EC,
  -- and FG through F parallel to AB,
  -- and let AF be joined.
  -- Then, since AC is equal to CE,
  -- the angle EAC is also equal to the angle AEC.
  -- And, since the angle at C is right,
  -- the remaining angles EAC, AEC are equal to one right angle. [I. 32]
  -- And they are equal;
  -- therefore each of the angles CEA, CAE is half a right angle.
  -- For the same reason
  -- each of the angles CEB, EBC is also half a right angle;
  -- therefore the whole angle AEB is right.
  -- And, since the angle GEF is half a right angle,
  -- and the angle EGF is right, for it is equal to the interior and opposite angle
  -- ECB, [I. 29]
  -- the remaining angle EFG is half a right angle; [I. 32]
  -- therefore the angle GEF is equal to the angle EFG,
  -- so that the side EG is also equal to GF. [I. 6]
  -- Again, since the angle at B is half a right angle,
  -- and the angle FDB is right, for it is again equal to the interior and opposite angle
  -- ECB, [I. 29]
  -- the remaining angle BFD is half a right angle; [I. 32]
  -- therefore the angle at B is equal to the angle DFB,
  -- so that the side FD is also equal to the side DB. [I. 6]
  -- Now, since AC is equal to CE,
  -- the square on AC is also equal to the square on CE;
  -- therefore the squares on AC, CE are double of the square on AC.
  -- But the square on EA is equal to the squares on AC, CE, for the angle ACE is
  -- right; [I. 47]
  -- therefore the square on EA is double of the square on AC.
  -- Again, since EG is equal to GF,
  -- the square on EG is also equal to the square on GF;
  -- therefore the squares on EG, GF are double of the square on GF.
  -- But the square on EF is equal to the squares on EG, GF;
  -- therefore the square on EF is double of the square on GF.
  -- But GF is equal to CD; [I. 34]
  -- therefore the square on EF is double of the square on CD.
  -- But the square on EA is also double of the square on AC;
  -- therefore the squares on AE, EF are double of the squares on AC, CD.
  -- And the square on AF is equal to the squares on AE, EF, for the angle AEF is
  -- right; [I. 47]
  -- therefore the square on AF is double of the squares on AC, CD.
  -- But the squares on AD, DF are equal to the square on AF, for the angle at D is
  -- right; [I. 47]
  -- therefore the squares on AD, DF are double of the squares on AC, CD.
  -- And DF is equal to DB;
  -- therefore the squares on AD, DB are double of the squares on AC, CD.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookII
