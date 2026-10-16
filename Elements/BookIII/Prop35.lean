import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop47
import Elements.BookII.Prop05
import Elements.BookIII.Prop03

/-!
# Book III, Proposition 35

Euclid's text, in Heath's translation: [`heath/III/35.md`](../../heath/III/35.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If in a circle two straight lines cut one another, the rectangle contained by the segments of
the one is equal to the rectangle contained by the segments of the other. -/
theorem Prop35 {A B C D E : Point} {ABCD : Circle} (hABCD : ∃ F : Point, Centre F ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)
    (hD : OnCircle D ABCD) (hAEC : Between A E C) (hBED : Between B E D) :
    rect A E E C = rect D E E B := by
  -- For in the circle ABCD let the two straight lines AC, BD cut one another at the point E;
  -- I say that the rectangle contained by AE, EC is equal to the rectangle contained by DE,
  -- EB.
  -- If now AC, BD are through the centre, so that E is the centre of the circle ABCD,
  -- it is manifest that, AE, EC, DE, EB being equal,
  -- the rectangle contained by AE, EC is also equal to the rectangle contained by DE, EB.
  -- Next let AC, DB not be through the centre;
  -- let the centre of ABCD be taken, and let it be F;
  -- from F let FG, FH be drawn perpendicular to the straight lines AC, DB, and let FB, FC, FE
  -- be joined.
  -- Then, since a straight line GF through the centre cuts a straight line AC not through the
  -- centre at right angles,
  -- it also bisects it; [III. 3]
  -- therefore AG is equal to GC.
  -- Since, then, the straight line AC has been cut into equal parts at G and into unequal
  -- parts at E,
  -- the rectangle contained by AE, EC together with the square on EG is equal to the square on
  -- GC; [II. 5]
  -- Let the square on GF be added;
  -- therefore the rectangle AE, EC together with the squares on GE, GF is equal to the squares
  -- on CG, GF.
  -- But the square on FE is equal to the squares on EG, GF,
  -- and the square on FC is equal to the squares on CG, GF; [I. 47]
  -- therefore the rectangle AE, EC together with the square on FE is equal to the square on
  -- FC.
  -- And FC is equal to FB;
  -- therefore the rectangle AE, EC together with the square on EF is equal to the square on
  -- FB.
  -- For the same reason, also,
  -- the rectangle DE, EB together with the square on FE is equal to the square on FB.
  -- But the rectangle AE, EC together with the square on FE was also proved equal to the
  -- square on FB;
  -- therefore the rectangle AE, EC together with the square on FE is equal to the rectangle
  -- DE, EB together with the square on FE.
  -- Let the square on FE be subtracted from each;
  -- therefore the rectangle contained by AE, EC which remains is equal to the rectangle
  -- contained by DE, EB.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
