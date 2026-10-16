import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop47
import Elements.BookII.Prop06
import Elements.BookIII.Prop03
import Elements.BookIII.Prop18

/-!
# Book III, Proposition 36

Euclid's text, in Heath's translation: [`heath/III/36.md`](../../heath/III/36.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If a point be taken outside a circle and from it there fall on the circle two straight lines,
and if one of them cut the circle and the other touch it, the rectangle contained by the whole
of the straight line which cuts the circle and the straight line intercepted on it outside
between the point and the convex circumference will be equal to the square on the tangent. -/
theorem Prop36 {A B C D : Point} {ABC : Circle} (hABC : ∃ F : Point, Centre F ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hDCA : Between D C A) (hDB : Touches D B ABC) :
    rect A D D C = sq D B := by
  -- For let a point D be taken outside the circle ABC,
  -- and from D let the two straight lines DCA, DB fall on the circle ABC; let DCA cut the
  -- circle ABC and let BD touch it;
  -- I say that the rectangle contained by AD, DC is equal to the square on DB.
  -- Then DCA is either through the centre or not through the centre.
  -- First let it be through the centre, and let F be the centre of the circle ABC;
  -- let FB be joined;
  -- therefore the angle FBD is right. [III. 18]
  -- And, since AC has been bisected at F, and CD is added to it,
  -- the rectangle AD, DC together with the square on FC is equal to the square on FD. [II. 6]
  -- But FC is equal to FB;
  -- therefore the rectangle AD, DC together with the square on FB is equal to the square on
  -- FD.
  -- And the squares on FB, BD are equal to the square on FD; [I. 47]
  -- therefore the rectangle AD, DC together with the square on FB is equal to the squares on
  -- FB, BD.
  -- Let the square on FB be subtracted from each;
  -- therefore the rectangle AD, DC which remains is equal to the square on the tangent DB.
  -- Again, let DCA not be through the centre of the circle ABC;
  -- let the centre E be taken, and from E let EF be drawn perpendicular to AC;
  -- let EB, EC, ED be joined.
  -- Then the angle EBD is right. [III. 18]
  -- And, since a straight line EF through the centre cuts a straight line AC not through the
  -- centre at right angles,
  -- it also bisects it; [III. 3]
  -- therefore AF is equal to FC.
  -- Now, since the straight line AC has been bisected at the point F, and CD is added to it,
  -- the rectangle contained by AD, DC together with the square on FC is equal to the square on
  -- FD. [II. 6]
  -- Let the square on FE be added to each;
  -- therefore the rectangle AD, DC together with the squares on CF, FE is equal to the squares
  -- on FD, FE.
  -- But the square on EC is equal to the squares on CF, FE, for the angle EFC is
  -- right; [I. 47]
  -- and the square on ED is equal to the squares on DF, FE;
  -- therefore the rectangle AD, DC together with the square on EC is equal to the square on
  -- ED.
  -- And EC is equal to EB;
  -- therefore the rectangle AD, DC together with the square on EB is equal to the square on
  -- ED.
  -- But the squares on EB, BD are equal to the square on ED, for the angle EBD is
  -- right; [I. 47]
  -- therefore the rectangle AD, DC together with the square on EB is equal to the squares on
  -- EB, BD.
  -- Let the square on EB be subtracted from each;
  -- therefore the rectangle AD, DC which remains is equal to the square on DB.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
