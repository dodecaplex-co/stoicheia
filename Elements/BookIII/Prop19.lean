import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop18

/-!
# Book III, Proposition 19

Euclid's text, in Heath's translation: [`heath/III/19.md`](../../heath/III/19.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If a straight line touch a circle, and from the point of contact a straight line be drawn at
right angles to the tangent, the centre of the circle will be on the straight line so drawn. -/
theorem Prop19 {A C D E : Point} {ABC : Circle} (hC : OnCircle C ABC) (hDE : Touches D E ABC)
    (hCDE : Collinear D E C) (hA : ¬ Collinear D E A)
    (hCA : ∀ P : Point, Collinear D E P → P ≠ C → ∠ A C P = ∟) :
    ∀ F : Point, Centre F ABC → Collinear A C F := by
  -- For let a straight line DE touch the circle ABC at the point C, and from C let CA be drawn
  -- at right angles to DE;
  -- I say that the centre of the circle is on AC.
  -- For suppose it is not, but, if possible, let F be the centre,
  -- and let CF be joined.
  -- Since a straight line DE touches the circle ABC,
  -- and FC has been joined from the centre to the point of contact,
  -- FC is perpendicular to DE; [III. 18]
  -- therefore the angle FCE is right.
  -- But the angle ACE is also right;
  -- therefore the angle FCE is equal to the angle ACE,
  -- the less to the greater: which is impossible.
  -- Therefore F is not the centre of the circle ABC.
  -- Similarly we can prove that neither is any other point except a point on AC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
