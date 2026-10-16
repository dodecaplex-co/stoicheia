import Elements.Figure.Basics
import Elements.BookIII.Squares

/-!
# Book III, Proposition 6

Euclid's text, in Heath's translation: [`heath/III/06.md`](../../heath/III/06.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If two circles touch one another, they will not have the same centre. -/
theorem Prop6 {C F : Point} {ABC CDE : Circle} (htouch : CirclesTouch ABC CDE C) :
    ¬ (Centre F ABC ∧ Centre F CDE) := by
  -- For let the two circles ABC, CDE touch one another at the point C;
  -- I say that they will not have the same centre.
  -- For, if possible, let it be F; let FC be joined, and let FEB be drawn through at random.
  -- Then, since the point F is the centre of the circle ABC,
  -- FC is equal to FB.
  -- Again, since the point F is the centre of the circle CDE,
  -- FC is equal to FE.
  -- But FC was proved equal to FB;
  -- therefore FE is also equal to FB, the less to the greater: which is impossible.
  -- Therefore F is not the centre of the circles ABC, CDE.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookIII
