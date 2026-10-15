import Elements.Figure.Basics
import Elements.BookI.Prop23
import Elements.BookI.Prop31
import Elements.BookI.Prop38
import Elements.BookI.Prop41

/-!
# Book I, Proposition 42

Euclid's text, in Heath's translation: [`heath/I/42.md`](../../heath/I/42.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- To construct, in a given rectilineal angle, a parallelogram equal to a given triangle. -/
theorem Prop42 {A B C D₁ D D₂ : Point} (hABC : Triangle A B C) (hD : Triangle D₁ D D₂) :
    ∃ E F G : Point, Between B E C ∧ SameSideOf F A B C ∧ Parallelogram F E C G ∧
      ∠ C E F = ∠ D₁ D D₂ ∧ quadArea F E C G = △ A B C := by
  -- Let ABC be the given triangle, and D the given rectilineal angle; thus it is required to
  -- construct in the rectilineal angle D a parallelogram equal to the triangle ABC.
  -- Let BC be bisected at E, and let AE be joined; on the straight line EC, and at the point E
  -- on it, let the angle CEF be constructed equal to the angle D; [I. 23] through A let AG be
  -- drawn parallel to EC, and [I. 31] through C let CG be drawn parallel to EF.
  -- Then FECG is a parallelogram.
  -- And, since BE is equal to EC, the triangle ABE is also equal to the triangle AEC, for they
  -- are on equal bases BE, EC and in the same parallels BC, AG; [I. 38] therefore the triangle
  -- ABC is double of the triangle AEC.
  -- But the parallelogram FECG is also double of the triangle AEC, for it has the same base
  -- with it and is in the same parallels with it; [I. 41] therefore the parallelogram FECG is
  -- equal to the triangle ABC.
  -- And it has the angle CEF equal to the given angle D.
  -- Therefore the parallelogram FECG has been constructed equal to the given triangle ABC, in
  -- the angle CEF which is equal to D.
  -- Q. E. F.
  sorry

end Elements.BookI
