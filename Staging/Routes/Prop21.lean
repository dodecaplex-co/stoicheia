import Elements.Figure.Basics
import Elements.BookIII.Squares
import Staging.Routes.Prop20

/-!
# Book III, Proposition 21, by Euclid's proof for every segment

This file answers issue #129 for III.21. Heath: "Under the restriction that the 'angle at
the centre' used in III. 20 must be less than two right angles, Euclid's proof of this
proposition only applies to the case of a segment greater than a semicircle" (vol. 2,
p. 49). The proof in `Elements/BookIII/Prop21.lean` therefore gives Euclid's argument for
that segment and Robert Simson's completion for the rest: AF produced to C, and Euclid's
case twice.

Here the angle at the centre may be two right angles or more (`angleAtCentre`, staged
with III.20 in `Staging/Routes/Prop20.lean`), so Euclid's own two steps cover every
segment: the angles BAD and BED are each half of the one angle at the centre standing on
the circumference BCD (`Routes.Prop20`), and halves of one angle are equal. The statement
is that of `Elements.BookIII.Prop21`, exactly.

Status: staged to replace the proof in `Elements/BookIII/Prop21.lean` when Book III's
files are next moved, once the draft it stands on, `angleAtCentre` and the general
statement of `Routes.Prop20`, has the owner's approval; that draft is not approved.
-/

namespace Elements.BookIII.Routes

open Tacit

/-- In a circle the angles in the same segment are equal to one another. -/
theorem Prop21 {A B D E : Point} {ABCD : Circle} (hABCD : ∃ F : Point, Centre F ABCD)
    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hD : OnCircle D ABCD)
    (hE : OnCircle E ABCD) (hAE : SameSideOf A E B D) :
    ∠ B A D = ∠ B E D := by
  -- Let ABCD be a circle, and let the angles BAD, BED be angles in the same segment BAED;
  -- I say that the angles BAD, BED are equal to one another.
  /- C names the circumference BCD, on the other side of BD from A and E. The angle at the
     centre reads only that side (`angleAtCentre.congr`), so any point across BD will do
     (System E, Points 6). -/
  obtain ⟨C, hCA, -⟩ := exists_oppositeSidesOf hAE.triangle []
  -- For let the centre of the circle ABCD be taken, and let it be F; let BF, FD be joined.
  obtain ⟨F, hF⟩ := hABCD
  -- Now, since the angle BFD is at the centre,
  -- and the angle BAD at the circumference,
  -- and they have the same circumference BCD as base,
  -- therefore the angle BFD is double of the angle BAD. [III. 20]
  /- The angle BFD at the centre is the one standing on the circumference BCD
     (`angleAtCentre`): the angle BFD itself when the segment BAED is greater than a
     semicircle, two right angles when it is a semicircle, and more when it is less
     (`angleAtCentre.size`). Heath says Euclid's proof, with the angle at the centre less
     than two right angles, covers only the greater segment (vol. 2, p. 49). With the
     angle at the centre of any size, the general III.20 carries his two steps to the
     semicircle and the less segment too, the cases his figure leaves aside. -/
  have h₁ : angleAtCentre ABCD B C D = ∠ B A D + ∠ B A D := Prop20 hF hA hB hD hCA.symm
  -- For the same reason
  -- the angle BFD is also double of the angle BED;
  have h₂ : angleAtCentre ABCD B C D = ∠ B E D + ∠ B E D :=
    Prop20 hF hE hB hD (hAE.symm.trans_opposite hCA.symm)
  -- therefore the angle BAD is equal to the angle BED.
  exact Magnitude.eq_of_add_self_eq (h₁.symm.trans h₂)
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII.Routes
