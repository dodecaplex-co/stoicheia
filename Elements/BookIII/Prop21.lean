import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Prop20

/-!
# Book III, Proposition 21

Euclid's text, in Heath's translation: [`heath/III/21.md`](../../heath/III/21.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Heath: "Under the restriction that the 'angle at the centre' used in III. 20 must be less
than two right angles, Euclid's proof of this proposition only applies to the case of a
segment greater than a semicircle" (vol. 2, p. 49). Here the angle at the centre may be two
right angles or more (`angleAtCentre`, with III.20 in `Elements/BookIII/Prop20.lean`), a
reading that is ours, after Heath's notes, and not Euclid's. So Euclid's two steps cover
every segment, the first of them argued another way in the semicircle and the less segment:
the angles BAD and BED are each half of the one angle at the centre standing on the
circumference BCD (`Prop20`), and halves of one angle are equal.
-/

namespace Elements.BookIII

open Tacit

/-- In a circle the angles in the same segment are equal to one another. -/
theorem Prop21 {A B D E : Point} {ABCD : Circle}
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
  /- III.20 takes the centre itself (`Prop20`), and the angle at the centre is made up of
     angles there (`angleAtCentre.diameter`), so nothing here takes it: Euclid's F is that
     centre, for a circle has one centre (`centre_unique`). -/
  -- Now, since the angle BFD is at the centre,
  -- and the angle BAD at the circumference,
  -- and they have the same circumference BCD as base,
  -- therefore the angle BFD is double of the angle BAD. [III. 20]
  /- The angle BFD at the centre is the one standing on the circumference BCD
     (`angleAtCentre`): the angle BFD itself when the segment BAED is greater than a
     semicircle, two right angles when it is a semicircle, and more when it is less
     (`angleAtCentre.size`). Heath says Euclid's proof, with the angle at the centre less
     than two right angles, covers only the greater segment (vol. 2, p. 49). With the
     angle at the centre of any size, III.20 carries his two steps to the semicircle and
     the less segment too, cases of his statement that his proof does not reach, so there
     this step is argued another way. -/
  have h₁ : angleAtCentre ABCD B C D = ∠ B A D + ∠ B A D :=
    Prop20 hA hB hD hCA.symm
  -- For the same reason
  -- the angle BFD is also double of the angle BED;
  have h₂ : angleAtCentre ABCD B C D = ∠ B E D + ∠ B E D :=
    Prop20 hE hB hD (hAE.symm.trans_opposite hCA.symm)
  -- therefore the angle BAD is equal to the angle BED.
  exact Magnitude.eq_of_add_self_eq (h₁.symm.trans h₂)
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
