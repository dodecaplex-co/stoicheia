import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookIII.Circumferences
import Elements.BookI.Prop04
import Elements.BookIII.Prop28

/-!
# Book III, Proposition 30

Euclid's text, in Heath's translation: [`heath/III/30.md`](../../heath/III/30.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- To bisect a given circumference. -/
theorem Prop30 {A B : Point} {ADB : Circle} (hADB : ∃ O : Point, Centre O ADB) (hA : OnCircle A ADB)
    (hB : OnCircle B ADB) :
    ∀ P : Point, ¬ Collinear A B P → ∃ D : Point, OnCircle D ADB ∧ SameSideOf D P A B ∧
      standing ADB A B D = standing ADB D A B := by
  -- Let ADB be the given circumference;
  -- thus it is required to bisect the circumference ADB.
  -- Let AB be joined and bisected at C; from the point C let CD be drawn at right angles to
  -- the straight line AB, and let AD, DB be joined.
  -- Then, since AC is equal to CB,
  -- and CD is common,
  -- the two sides AC, CD are equal to the two sides BC, CD;
  -- and the angle ACD is equal to the angle BCD, for each is right;
  -- therefore the base AD is equal to the base DB. [I. 4]
  -- But equal straight lines cut off equal circumferences, the greater equal to the greater,
  -- and the less to the less; [III. 28]
  -- and each of the circumferences AD, DB is less than a semicircle;
  -- therefore the circumference AD is equal to the circumference DB.
  -- Therefore the given circumference has been bisected at the point D.
  -- Q. E. F.
  sorry

end Elements.BookIII
