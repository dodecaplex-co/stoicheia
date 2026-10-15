import Elements.Figure.Basics
import Elements.BookI.Prop34

/-!
# Book I, Proposition 43

Euclid's text, in Heath's translation: [`heath/I/43.md`](../../heath/I/43.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- In any parallelogram the complements of the parallelograms about the diameter are equal to one
another. -/
theorem Prop43 {A B C D E F G H K : Point} (hABCD : Parallelogram A B C D) (hK : Between A K C)
    (hE : Between A E B) (hG : Between B G C) (hF : Between C F D) (hH : Between D H A)
    (hEH : Parallelogram A E K H) (hFG : Parallelogram K G C F) :
    quadArea E B G K = quadArea H K F D := by
  -- Let ABCD be a parallelogram, and AC its diameter; and about AC let EH, FG be
  -- parallelograms, and BK, KD the so-called complements;
  -- I say that the complement BK is equal to the complement KD.
  -- For, since ABCD is a parallelogram, and AC its diameter, the triangle ABC is equal to the
  -- triangle ACD. [I. 34]
  -- Again, since EH is a parallelogram, and AK is its diameter, the triangle AEK is equal to
  -- the triangle AHK.
  -- For the same reason the triangle KFC is also equal to KGC.
  -- Now, since the triangle AEK is equal to the triangle AHK, and KFC to KGC, the triangle AEK
  -- together with KGC is equal to the triangle AHK together with KFC. [C.N. 2]
  -- And the whole triangle ABC is also equal to the whole ADC; therefore the complement BK
  -- which remains is equal to the complement KD which remains. [C.N. 3]
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
