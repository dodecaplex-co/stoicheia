import Elements.Figure.Basics
import Elements.BookI.Prop15
import Elements.BookI.Prop29
import Elements.BookI.Prop31
import Elements.BookI.Prop42
import Elements.BookI.Prop43

/-!
# Book I, Proposition 44

Euclid's text, in Heath's translation: [`heath/I/44.md`](../../heath/I/44.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- To a given straight line to apply, in a given rectilineal angle, a parallelogram equal to a
given triangle. -/
theorem Prop44 {A B C₁ C₂ C₃ D₁ D D₂ P : Point} (hAB : A ≠ B) (hC : Triangle C₁ C₂ C₃)
    (hD : Triangle D₁ D D₂) (hP : ¬ Collinear A B P) :
    ∃ L M : Point, SameSideOf M P A B ∧ Parallelogram A B M L ∧
      ∠ A B M = ∠ D₁ D D₂ ∧ quadArea A B M L = △ C₁ C₂ C₃ := by
  -- Let AB be the given straight line, C the given triangle and D the given rectilineal angle;
  -- thus it is required to apply to the given straight line AB, in an angle equal to the angle
  -- D, a parallelogram equal to the given triangle C.
  -- Let the parallelogram BEFG be constructed equal to the triangle C, in the angle EBG which
  -- is equal to D [I. 42]; let it be placed so that BE is in a straight line with AB; let FG
  -- be drawn through to H, and let AH be drawn through A parallel to either BG or EF. [I. 31]
  -- Let HB be joined.
  -- Then, since the straight line HF falls upon the parallels AH, EF, the angles AHF, HFE are
  -- equal to two right angles. [I. 29]
  -- Therefore the angles BHG, GFE are less than two right angles; and straight lines produced
  -- indefinitely from angles less than two right angles meet; [Post. 5] therefore HB, FE, when
  -- produced, will meet.
  -- Let them be produced and meet at K; through the point K let KL be drawn parallel to either
  -- EA or FH, [I. 31] and let HA, GB be produced to the points L, M.
  -- Then HLKF is a parallelogram, HK is its diameter, and AG, ME are parallelograms, and LB,
  -- BF the so-called complements, about HK; therefore LB is equal to BF. [I. 43]
  -- But BF is equal to the triangle C; therefore LB is also equal to C. [C.N. 1]
  -- And, since the angle GBE is equal to the angle ABM, [I. 15] while the angle GBE is equal
  -- to D, the angle ABM is also equal to the angle D.
  -- Therefore the parallelogram LB equal to the given triangle C has been applied to the given
  -- straight line AB, in the angle ABM which is equal to D.
  -- Q. E. F.
  sorry

end Elements.BookI
