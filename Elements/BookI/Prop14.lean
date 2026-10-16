import Elements.Figure.Basics
import Elements.BookI.Prop13

/-!
# Book I, Proposition 14

Euclid's text, in Heath's translation: [`heath/I/14.md`](../../heath/I/14.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

I.14 is the converse of I.13, and Euclid proves it by *reductio ad absurdum*.
He supposes that `BD` is not in a straight line with `CB`, produces `CB` to
`E`, and finds the angle `ABE` equal to the angle `ABD`, "the less to the
greater". In Lean, once `E` is there, Euclid's supposition is that `D` is off
the ray from `B` through `E`, and the argument runs as a sub-proof under it,
as in I.6.
-/

namespace Elements.BookI

open Tacit

/-- If with any straight line, and at a point on it, two straight lines not lying on the same side
make the adjacent angles equal to two right angles, the two straight lines will be in a straight
line with one another. -/
theorem Prop14 {A B C D : Point} (hCD : OppositeSidesOf C D A B) (h : ∠ A B C + ∠ A B D = ∟ + ∟) :
    Between C B D := by
  -- For with any straight line AB, and at the point B on it, let the two straight lines BC, BD
  -- not lying on the same side make the adjacent angles ABC, ABD equal to two right angles;
  /- "Not lying on the same side": C and D are on opposite sides of AB. So C is
     off AB, and ABC is a triangle. -/
  have hABC : Triangle A B C := hCD.triangle
  have hA_B : A ≠ B := hABC.ne₁₂
  have hC_B : C ≠ B := hABC.ne₂₃.symm
  -- I say that BD is in a straight line with CB.
  /- In Lean: B lies between C and D. -/
  -- For, if BD is not in a straight line with BC, let BE be in a straight line with CB.
  /- CB is produced beyond B to E [Post. 1, Post. 2], which is `produce` in Book
     Zero. Euclid's supposition then says that BE is another straight line than
     BD: that D is not on the ray from B through E. We follow his argument
     under that supposition, as far as the impossible. -/
  obtain ⟨E, hCBE⟩ := produce hC_B
  have other : ¬ OnRay D B E → False := by
    intro hD_BE
    -- Then, since the straight line AB stands on the straight line CBE,
    /- Stands on it, and is not part of it: A is off the straight line CE, for
       that line passes through B, and A, B, C are not on one straight line. -/
    have hA_CE : ¬ Collinear C E A := by
      rintro ⟨L, hC, hE, hA⟩
      exact hABC ⟨L, hA, on_line_of_between_ends hCBE hC hE, hC⟩
    -- the angles ABC, ABE are equal to two right angles. [I. 13]
    have hCBA_ABE : ∠ C B A + ∠ A B E = ∟ + ∟ := Prop13 hCBE hA_CE
    -- But the angles ABC, ABD are also equal to two right angles;
    have hCBA_ABD : ∠ C B A + ∠ A B D = ∟ + ∟ := by
      rw [← angle_symm hA_B hC_B]
      exact h
    -- therefore the angles CBA, ABE are equal to the angles CBA, ABD. [Post. 4 and C.N. 1]
    /- Postulate 4 has done its work before we get here: every right angle is
       written with the one name `∟`, and I.13 hands its two back as `∟ + ∟`.
       So the step itself is C.N. 1 alone. -/
    have hsum : ∠ C B A + ∠ A B E = ∠ C B A + ∠ A B D := CommonNotion1 hCBA_ABE hCBA_ABD
    -- Let the angle CBA be subtracted from each;
    -- therefore the remaining angle ABE is equal to the remaining angle ABD, [C.N. 3]
    have hABE_ABD : ∠ A B E = ∠ A B D :=
      CommonNotion3 (c := ∠ C B A) (d := ∠ C B A) (by rw [add_comm, hsum, add_comm]) rfl
    -- the less to the greater: which is impossible.
    /- In Euclid's figure BE falls within the angle ABD, so that ABE is a part
       of ABD; Lean must allow too for BD falling within ABE. Both figures are
       settled by `onRay_of_angle_eq` in Book Zero: on one side of a straight
       line, only one ray from a point of it makes a given angle with it, for
       otherwise one of two equal angles would be a part of the other, the less
       equal to the greater. E and D are on the same side of AB, both being on
       the other side from C (`OppositeSidesOf.of_between`,
       `OppositeSidesOf.sameSideOf`); so D would lie on the ray from B through E,
       against the supposition. -/
    have hDE : SameSideOf D E A B := hCD.sameSideOf (OppositeSidesOf.of_between hABC hCBE)
    exact hD_BE (onRay_of_angle_eq hDE.swap hABE_ABD.symm)
  -- Therefore BE is not in a straight line with CB.
  /- That is, BE is not another straight line than BD: the supposition has
     failed, so D lies on the ray from B through E. -/
  have hD_BE : OnRay D B E := Classical.byContradiction other
  -- Similarly we can prove that neither is any other straight line except BD.
  /- Lean needs no "similarly": E was any point on CB produced, and the
     argument never asked which. -/
  -- Therefore CB is in a straight line with BD.
  /- So D lies beyond B from C: a point of the ray from B through E does
     (`OnRay.between`, in Book Zero). -/
  exact hD_BE.between hCBE
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
