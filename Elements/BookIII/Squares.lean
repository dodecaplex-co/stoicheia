import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop17
import Elements.BookI.Prop19

/-!
# Book III: squares on straight lines, and the perpendicular from the centre

Book III borrows Book II's squares twice to compare straight lines, and passes from
equal squares to equal sides without a word: "therefore the square on FE which remains
is equal to the square on EG, therefore EF is equal to EG" (III.14); "the square on DE
is equal to the square on DB; therefore DE is equal to DB" (III.37). Book I proves it of
squares that are drawn (`Prop46.side_eq`); here it is said once of the squares on
straight lines, with the fact that the square on a straight line is something.

The propositions that compare those squares (III.14, III.35, III.36) draw a
perpendicular from the centre to a straight line in the circle, and read off the figure
that it falls within the straight line, between its ends, before III.3 bisects it there.
That is said once too (`foot_between`).

Each docstring ends with the propositions the step cites; the certificate walks through
it and records them.
-/

namespace Elements

open Tacit BookI

/-- The square on a straight line is something. Described on `AB` [I. 46], it is a
parallelogram (`Square.described`), and its diameter cuts it into two triangles, each of
which is something. [I. 4, I. 28, I. 34, I. 46] -/
theorem sq_pos {A B : Point} (hAB : A ≠ B) : 0 < sq A B := by
  obtain ⟨P, hP, -⟩ := exists_off_line hAB []
  obtain ⟨D, E, hsq, hD, hE⟩ := Prop46 hAB hP
  obtain ⟨hp, heq⟩ := Square.described hsq hD hE
  rw [← heq]
  have h₁ : 0 < △ A D E := hp.triangle.area_pos
  have h₂ : 0 < △ A E B := by
    rw [← area_rotate E B A]
    exact hp.rotate.rotate.triangle.area_pos
  exact lt_trans h₁ (CommonNotion5 h₂)

/-- **Equal squares are on equal straight lines.** If the square on `AB` is equal to the
square on `CD`, then `AB` is equal to `CD`. Each square is described [I. 46] and is the
square on its side (`Square.described`); then I.46's corollary for drawn squares,
`Prop46.side_eq`, compares them. If one of the straight lines is nothing, so is its
square, and so the other (`sq_pos`). [I. 3, I. 4, I. 28, I. 34, I. 46] -/
theorem BookI.Prop46.sq {A B C D : Point} (h : sq A B = sq C D) : ‖A B‖ = ‖C D‖ := by
  by_cases hAB : A = B
  · subst hAB
    by_cases hCD : C = D
    · subst hCD
      rw [len_self, len_self]
    · rw [sq_self] at h
      exact absurd h.symm (Magnitude.ne_of_lt (sq_pos hCD)).symm
  · by_cases hCD : C = D
    · subst hCD
      rw [sq_self] at h
      exact absurd h (Magnitude.ne_of_lt (sq_pos hAB)).symm
    /- The squares on `AB` and on `CD` [I. 46], each read from its second corner. -/
    obtain ⟨P, hP, -⟩ := exists_off_line hAB []
    obtain ⟨D', E', hsq, hD', hE'⟩ := Prop46 hAB hP
    obtain ⟨hp, heq⟩ := Square.described hsq hD' hE'
    obtain ⟨Q, hQ, -⟩ := exists_off_line hCD []
    obtain ⟨G, H, hsq', hG, hH⟩ := Prop46 hCD hQ
    obtain ⟨hp', heq'⟩ := Square.described hsq' hG hH
    have e₁ : quadArea B A D' E' = Elements.sq A B := by
      rw [← heq, quadArea_rotate₂ D' E' B A, hp.quadArea_rotate]
    have e₂ : quadArea D C G H = Elements.sq C D := by
      rw [← heq', quadArea_rotate₂ G H D C, hp'.quadArea_rotate]
    have := Prop46.side_eq hsq.rotate.rotate.rotate (hD'.trans hE'.symm).swap
      hsq'.rotate.rotate.rotate (hG.trans hH.symm).swap (by rw [e₁, e₂, h])
    rw [len_symm A B, len_symm C D]
    exact this

/-- **The perpendicular from the centre falls within.** The perpendicular drawn from the
centre `E` to a straight line `AB` in the circle, not through the centre, falls between
`A` and `B`. Its foot `F` is nearer the centre than any other point `P` of the straight
line: in the triangle `EFP` the angle at `F` is right, so the angle at `P` is less than a
right angle [I. 17], and `EP`, opposite the greater angle, is greater than `EF` [I. 19].
So `F` is nearer than `A` or than `B`, which are on the circle; it is within the circle,
and so between them (System E, Circle 1). Euclid reads it off the figure in III.14,
III.35 and III.36, before III.3 bisects the straight line there. [I. 17, I. 19] -/
theorem foot_between {A B E F : Point} {α : Circle} (hE : Centre E α) (hA : OnCircle A α)
    (hB : OnCircle B α) (hE_AB : ¬ Collinear A B E) (hF : Collinear A B F)
    (hEF : ∀ P : Point, Collinear A B P → P ≠ F → ∠ E F P = ∟) : Between A F B := by
  have hAB : A ≠ B := Triangle.ne₁₂ hE_AB
  obtain ⟨M, hA_M, hB_M, hF_M⟩ := hF
  have hE_M : ¬ OnLine E M := Triangle.off_line hE_AB hA_M hB_M
  /- Any other point `P` of the straight line is farther from `E` than `F` is. -/
  have nearer : ∀ P : Point, OnLine P M → P ≠ F → ‖E F‖ < ‖E P‖ := by
    intro P hP_M hPF
    have hFPE : Triangle F P E := Triangle.of_line hF_M hP_M hPF.symm hE_M
    have hEFP : Triangle E F P := hFPE.cab
    have hright : ∠ E F P = ∟ := hEF P ⟨M, hA_M, hB_M, hP_M⟩ hPF
    /- The angles `EFP`, `FPE` are less than two right angles [I. 17]. -/
    have h17 := (BookI.Prop17 hEFP).1
    rw [hright] at h17
    have hP : ∠ F P E < ∠ E F P := hright ▸ Magnitude.lt_of_add_lt_add_left h17
    /- The greater angle is subtended by the greater side [I. 19]. -/
    exact BookI.Prop19 hEFP hP
  /- `F` is within the circle: nearer the centre than `A`, or than `B`. -/
  have hF_in : InsideCircle F α := by
    by_cases hAF : A = F
    · have hBF : B ≠ F := fun e => hAB (hAF.trans e.symm)
      exact inside_of_len_lt hE hB (nearer B hB_M hBF)
    · exact inside_of_len_lt hE hA (nearer A hA_M hAF)
  exact between_of_inside_chord hF_M hA_M hB_M hF_in hA hB hAB

end Elements
