import Elements.Figure.Basics
import Elements.BookII.Rectangles

/-!
# Book III: squares on straight lines, from Books I and II

Book III borrows Book II's squares twice to compare straight lines, and passes from
equal squares to equal sides without a word: "therefore the square on FE which remains
is equal to the square on EG, therefore EF is equal to EG" (III.14); "the square on DE
is equal to the square on DB; therefore DE is equal to DB" (III.37). Book I proves it of
squares that are drawn (`Prop46.side_eq`, from Proclus' remark under I.46, as Heath
reports it); here it is said once of the squares on straight lines, with the fact that
the square on a straight line is something.

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
    /- The squares `ADEB` on `AB` and `CGHD` on `CD`, read from `B` and from `D`. -/
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

end Elements
