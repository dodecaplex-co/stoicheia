import Elements.Figure.Basics
import Elements.BookI.Prop03
import Elements.BookI.Prop04

/-!
# Book I, Proposition 6

Euclid's text, in Heath's translation: [`heath/I/06.md`](../../heath/I/06.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

This is the first proof in the *Elements* by *reductio ad absurdum*. Euclid
supposes that AB is the greater and lets the argument fall apart; the case in
which AC is the greater is the same argument with B and C exchanged, so
the Lean makes the argument once, for any triangle with equal angles at the
base, and uses it both ways round.
-/

namespace Elements.BookI

open Tacit

/-- What Euclid sees in the figure but never says: D, cut off on BA, is not on
the straight line BC, so DBC is a triangle (and I.4 may be applied to it). -/
theorem Prop6.figure {A B C D : Point} (hABC : Triangle A B C) (hBDA : Between B D A) :
    Triangle B D C := by
  rintro ⟨L, hB, hD, hC⟩
  /- A straight line through B and D goes on through A, and then A, B, C would
     lie on one straight line. -/
  exact hABC ⟨L, on_line_of_between hBDA hB hD, hB, hC⟩

/-- The step Heath points out: because D is between A and B, the
triangle DBC is less than the triangle ACB. The straight line CD cuts ACB
into DBC and ADC (System E, Diagram-area 2), ADC is something, since C is
not on AB (Diagram-area 1), and the whole is greater than the part (C.N. 5). -/
theorem Prop6.less {A B C D : Point} (hABC : Triangle A B C) (hBDA : Between B D A) :
    △ D B C < △ A C B := by
  obtain ⟨BA, hB, hA⟩ := Postulate1 B A hABC.ne₁₂.symm
  have hD : OnLine D BA := on_line_of_between_ends hBDA hB hA
  have hC : ¬ OnLine C BA := fun hC => hABC ⟨BA, hA, hB, hC⟩
  have hDA : D ≠ A := (ne_of_between (between_symm hBDA)).symm
  /- The two parts make up the whole. -/
  have hwhole : △ B D C + △ C D A = △ B C A :=
    area_add_of_between hB hA hD hABC.ne₁₂.symm (ne_of_between hBDA) hDA.symm hC hBDA
  /- The part ADC is something: a triangle with no area would have C on BA. -/
  have hpart : △ C D A ≠ 0 := by
    intro h0
    rw [← area_rotate D A C] at h0
    exact hC (on_line_of_area_eq_zero hD hA hDA h0)
  have := CommonNotion5 (a := △ B D C) (Magnitude.pos_of_ne_zero hpart)
  rw [hwhole, area_rotate B C A, area_swap A B C, ← area_rotate D C B, ← area_swap D B C]
    at this
  exact this

/-- If in a triangle two angles be equal to one another, the sides which subtend the equal angles
will also be equal to one another. -/
theorem Prop6 {A B C : Point} (hABC : Triangle A B C) (h : ∠ A B C = ∠ A C B) :
    ‖A B‖ = ‖A C‖ := by
  -- Let ABC be a triangle having the angle ABC equal to the angle ACB;
  -- I say that the side AB is also equal to the side AC.
  -- For, if AB is unequal to AC, one of them is greater.
  /- That of two unequal lengths one is the greater is a tacit rule of
     magnitude (System E §3.5), `lt_trichotomy`. -/
  have one_greater : ‖A B‖ ≠ ‖A C‖ → ‖A C‖ < ‖A B‖ ∨ ‖A B‖ < ‖A C‖ := by
    intro hne
    rcases lt_trichotomy ‖A B‖ ‖A C‖ with hlt | heq | hgt
    · exact Or.inr hlt
    · exact absurd heq hne
    · exact Or.inl hgt
  /- Euclid takes AB to be the greater. The other case is his argument again
     with B and C exchanged, so we give the argument for every triangle whose
     angles at B and C are equal, and use it twice below. -/
  have greater : ∀ {B C : Point}, Triangle A B C → ∠ A B C = ∠ A C B →
      ‖A C‖ < ‖A B‖ → False := by
    intro B C hABC h hAC_AB
    -- Let AB be greater; and from AB the greater let DB be cut off equal to AC the less;
    /- Heath gives no reference here, but cutting off is I.3, from the end B. -/
    have hAC_BA : ‖A C‖ < ‖B A‖ := by rw [len_symm B A]; exact hAC_AB
    obtain ⟨D, hBDA, hBD⟩ := Prop3 (A := B) (B := A) hABC.ne₁₃ hAC_BA
    -- let DC be joined.
    /- Our proof uses only the points D and C; the straight line DC is drawn
       for the eye. -/
    -- Then, since DB is equal to AC,
    have hDB : ‖D B‖ = ‖A C‖ := (len_symm D B).trans hBD
    -- and BC is common,
    have hBC : ‖B C‖ = ‖C B‖ := len_symm B C
    -- the two sides DB, BC are equal to the two sides AC, CB respectively;
    have hsides : ‖B D‖ = ‖C A‖ ∧ ‖B C‖ = ‖C B‖ :=
      ⟨(len_symm B D).trans (hDB.trans (len_symm A C)), hBC⟩
    -- and the angle DBC is equal to the angle ACB;
    /- The angle DBC is the angle ABC itself, since D lies on the ray from B
       through A (`angle_onRay_left` in Book Zero, from System E's Diagram-angle
       4), and ABC is equal to ACB by hypothesis. -/
    have hDBC : ∠ D B C = ∠ A C B :=
      (angle_onRay_left (OnRay.of_between hBDA) hABC.ne₂₃.symm).trans h
    -- therefore the base DC is equal to the base AB,
    /- This is I.4, applied to the triangles DBC and ACB; that DBC is a
       triangle at all is `Prop6.figure`. -/
    obtain ⟨hDC_AB, hBDC_CAB, -, -⟩ :=
      Prop4 (Prop6.figure hABC hBDA) hABC.cab hsides.1 hsides.2 hDBC
    -- and the triangle DBC will be equal to the triangle ACB,
    have hequal : △ D B C = △ A C B := by
      rw [area_swap D B C, area_rotate D C B, hBDC_CAB, ← area_rotate A B C, area_swap A B C]
    -- the less to the greater:
    /- Heath: "Euclid assumes that, because D is between A and B, the
       triangle DBC is less than the triangle ABC" (vol. 1, p. 256). We prove it,
       with areas: the whole triangle is greater than its part (`Prop6.less`). -/
    have hless : △ D B C < △ A C B := Prop6.less hABC hBDA
    -- which is absurd.
    rw [hequal] at hless
    exact lt_irrefl _ hless
  -- Therefore AB is not unequal to AC;
  have hnot : ¬ ‖A B‖ ≠ ‖A C‖ := fun hne =>
    (one_greater hne).elim (greater hABC h) (greater hABC.acb h.symm)
  -- it is therefore equal to it.
  /- Reductio ad absurdum: a length not unequal to another is equal to it. -/
  exact Classical.byContradiction hnot
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookI
