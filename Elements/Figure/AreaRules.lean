import Elements.Figure.Triangles
import Elements.Figure.RuleBase
import Elements.Figure.Incidence

/-!
# Book Zero: reversing and recognizing an area dissection

Area addition, rotation and cancellation prove reversal of a triangle's area.
Positivity then locates a cut from the areas it produces. These proofs precede the
usual area lemmas and use no proposition.
-/

namespace Elements

open Tacit

variable {A B C D E F : Point} {L M N : Line} {α β : Circle}

namespace RuleProofs.Area

local instance {k : Kind} : Std.Associative (α := Magnitude k) (· + ·) := ⟨add_assoc⟩
local instance {k : Kind} : Std.Commutative (α := Magnitude k) (· + ·) := ⟨add_comm⟩

/-- Adding two strict inequalities preserves strictness. -/
theorem add_self_lt_add_self {a b : Magnitude k} (h : a < b) : a + a < b + b :=
  lt_trans (add_lt_add_right a h) (by
    rw [add_comm b a, add_comm b b]
    exact add_lt_add_right b h)

/-- The area addition rule and rotation express a cut with the outer endpoints reversed. -/
theorem cut_reversed {A B C X : Point} {L : Line}
    (hA : OnLine A L) (hB : OnLine B L) (hC : OnLine C L)
    (hX : ¬ OnLine X L) (h : Between A B C) :
    △ X A B + △ X B C = △ X C A := by
  have e := area_add_of_between hA hC hB (ne_of_between_ends h)
    (ne_of_between h) (ne_of_between (between_symm h)) hX h
  rw [area_rotate A B X, ← area_rotate X C A] at e
  exact e

/-- Four cuts give the same residual areas after cancellation. -/
theorem cross_equal {P Q R S X : Point} {L : Line}
    (hP : OnLine P L) (hQ : OnLine Q L) (hR : OnLine R L) (hS : OnLine S L)
    (hX : ¬ OnLine X L) (hPQR : Between P Q R) (hQRS : Between Q R S) :
    △ X P Q + △ X S R = △ X Q P + △ X R S := by
  have hPQS := between_of_between_right hPQR hQRS
  have hPRS := between_symm (between_of_between_right
    (between_symm hQRS) (between_symm hPQR))
  have e₁ := cut_reversed hP hQ hS hX hPQS
  have e₂ := cut_reversed hS hR hQ hX (between_symm hQRS)
  have e₃ := cut_reversed hP hR hS hX hPRS
  have e₄ := cut_reversed hR hQ hP hX (between_symm hPQR)
  have e : (△ X P Q + △ X S R) + △ X R Q =
      (△ X Q P + △ X R S) + △ X R Q := by
    calc
      _ = △ X P Q + (△ X S R + △ X R Q) := by ac_rfl
      _ = △ X P Q + △ X Q S := by rw [e₂]
      _ = △ X S P := e₁
      _ = △ X P R + △ X R S := e₃.symm
      _ = (△ X R Q + △ X Q P) + △ X R S := by rw [e₄]
      _ = _ := by ac_rfl
  exact CommonNotion3 e rfl

/-- Equal triples have equal thirds, by strict comparison. -/
theorem eq_of_triples_eq {a b : Area} (h : a + a + a = b + b + b) : a = b := by
  have strict {x y : Area} (hxy : x < y) : x + x + x < y + y + y := by
    have h₂ := add_self_lt_add_self hxy
    exact lt_trans (add_lt_add_right x h₂) (by
      rw [add_comm (y + y) x, add_comm (y + y) y]
      exact add_lt_add_right (y + y) hxy)
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (Magnitude.ne_of_lt (strict hab) h)
  · exact hab
  · exact False.elim (Magnitude.ne_of_lt (strict hab) h.symm)

/-- The three cut identities force equality of the two orientations. -/
theorem reversal_algebra {a b c d e f u v : Area}
    (h₁ : a + v = b + u) (h₂ : e + v = f + u) (h₃ : c + v = d + u)
    (h₄ : b + d = e) (h₅ : a + c = f) : a = b := by
  have hsum : (a + c) + (v + v + v) = (a + c) + (u + u + u) := by
    calc
      _ = (a + v) + (c + v) + v := by ac_rfl
      _ = (b + u) + (d + u) + v := by rw [h₁, h₃]
      _ = (b + d + v) + (u + u) := by ac_rfl
      _ = (e + v) + (u + u) := by rw [h₄]
      _ = (f + u) + (u + u) := by rw [h₂]
      _ = (a + c) + (u + u + u) := by rw [← h₅]; ac_rfl
  have htriple : v + v + v = u + u + u := by
    apply CommonNotion3 (c := a + c) (d := a + c)
    · simpa only [add_comm (a + c)] using hsum
    · rfl
  have hvu := eq_of_triples_eq htriple
  rw [hvu] at h₁
  exact CommonNotion3 h₁ rfl

/-- Extend a side three times and compare the overlapping cuts. -/
theorem area_swap_triangle {X P Q : Point} (h : Triangle X P Q) :
    △ X P Q = △ X Q P := by
  obtain ⟨L, hP, hQ⟩ := Postulate1 P Q h.ne₂₃
  have hX := h.bca.off_line hP hQ
  obtain ⟨R, hR, hPQR, -⟩ := Postulate2 hP hQ h.ne₂₃ []
  obtain ⟨S, hS, hQRS, -⟩ := Postulate2 hQ hR
    (ne_of_between (between_symm hPQR)).symm []
  obtain ⟨T, hT, hRST, -⟩ := Postulate2 hR hS
    (ne_of_between (between_symm hQRS)).symm []
  have hPQS := between_of_between_right hPQR hQRS
  have hPRS := between_symm (between_of_between_right
    (between_symm hQRS) (between_symm hPQR))
  have hQST := between_symm (between_of_between_right
    (between_symm hRST) (between_symm hQRS))
  exact reversal_algebra
    (cross_equal hP hQ hS hT hX hPQS hQST)
    (cross_equal hP hR hS hT hX hPRS hRST)
    (cross_equal hQ hR hS hT hX hQRS hRST)
    (by
      have e := cut_reversed hR hQ hP hX (between_symm hPQR)
      simpa only [add_comm] using e)
    (cut_reversed hP hQ hR hX hPQR)

end RuleProofs.Area

/-- The triangle ABC is the triangle ACB. (Metric 8) Successive cuts prove reversal for a
triangle; collinear and repeated corners have zero area. -/
theorem Tacit.area_swap (A B C : Point) : △ A B C = △ A C B := by
  by_cases h : Triangle A B C
  · exact RuleProofs.Area.area_swap_triangle h
  · have hcol : Collinear A B C := Classical.not_not.mp h
    have zero {P Q R : Point} (hc : Collinear P Q R) : △ P Q R = 0 := by
      by_cases hPQ : P = Q
      · subst Q
        exact area_degenerate P R
      · obtain ⟨L, hP, hQ, hR⟩ := hc
        exact area_eq_zero_of_on_line hP hQ hPQ hR
    obtain ⟨L, hA, hB, hC⟩ := hcol
    exact (zero ⟨L, hA, hB, hC⟩).trans (zero ⟨L, hA, hC, hB⟩).symm

namespace RuleProofs.Area

/-- A noncollinear triangle has positive area. -/
theorem positive_area (h : Triangle A B C) : 0 < △ A B C := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B h.ne₁₂
  exact Magnitude.pos_of_ne_zero fun h0 =>
    h.off_line hA hB (on_line_of_area_eq_zero hA hB h.ne₁₂ h0)


end RuleProofs.Area

/-- Rotation read in the other direction names the same area. -/
private theorem RuleProofs.Area.area_bca (A B C : Point) : △ A B C = △ B C A :=
  (area_rotate B C A).symm

/-- If A, B and C are different points of a straight line, D is off it, and the triangles ACD
and DCB together make up the triangle ADB, then C lies between A and B. (Diagram-area 2,
converse) In either contrary collinear order, area addition would make each of two areas
greater than the other. -/
theorem Tacit.between_of_area_add (hA : OnLine A L) (hB : OnLine B L) (hC : OnLine C L)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hD : ¬ OnLine D L)
    (h : △ A C D + △ D C B = △ A D B) : Between A C B := by
  rcases between_cases hAB hBC hAC hA hB hC with hABC | hBAC | hACB
  · have hadd := area_add_of_between hA hC hB hAC hAB hBC.symm hD hABC
    have hp : 0 < △ D C B := RuleProofs.Area.positive_area (Triangle.of_line hC hB hBC.symm hD).cab
    have hlt := CommonNotion5 (a := △ A D B) hp
    have he : △ A D B + △ D C B = △ A C D := by
      rw [← area_swap A B D, area_swap D C B, hadd]
      exact area_swap A D C
    rw [he] at hlt
    have hlt' := CommonNotion5 (a := △ A C D) hp
    rw [h] at hlt'
    exact False.elim (lt_irrefl _ (lt_trans hlt hlt'))
  · have hadd := area_add_of_between hB hC hA hBC hAB.symm hAC.symm hD hBAC
    have hp : 0 < △ A C D := RuleProofs.Area.positive_area (Triangle.of_line hA hC hAC hD)
    have he : △ A D B + △ A C D = △ D C B := by
      rw [area_rotate A D B, area_rotate A C D, hadd, RuleProofs.Area.area_bca B D C]
    have hlt := CommonNotion5 (a := △ A D B) hp
    rw [he] at hlt
    have hlt' := CommonNotion5 (a := △ D C B) hp
    rw [add_comm, h] at hlt'
    exact False.elim (lt_irrefl _ (lt_trans hlt hlt'))
  · exact hACB

end Elements
