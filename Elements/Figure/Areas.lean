import Elements.Figure.Triangles
import Elements.Figure.Rays

/-!
# Book Zero: areas

From I.35 on, Euclid adds and takes away areas as freely as lengths and angles:
"let DGE be subtracted from each", "let the triangle GBC be added to each". He
never doubts that the triangle ABC is the triangle BCA, whichever corner it is
named from; that a straight line from a corner cuts a triangle into two which make
up the whole; that a triangle is something, and greater than a part of it; that
on a ray from a corner only one point makes a triangle equal to a given one on the
same base; or that the halves of equal things are equal. Nor does he say which
diameter measures a four-sided figure: when its diameters cross, either will do.
These are those facts, proved from System E's rules for areas (Avigad, Dean and
Mumma, §3.5 and §3.6) and the laws of magnitudes.

Lean's `ac_rfl` can put any sum of magnitudes in order once it knows that adding
is associative and commutative, and the two instances below tell it so. A proof
that has cut a figure into triangles can then close with `ac_rfl`, instead of a
long run of `add_comm` and `add_assoc`.
-/

namespace Elements

open Tacit

variable {A B C D X : Point} {k : Kind}

/-! ## Adding magnitudes in any order -/

/-- Adding magnitudes is associative (System E §3.5), told to `ac_rfl`. -/
instance Magnitude.instAssociative : Std.Associative (α := Magnitude k) (· + ·) :=
  ⟨add_assoc⟩

/-- Adding magnitudes is commutative (System E §3.5), told to `ac_rfl`. -/
instance Magnitude.instCommutative : Std.Commutative (α := Magnitude k) (· + ·) :=
  ⟨add_comm⟩

/-- The doubles of unequal things are unequal, the less to the less: if `a` is less
than `b`, then `a` and `a` together are less than `b` and `b` together. (System E
§3.5) -/
theorem Magnitude.add_self_lt_add_self {a b : Magnitude k} (h : a < b) : a + a < b + b :=
  lt_trans (add_lt_add_right a h) (by
    rw [add_comm b a, add_comm b b]
    exact add_lt_add_right b h)

/-- The halves of equal things are equal: if `a` and `a` together are equal to `b`
and `b` together, then `a` is equal to `b`. Were `a` less than `b`, then `a` and `a`
would be less than `b` and `b`; and the same the other way round. Heiberg brackets
these words in I.37 and I.38 as added later, but the step is needed all the same. -/
theorem Magnitude.eq_of_add_self_eq {a b : Magnitude k} (h : a + a = b + b) : a = b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd h (Magnitude.ne_of_lt (Magnitude.add_self_lt_add_self h'))
  · exact h'
  · exact absurd h.symm (Magnitude.ne_of_lt (Magnitude.add_self_lt_add_self h'))

/-! ## A triangle named from any corner -/

/-- The triangle ABC is the triangle BCA. (System E, Metric 8) -/
theorem area_bca (A B C : Point) : △ A B C = △ B C A := (area_rotate B C A).symm

/-- The triangle ABC is the triangle CAB. (System E, Metric 8) -/
theorem area_cab (A B C : Point) : △ A B C = △ C A B := area_rotate A B C

/-- The triangle ABC is the triangle ACB. (System E, Metric 8) -/
theorem area_acb (A B C : Point) : △ A B C = △ A C B := area_swap A B C

/-- The triangle ABC is the triangle BAC. (System E, Metric 8) -/
theorem area_bac (A B C : Point) : △ A B C = △ B A C :=
  (area_swap A B C).trans (area_rotate A C B)

/-- The triangle ABC is the triangle CBA. (System E, Metric 8) -/
theorem area_cba (A B C : Point) : △ A B C = △ C B A :=
  (area_rotate A B C).trans (area_swap C A B)

/-! ## Triangles that are nothing, and triangles that are something -/

/-- Three points on one straight line make no triangle: its area is nothing.
(System E, Metric 6 and Diagram-area 1) -/
theorem area_eq_zero_of_collinear (h : Collinear A B C) : △ A B C = 0 := by
  by_cases hAB : A = B
  · subst hAB
    exact area_degenerate A C
  · obtain ⟨L, hA, hB, hC⟩ := h
    exact area_eq_zero_of_on_line hA hB hAB hC

/-- A triangle is something: its area is more than nothing. Were it nothing, its
corners would lie on one straight line (System E, Diagram-area 1). -/
theorem Triangle.area_pos (h : Triangle A B C) : 0 < △ A B C := by
  obtain ⟨L, hA, hB⟩ := Postulate1 A B h.ne₁₂
  exact Magnitude.pos_of_ne_zero fun h0 =>
    h.off_line hA hB (on_line_of_area_eq_zero hA hB h.ne₁₂ h0)

/-! ## Cutting a triangle from a corner -/

/-- A straight line from a corner cuts a triangle into two which make up the
whole: if D lies between B and C, the triangles ABD and ADC together are
the triangle ABC. (System E, Diagram-area 2) When A is on the straight line
BC, all three are nothing, and it still holds. -/
theorem area_cut (h : Between B D C) : △ A B D + △ A D C = △ A B C := by
  obtain ⟨L, hB, hC⟩ := Postulate1 B C (ne_of_between_ends h)
  have hD : OnLine D L := on_line_of_between_ends h hB hC
  by_cases hA : OnLine A L
  · rw [area_eq_zero_of_collinear ⟨L, hA, hB, hD⟩, area_eq_zero_of_collinear ⟨L, hA, hD, hC⟩,
      area_eq_zero_of_collinear ⟨L, hA, hB, hC⟩, add_zero]
  · have := area_add_of_between hB hC hD (ne_of_between_ends h) (ne_of_between h)
      (ne_of_between (between_symm h)) hA h
    rw [area_bca A B D, area_bac A B C]
    exact this

/-- The part is less than the whole, for triangles: if D lies between B and C,
the triangle ABD is less than the triangle ABC, for the triangle ADC is
something besides. (System E, Diagram-area 2, and C.N. 5) -/
theorem area_lt_of_cut (hABC : Triangle A B C) (h : Between B D C) : △ A B D < △ A B C := by
  obtain ⟨L, hB, hC⟩ := Postulate1 B C hABC.ne₂₃
  have hADC : Triangle A D C :=
    (Triangle.of_line (on_line_of_between_ends h hB hC) hC (ne_of_between (between_symm h)).symm
      (hABC.bca.off_line hB hC)).cab
  rw [← area_cut (A := A) h]
  exact CommonNotion5 hADC.area_pos

/-- "The greater to the less: which is impossible" (I.39, I.40). On the ray from B
through D, only D itself makes with the base BC a triangle equal to DBC. A
point E nearer to B makes EBC a part of DBC, and a point beyond D makes
DBC a part of EBC; either way the part would be equal to the whole
(`area_lt_of_cut`, C.N. 5). If E is as far from B as D is, it is D
(`OnRay.eq_of_len_eq`). -/
theorem OnRay.eq_of_area_eq {E : Point} (hDBC : Triangle D B C) (hE : OnRay E B D)
    (h : △ E B C = △ D B C) : E = D := by
  obtain ⟨hBD, hEB, ⟨L, hB, hD, hE_L⟩, -⟩ := id hE
  have hEBC : Triangle E B C := fun ⟨M, hE_M, hB_M, hC_M⟩ =>
    hDBC ⟨M, (line_unique hEB hE_L hB hE_M hB_M) ▸ hD, hB_M, hC_M⟩
  rcases lt_trichotomy ‖B E‖ ‖B D‖ with hlt | heq | hgt
  · have hless := area_lt_of_cut hDBC.cba (hE.between_of_len_lt (OnRay.self hBD) hlt)
    rw [← area_cba E B C, ← area_cba D B C, h] at hless
    exact absurd rfl (Magnitude.ne_of_lt hless)
  · exact hE.eq_of_len_eq heq
  · have hless := area_lt_of_cut hEBC.cba ((OnRay.self hBD).between_of_len_lt hE hgt)
    rw [← area_cba E B C, ← area_cba D B C, h] at hless
    exact absurd rfl (Magnitude.ne_of_lt hless)

/-! ## Four-sided figures

`quadArea A B C D` measures the figure ABCD by its diameter AC: it is the
triangles ABC and ACD together. Read from C, or the other way round, the
diameter is the same. Read from B, the diameter is BD; when the two diameters
cross, the two measures agree. -/

/-- The figure ABCD read the other way round, as ADCB, has the same diameter
AC, and the same area. -/
theorem quadArea_reverse (A B C D : Point) : quadArea A D C B = quadArea A B C D := by
  unfold quadArea
  rw [area_acb A D C, area_acb A C B, add_comm]

/-- The figure ABCD read from C, as CDAB, has the same diameter CA, and the
same area. -/
theorem quadArea_rotate₂ (A B C D : Point) : quadArea C D A B = quadArea A B C D := by
  unfold quadArea
  rw [area_bca A C D, area_cab A B C, add_comm]

/-- A four-sided figure whose diameters cross has the same area whichever diameter
cuts it: if X lies between A and C and also between B and D, the figure
ABCD measured by AC is the figure BCDA measured by BD. Each diameter cuts
the figure into two triangles, and the other diameter cuts each of those into two
more; the four small triangles about X are the same either way (System E,
Diagram-area 2). -/
theorem quadArea_rotate_of_cross (hAXC : Between A X C) (hBXD : Between B X D) :
    quadArea B C D A = quadArea A B C D := by
  unfold quadArea
  have h₁ : △ A B C = △ B A X + △ B X C := (area_bac A B C).trans (area_cut hAXC).symm
  have h₂ : △ A C D = △ D A X + △ D X C := (area_cab A C D).trans (area_cut hAXC).symm
  have h₃ : △ B C D = △ C B X + △ C X D := (area_bac B C D).trans (area_cut hBXD).symm
  have h₄ : △ B D A = △ A B X + △ A X D := (area_cab B D A).trans (area_cut hBXD).symm
  rw [h₁, h₂, h₃, h₄, ← area_cab B X C, area_bac A B X, area_cab A X D, area_cba C X D]
  ac_rfl

end Elements
