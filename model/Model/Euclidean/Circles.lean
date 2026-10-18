module

public import Model.Euclidean
public import Model.Hand

/-!
# Where two circles cut one another, in the plane

The first laws proved in the model are the two that say when two circles cut one another.
Intersection 5 (`circles_meet`) is the step Euclid takes for granted in I.1: each circle
passes through a point inside the other, so they cross. Intersection 4
(`circles_meet_of_on_inside_outside`) is its companion, in LeanEuclid's corrected form.

Both come down to one fact about the plane. Put the centres at distance `d` apart, with
radii `r` and `s`. Two different circles cut one another in two points exactly when
`|r - s| < d < r + s`: the strict inequalities rule out circles that only touch, one
inside the other, and concentric circles (`d = 0`). (A circle also meets itself in two
points, with `d = 0`; neither law's hypotheses allow that case, since each asks for a
point on one circle and inside the other.) In each law the hypotheses give those
inequalities through the triangle inequality, and the crossing points are found by
coordinates: at the signed distance `a = (d² + r² - s²) / (2d)` from the first centre
along the line of centres, negative when the foot falls behind the first centre, and off
that line by `±h`, with `h² = r² - a²`. The strict inequalities are what make `h`
positive, and so give two points, not one.
-/

@[expose] public section

namespace Model.Euclidean

open scoped RealInnerProductSpace

/-! ## A quarter turn

In the plane every vector has a perpendicular of the same length: turn it a quarter turn. -/

/-- The vector `u` turned a quarter turn: `(-u₁, u₀)`. -/
noncomputable def quarterTurn (u : Plane) : Plane := !₂[-u 1, u 0]

/-- A vector and its quarter turn are perpendicular. -/
theorem inner_quarterTurn (u : Plane) : ⟪u, quarterTurn u⟫ = 0 := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- A quarter turn keeps a vector's length. -/
theorem norm_quarterTurn (u : Plane) : ‖quarterTurn u‖ = ‖u‖ := by
  simp only [quarterTurn, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp
  rw [add_comm]

/-! ## Two circles cut one another when `|r - s| < d < r + s` -/

/-- Two circles with centres `c₁`, `c₂` and radii `r`, `s` cut one another in two points
when the distance between the centres lies strictly between `|r - s|` and `r + s`. -/
theorem exists_two_common_points {c₁ c₂ : Plane} {r s : ℝ}
    (h₁ : |r - s| < dist c₁ c₂) (h₂ : dist c₁ c₂ < r + s) :
    ∃ P Q : Plane, P ≠ Q ∧ dist P c₁ = r ∧ dist P c₂ = s ∧ dist Q c₁ = r ∧ dist Q c₂ = s := by
  set d := dist c₁ c₂ with hd_def
  have hrs : r - s < d := lt_of_le_of_lt (le_abs_self _) h₁
  have hsr : s - r < d := by have := neg_abs_le (r - s); linarith
  have hd : 0 < d := lt_of_le_of_lt (abs_nonneg _) h₁
  have hr : 0 < r := by linarith
  have hs : 0 < s := by linarith
  -- The vector from the first centre to the second, and its quarter turn.
  set u : Plane := c₂ - c₁ with hu_def
  set w : Plane := quarterTurn u with hw_def
  have hu : ‖u‖ = d := by rw [hd_def, dist_comm, dist_eq_norm]
  have hw : ‖w‖ = d := by rw [hw_def, norm_quarterTurn, hu]
  have huw : ⟪u, w⟫ = 0 := inner_quarterTurn u
  -- Along the line of centres, a fraction `t` of the way; off it, `k` times `w`.
  set t : ℝ := (d ^ 2 + r ^ 2 - s ^ 2) / (2 * d ^ 2) with ht_def
  have hk2pos : 0 < r ^ 2 / d ^ 2 - t ^ 2 := by
    have key : r ^ 2 / d ^ 2 - t ^ 2 =
        ((s + r - d) * (s - r + d) * (d + r - s) * (d + r + s)) / (4 * d ^ 4) := by
      rw [ht_def]
      field_simp
      ring
    rw [key]
    apply div_pos _ (by positivity)
    apply mul_pos (mul_pos (mul_pos _ _) _) _ <;> linarith
  set k : ℝ := Real.sqrt (r ^ 2 / d ^ 2 - t ^ 2)
  have hk : 0 < k := Real.sqrt_pos.2 hk2pos
  have hkk : k ^ 2 = r ^ 2 / d ^ 2 - t ^ 2 := Real.sq_sqrt hk2pos.le
  -- The squared length of `a • u + b • w`.
  have hnorm : ∀ a b : ℝ, ‖a • u + b • w‖ ^ 2 = (a ^ 2 + b ^ 2) * d ^ 2 := by
    intro a b
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, huw, hu,
      hw]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, RCLike.conj_to_real]
    ring
  have hfirst : (t ^ 2 + k ^ 2) * d ^ 2 = r ^ 2 := by
    rw [hkk]; field_simp; ring
  have hsecond : ((t - 1) ^ 2 + k ^ 2) * d ^ 2 = s ^ 2 := by
    rw [hkk, ht_def]; field_simp; ring
  have hdist : ∀ (P : Plane) (c : Plane) (x : ℝ) (a b : ℝ), 0 ≤ x → P - c = a • u + b • w →
      (a ^ 2 + b ^ 2) * d ^ 2 = x ^ 2 → dist P c = x := by
    intro P c x a b hx hP hab
    rw [dist_eq_norm, hP]
    exact (pow_left_inj₀ (norm_nonneg _) hx two_ne_zero).1 (by rw [hnorm, hab])
  refine ⟨c₁ + t • u + k • w, c₁ + t • u - k • w, ?_, ?_, ?_, ?_, ?_⟩
  · -- The two points differ by `2k • w`, which is not zero.
    intro hPQ
    have h2 : (2 * k) • w = 0 := by
      have : (c₁ + t • u + k • w) - (c₁ + t • u - k • w) = (2 * k) • w := by
        rw [two_mul, add_smul]; abel
      rw [← this, hPQ, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · linarith
    · have : ‖w‖ = 0 := by rw [h, norm_zero]
      linarith
  · exact hdist _ _ _ t k hr.le (by abel) hfirst
  · exact hdist _ _ _ (t - 1) k hs.le (by rw [hu_def, sub_smul, one_smul]; abel) hsecond
  · exact hdist _ _ _ t (-k) hr.le (by rw [neg_smul]; abel) (by rw [neg_sq]; exact hfirst)
  · exact hdist _ _ _ (t - 1) (-k) hs.le (by rw [hu_def, sub_smul, one_smul, neg_smul]; abel)
      (by rw [neg_sq]; exact hsecond)

/-! ## The laws -/

/-- **Intersection 5 holds in the plane.** If the circle α passes through A, inside β, and β
passes through B, inside α, the two circles cut one another in two points. -/
theorem circles_meet : Hand.circles_meet plane := by
  intro A B α β hAα hBα hAβ hBβ
  rw [onCircle_iff] at hAα hBβ
  rw [insideCircle_iff] at hBα hAβ
  obtain ⟨⟨c₁, r⟩, hr⟩ := α
  obtain ⟨⟨c₂, s⟩, hs⟩ := β
  dsimp only at hAα hBα hAβ hBβ
  have hlt : dist c₁ c₂ < r + s := by
    have := dist_triangle c₁ A c₂
    rw [dist_comm c₁ A] at this
    linarith
  have hgt : |r - s| < dist c₁ c₂ := by
    rw [abs_sub_lt_iff]
    constructor
    · have := dist_triangle A c₂ c₁
      rw [dist_comm c₂ c₁] at this
      linarith
    · have := dist_triangle B c₁ c₂
      linarith
  obtain ⟨P, Q, hPQ, hP₁, hP₂, hQ₁, hQ₂⟩ := exists_two_common_points hgt hlt
  exact ⟨P, Q, hPQ, onCircle_iff.2 hP₁, onCircle_iff.2 hP₂, onCircle_iff.2 hQ₁,
    onCircle_iff.2 hQ₂⟩

/-- **Intersection 4, in LeanEuclid's corrected form, holds in the plane.** If the circle α
passes through A, inside β, and a point B outside β is inside or on α, the two circles cut
one another in two points. -/
theorem circles_meet_of_on_inside_outside : Hand.circles_meet_of_on_inside_outside plane := by
  intro A B α β hAα hBα hAβ hBβ
  rw [onCircle_iff] at hAα
  rw [insideCircle_iff, onCircle_iff] at hBα
  rw [insideCircle_iff] at hAβ
  obtain ⟨hBβ₁, hBβ₂⟩ := hBβ
  rw [insideCircle_iff] at hBβ₁
  rw [onCircle_iff] at hBβ₂
  obtain ⟨⟨c₁, r⟩, hr⟩ := α
  obtain ⟨⟨c₂, s⟩, hs⟩ := β
  dsimp only at hAα hBα hAβ hBβ₁ hBβ₂
  have hBβ : s < dist B c₂ := lt_of_le_of_ne (not_lt.1 hBβ₁) (Ne.symm hBβ₂)
  have hBα' : dist B c₁ ≤ r := by rcases hBα with h | h <;> linarith
  have hlt : dist c₁ c₂ < r + s := by
    have := dist_triangle c₁ A c₂
    rw [dist_comm c₁ A] at this
    linarith
  have hgt : |r - s| < dist c₁ c₂ := by
    rw [abs_sub_lt_iff]
    constructor
    · have := dist_triangle A c₂ c₁
      rw [dist_comm c₂ c₁] at this
      linarith
    · have := dist_triangle B c₁ c₂
      linarith
  obtain ⟨P, Q, hPQ, hP₁, hP₂, hQ₁, hQ₂⟩ := exists_two_common_points hgt hlt
  exact ⟨P, Q, hPQ, onCircle_iff.2 hP₁, onCircle_iff.2 hP₂, onCircle_iff.2 hQ₁,
    onCircle_iff.2 hQ₂⟩

end Model.Euclidean
