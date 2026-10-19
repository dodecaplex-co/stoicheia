module

public import Model.Euclidean
public import Model.Hand

/-!
# How magnitudes add and compare, in the plane

Every kind of magnitude is read as `ℝ≥0`, with its own `0`, `+` and `<`, so the eight
magnitude laws are facts about the non-negative reals: addition is associative and
commutative with 0 as its identity, `<` is a strict total order, nothing is below 0, and
adding the same amount keeps `<`. `not_lt_zero` is the one that needs the reals to be
non-negative, as MODEL.md says.
-/

@[expose] public section

namespace Model.Euclidean

open scoped NNReal

/-- **`add_assoc` holds in the plane.** -/
theorem add_assoc : Hand.add_assoc plane := by
  intro _
  change ∀ a b c : ℝ≥0, a + b + c = a + (b + c)
  exact _root_.add_assoc

/-- **`add_comm` holds in the plane.** -/
theorem add_comm : Hand.add_comm plane := by
  intro _
  change ∀ a b : ℝ≥0, a + b = b + a
  exact _root_.add_comm

/-- **`add_lt_add_right` holds in the plane.** -/
theorem add_lt_add_right : Hand.add_lt_add_right plane := by
  intro _
  change ∀ {a b : ℝ≥0} (c : ℝ≥0), a < b → a + c < b + c
  exact fun _ h => add_lt_add_of_lt_of_le h le_rfl

/-- **`add_zero` holds in the plane.** -/
theorem add_zero : Hand.add_zero plane := by
  intro _
  change ∀ a : ℝ≥0, a + 0 = a
  exact _root_.add_zero

/-- **`lt_irrefl` holds in the plane.** -/
theorem lt_irrefl : Hand.lt_irrefl plane := by
  intro _
  change ∀ a : ℝ≥0, ¬ a < a
  exact _root_.lt_irrefl

/-- **`lt_trans` holds in the plane.** -/
theorem lt_trans : Hand.lt_trans plane := by
  intro _
  change ∀ {a b c : ℝ≥0}, a < b → b < c → a < c
  exact _root_.lt_trans

/-- **`lt_trichotomy` holds in the plane.** -/
theorem lt_trichotomy : Hand.lt_trichotomy plane := by
  intro _
  change ∀ a b : ℝ≥0, a < b ∨ a = b ∨ b < a
  exact _root_.lt_trichotomy

/-- **`not_lt_zero` holds in the plane:** the one magnitude law that needs the reals to be
non-negative. -/
theorem not_lt_zero : Hand.not_lt_zero plane := by
  intro _
  change ∀ a : ℝ≥0, ¬ a < 0
  exact fun _ => not_lt.2 zero_le

end Model.Euclidean
