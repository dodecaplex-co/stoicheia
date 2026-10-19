module

public import Model.Euclidean
public import Model.Laws.lengths

/-!
# The metric length laws in the plane

Lengths are Mathlib's nonnegative distances. A distance is zero exactly when its
endpoints coincide, and reversing the endpoints preserves it.
-/

@[expose] public section

namespace Model.Euclidean

/-- **`eq_of_len_eq_zero` holds in the plane.** -/
theorem eq_of_len_eq_zero : Hand.eq_of_len_eq_zero plane := by
  intro A B h
  exact nndist_eq_zero.1 h

/-- **`len_self` holds in the plane.** -/
theorem len_self : Hand.len_self plane := by
  intro A
  exact nndist_self A

/-- **`len_symm` holds in the plane.** -/
theorem len_symm : Hand.len_symm plane := by
  intro A B
  exact nndist_comm A B

end Model.Euclidean
