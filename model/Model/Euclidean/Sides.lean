module

public import Model.Euclidean
public import Model.Euclidean.CircleSides
public import Model.Laws.sides

/-!
# The same-side rules, in the plane

`SameSide A B L` is read as Mathlib's strict same-side relation, `L.SSameSide A B`: there
are points `P` and `Q` of `L` with `A - P` and `B - Q` pointing the same way, and neither
`A` nor `B` on `L`. The lemmas below unfold the reading of `OnLine`, `SameSide` and
`Between`, so that the proofs can stand on Mathlib's lemmas about sides and betweenness,
the work of Joseph Myers.
-/

@[expose] public section

namespace Model.Euclidean

/-! ## How the words read -/

@[simp] theorem onLine_iff {A : Plane} {L : Line} : plane.OnLine A L ↔ A ∈ L.1 :=
  Iff.rfl

/-- `SameSide` is Mathlib's strict same-side relation. -/
@[simp] theorem sameSide_iff {A B : Plane} {L : Line} :
    plane.SameSide A B L ↔ L.1.SSameSide A B :=
  Iff.rfl

@[simp] theorem between_iff {A B C : Plane} : plane.Between A B C ↔ Sbtw ℝ A B C :=
  Iff.rfl

end Model.Euclidean
