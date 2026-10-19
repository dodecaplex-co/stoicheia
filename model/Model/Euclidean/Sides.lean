module

public import Model.Euclidean
public import Model.Euclidean.CircleSides
public import Model.Laws.sides

/-!
# The same-side rules, in the plane

`SameSide A B L` is read as Mathlib's strict same-side relation, `L.SSameSide A B`: there
are points `P` and `Q` of `L` with `A - P` and `B - Q` pointing the same way, and neither
`A` nor `B` on `L`. The five same-side rules hold for this reading. Reflexivity uses the
line's nonemptiness, and Same side 5 uses the plane dichotomy proved in
`sSameSide_or_sOppSide`. The proofs stand on Mathlib's lemmas about sides, the work of
Joseph Myers, with our thanks.
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

/-! ## Same side -/

/-- **Same side 1 holds in the plane.** A line is nonempty because its direction has
dimension one, so Mathlib's strict same-side relation is reflexive off it. -/
theorem same_side_refl : Hand.same_side_refl plane := by
  intro A L hA
  have hL : (L.1 : Set Plane).Nonempty := by
    apply L.1.nonempty_iff_ne_bot.2
    intro h
    have hdim := L.2
    rw [h, AffineSubspace.direction_bot] at hdim
    simp at hdim
  exact AffineSubspace.sSameSide_self_iff.2 ⟨hL, hA⟩

/-- **Same side 2 holds in the plane.** -/
theorem same_side_symm : Hand.same_side_symm plane := by
  intro A B L hAB
  exact AffineSubspace.SSameSide.symm hAB

/-- **Same side 3 holds in the plane.** -/
theorem not_on_line_of_same_side : Hand.not_on_line_of_same_side plane := by
  intro A B L hAB
  exact AffineSubspace.SSameSide.left_notMem hAB

/-- **Same side 4 holds in the plane.** Symmetry followed by transitivity gives the
relation between the two points on the same side as A. -/
theorem same_side_trans : Hand.same_side_trans plane := by
  intro A B C L hAB hAC
  exact (AffineSubspace.SSameSide.symm hAB).trans hAC

/-- **Same side 5 holds in the plane.** The two-dimensional dichotomy
`sSameSide_or_sOppSide` places A and B on opposite sides. If C is opposite A too, then
B and C are on the same side. -/
theorem same_side_or : Hand.same_side_or plane := by
  intro A B C L hA hB hC hnot
  rcases sSameSide_or_sOppSide L.2 hA hB with hAB | hAB
  · exact False.elim (hnot hAB)
  · rcases sSameSide_or_sOppSide L.2 hA hC with hAC | hAC
    · exact Or.inl hAC
    · exact Or.inr (hAB.symm.trans hAC)

end Model.Euclidean
