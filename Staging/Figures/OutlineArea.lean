import Staging.Figures.Division
import Elements.Figure.Areas
import Elements.Figure.Sums

/-!
The area of an outline proposed by brief 0013, using the content theorem.
No proposition of the Elements is cited; through `Outline.lean` it imports I.23, which only
`outline_bounded` uses.
-/

namespace Elements.Figures

/-- An area selected from divisions of the outline. A division exists (`division_exists`)
and any two have the same sum (`divisions_equal`), so every division gives this area
(`area_eq`). -/
noncomputable def Outline.area (F : Outline) : Area :=
  Classical.epsilon fun a : Area => ∃ R : Apart, Divides F.region R ∧ R.area = a

/-- Two divisions of an outline have the same sum.
This follows from the content theorem (`Apart.area_eq_of_same_region`). -/
theorem divisions_equal (F : Outline) (R S : Apart)
    (hR : Divides F.region R) (hS : Divides F.region S) : R.area = S.area := by
  exact Apart.area_eq_of_same_region R S (fun X => (hR X).trans (hS X).symm)

/-- Every division gives the selected area of the outline.
This derivation depends on the content theorem; the division given is its own witness. -/
theorem area_eq (F : Outline) (R : Apart) (hR : Divides F.region R) :
    F.area = R.area := by
  have hex : ∃ a : Area, ∃ T : Apart, Divides F.region T ∧ T.area = a :=
    ⟨R.area, R, hR, rfl⟩
  obtain ⟨T, hT, ht⟩ := Classical.epsilon_spec hex
  exact ht.symm.trans (divisions_equal F T R hT hR)

/-- The area depends only on the region: a division of one region divides the other
(`division_exists`, `area_eq`). -/
theorem area_congr (F G : Outline)
    (h : ∀ X : Point, F.region X ↔ G.region X) : F.area = G.area := by
  obtain ⟨R, hR⟩ := division_exists F
  have hG : Divides G.region R := fun X => (hR X).trans (h X)
  exact (area_eq F R hR).trans (area_eq G R hG).symm

/-- Reading the same boundary another way leaves its area unchanged: the same boundary has
the same region (`same_boundary_region`), and so the same area (`area_congr`). -/
theorem area_of_same_boundary (F G : Outline)
    (h : ∀ X : Point, F.boundary X ↔ G.boundary X) : F.area = G.area :=
  area_congr F G (same_boundary_region F G h)

/-- A strictly convex outline has its explicit fan sum for area: the fan divides its region
(`convex_fan`), which is the outline's region (`convex_loop_region`), so the fan's sum is the
area (`area_eq`). -/
theorem convex_fan_area {cs : List Point} (h : ConvexOutline cs) :
    (singleOutline cs (convex_loop_region h).1).area = fanSum cs := by
  obtain ⟨R, hp, hd⟩ := convex_fan h
  have hR : Divides (singleOutline cs (convex_loop_region h).1).region R := by
    intro X
    exact (hd X).trans (((single_region cs (convex_loop_region h).1 X).trans
      ((convex_loop_region h).2 X)).symm)
  rw [area_eq _ R hR]
  unfold Apart.area fanSum
  rw [hp]

end Elements.Figures
