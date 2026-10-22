import Elements.Figure.Outlines
import Elements.Figure.Content
import Elements.Figure.Convex.Cover
import Elements.Figure.Arrangements
import Elements.Figure.Divisions.DivisionFacts
import Elements.Figure.Divisions.Extract
import Elements.Figure.Rectilineal
import Elements.Figure.Areas
import Elements.Figure.Sums

/-!
# Book Zero: divisions of an outline, and its area

The last steps of brief 0013's route (section 8: D9, D10 and E1). A figure is given by its
outline alone (`Outline`, in `Foundations/Figures.lean`), which holds no division, triangle
list or area; these theorems supply them.

* **A division exists** (`division_exists`, D9). Every outline is divided into triangles
  that lie apart (`Apart`) and cover exactly its region (`Divides`): the fans of the cells
  selected from an arrangement of its side lines (`Arrangements.lean`). A convex outline's
  own fan divides it (`convex_fan`).
* **The figures given with triangles keep their place** (`apart_has_outline`, D10). Every
  figure given with triangles that lie apart has an outline with exactly their region, holes,
  separate pieces and contacts at corners included (helpers in `Divisions/`).
* **One area** (E1, the last section). By the content theorem
  (`Apart.area_eq_of_same_region`, in `Content.lean`), two divisions of an outline have one
  sum (`divisions_equal`), so the area chosen from its divisions (`Outline.area`) is the sum
  of every division (`area_eq`). Equal regions, and so equal boundaries, have equal areas
  (`area_congr`, `area_of_same_boundary`), and a convex outline's area is its fan's sum
  (`convex_fan_area`).

Through these, I.45 and II.14 take a figure by its outline (`Prop45.outline`,
`Prop14.outline`, `Prop14.outline_side`). Nothing in Book Zero cites a proposition of the
*Elements*.
-/

namespace Elements.Figures

/-- Every admitted outline has a division into nondegenerate triangles. -/
theorem division_exists (F : Outline) : ∃ R : Apart, Divides F.Region R := by
  /- A convex cell holds the region strictly inside it (`outline_enclosure`); the straight
  lines of the contour sides (`outline_side_lines`) cut it into cells with disjoint insides
  (`convex_arrangement`). The cells with a point inside the figure make up its closed region
  exactly (`outline_cells_cover`), and their fans, put together, divide it
  (`DivisionFacts.cells_division`). -/
  obtain ⟨P, hP⟩ := outline_enclosure F
  obtain ⟨ls, hls⟩ := outline_side_lines F
  have hs : ∀ ps ∈ F.loops, ∀ s ∈ sides ps, ∃ L ∈ ls, OnLine s.1 L ∧ OnLine s.2 L := by
    intro ps hps s hs
    obtain ⟨L, h₁, h₂⟩ := collinear_of_two s.1 s.2
    exact ⟨L, (hls L).mpr ⟨ps, hps, s, hs, h₁, h₂⟩, h₁, h₂⟩
  obtain ⟨qs, -, ha, hc, hl⟩ := convex_arrangement P ls
  obtain ⟨rs, hne, hsub, -, hcov⟩ := outline_cells_cover F P hP ls hs qs hc hl
  obtain ⟨R, -, hR⟩ := DivisionFacts.cells_division rs hne (List.Pairwise.sublist hsub ha)
  exact ⟨R, fun X => (hR X).trans (hcov X).symm⟩

/-- The explicit fan divides a strictly convex outline: its pieces are triangles
(`fan_triangle`), they lie apart (`fan_apart`), and they cover the region (`fan_covers`). -/
theorem convex_fan {cs : List Point} (h : ConvexOutline cs) :
    ∃ R : Apart, R.pieces = fan cs ∧ Divides (ConvexRegion cs) R := by
  have hne : fan cs ≠ [] := by
    rcases cs with _ | ⟨O, cs⟩
    · simp [ConvexOutline] at h
    rcases cs with _ | ⟨A, cs⟩
    · simp [ConvexOutline] at h
    rcases cs with _ | ⟨B, cs⟩
    · simp [ConvexOutline] at h
    simp [fan, segments]
  let R : Apart := ⟨fan cs, hne, fan_triangle h, fan_apart h⟩
  exact ⟨R, rfl, fun X => fan_covers h X⟩

/-- Every figure given with triangles that lie apart (`Apart`) has an outline with exactly
the same region, including holes, separate pieces and contacts at corners. -/
theorem apart_has_outline (R : Apart) : ∃ F : Outline, Divides F.Region R := by
  /- Cut the sides at the corners; the elementary lines along one triangle only, grouped by
  linked triangles, are even in number at every corner of each group, so they are the sides of
  simple contours (`Extract.cycles`). A contour lies wholly inside or outside another, off it,
  since the other contour has one inside-status on all the closed triangles of a class
  (`Extract.linked_status`), and the first lies on closed triangles of its own class; so
  contours are compatible. Off the sides, crossing parity counts the triangles
  (`Extract.parity_at`). -/
  exact Extract.apart_outline R

end Elements.Figures

/-! ## The area of an outline

Step E1 of brief 0013's route: the area of a figure given by its outline, from the content
theorem and a division of the outline. -/

namespace Elements.Figures

/-- Two divisions of an outline have the same sum.
This follows from the content theorem (`Apart.area_eq_of_same_region`). -/
theorem divisions_equal (F : Outline) (R S : Apart)
    (hR : Divides F.Region R) (hS : Divides F.Region S) : R.area = S.area := by
  exact Apart.area_eq_of_same_region R S (fun X => (hR X).trans (hS X).symm)

/-- Every division gives the selected area of the outline.
This derivation depends on the content theorem; the division given is its own witness. -/
theorem area_eq (F : Outline) (R : Apart) (hR : Divides F.Region R) :
    F.area = R.area := by
  have hex : ∃ a : Area, ∃ T : Apart, Divides F.Region T ∧ T.area = a :=
    ⟨R.area, R, hR, rfl⟩
  obtain ⟨T, hT, ht⟩ := Classical.epsilon_spec hex
  exact ht.symm.trans (divisions_equal F T R hT hR)

/-- The area depends only on the region: a division of one region divides the other
(`division_exists`, `area_eq`). -/
theorem area_congr (F G : Outline)
    (h : ∀ X : Point, F.Region X ↔ G.Region X) : F.area = G.area := by
  obtain ⟨R, hR⟩ := division_exists F
  have hG : Divides G.Region R := fun X => (hR X).trans (h X)
  exact (area_eq F R hR).trans (area_eq G R hG).symm

/-- Reading the same boundary another way leaves its area unchanged: the same boundary has
the same region (`same_boundary_region`), and so the same area (`area_congr`). -/
theorem area_of_same_boundary (F G : Outline)
    (h : ∀ X : Point, F.Boundary X ↔ G.Boundary X) : F.area = G.area :=
  area_congr F G (same_boundary_region F G h)

/-- A strictly convex outline has its explicit fan sum for area: the fan divides its region
(`convex_fan`), which is the outline's region (`convex_loop_region`), so the fan's sum is the
area (`area_eq`). -/
theorem convex_fan_area {cs : List Point} (h : ConvexOutline cs) :
    (singleOutline cs (convex_loop_region h).1).area = fanSum cs := by
  obtain ⟨R, hp, hd⟩ := convex_fan h
  have hR : Divides (singleOutline cs (convex_loop_region h).1).Region R := by
    intro X
    exact (hd X).trans (((single_region cs (convex_loop_region h).1 X).trans
      ((convex_loop_region h).2 X)).symm)
  rw [area_eq _ R hR]
  unfold Apart.area fanSum
  rw [hp]

end Elements.Figures
