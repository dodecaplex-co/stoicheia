import Staging.Figures.Outline
import Staging.Figures.Content
import Staging.Figures.ConvexCover
import Staging.Figures.Arrangement
import Staging.Figures.DivisionFacts
import Staging.Figures.Extract
import Elements.Figure.Rectilineal

/-!
Division statements proposed by brief 0013, with their proofs.
The supplied Outline never contains a division witness.
No proposition of the Elements is cited; through `Outline.lean` this file imports I.23,
which only `outline_bounded` uses.
-/

namespace Elements.Figures

/-- Every admitted outline has a division into nondegenerate triangles. -/
theorem division_exists (F : Outline) : ∃ R : Apart, Divides F.region R := by
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
  obtain ⟨rs, hne, hsub, -, hcov⟩ := outline_cells_cover F P hP ls hs qs ha hc hl
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

/-- Every figure previously supplied as an Apart has an outline with exactly
the same region, including holes, separate pieces and contacts at corners. -/
theorem apart_has_outline (R : Apart) : ∃ F : Outline, Divides F.region R := by
  /- Cut the sides at the corners; the elementary lines along one triangle only, grouped by
  linked triangles, are even in number at every corner of each group, so they are the sides of
  simple contours (`Extract.cycles`). A contour lies wholly inside or outside another, off it,
  since the other contour has one inside-status on all the closed triangles of a class
  (`Extract.linked_status`), and the first lies on closed triangles of its own class; so
  contours are compatible. Off the sides, crossing parity counts the triangles
  (`Extract.parity_at`). -/
  exact Extract.apart_outline R

end Elements.Figures
