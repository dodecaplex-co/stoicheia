import Staging.Figures.Cells
import Staging.Figures.ContentFacts

/-!
# Staging: the content of a figure does not depend on its division

The central statement of brief 0013 (a draft for the owner's approval), with its proof: two
divisions of a figure into triangles that lie apart, whose triangles cover the same points,
have the same sum. The figure may have holes, touch itself at a
corner, or be in pieces; the triangles may meet a side of another at a corner of their own.
Euclid takes it for granted under I.45; David Hilbert proved it, for the measure of area he
builds from his axioms (*The Foundations of Geometry*, chapter IV, section 20).
-/

namespace Elements.Figures

open Tacit

/-- The triangles `R` divide the region `U`: a point is within or on one of them exactly when
it is in `U`. -/
def Divides (U : Point → Prop) (R : Apart) : Prop :=
  ∀ X : Point, Covers R.pieces X ↔ U X

/-- **The content theorem**: two divisions into triangles that lie apart, covering the same
points, have the same sum. -/
theorem Apart.area_eq_of_same_region (R S : Apart)
    (h : ∀ X : Point, Covers R.pieces X ↔ Covers S.pieces X) : R.area = S.area := by
  /- One table of common parts, chosen once (`convex_intersection`): the triangle `r` of `R`
  and the triangle `s` of `S` meet in a cell or in nothing, and `m r s` is its area. The
  same chosen part is counted in its row and in its column. -/
  let m : Point × Point × Point → Point × Point × Point → Area := fun r s =>
    cellArea (Content.meet (Content.triCell r) (Content.triCell s))
  /- A row tiles its triangle of `R`: the triangles of `S` lie apart, and cover the points
  of `r`, since `R` and `S` cover the same points. -/
  have hrow : ∀ r ∈ R.pieces, Magnitude.sum (S.pieces.map (m r)) = △ r.1 r.2.1 r.2.2 := by
    intro r hr
    obtain ⟨P, -, -, hPr, hPa⟩ := Content.triCell_eq (R.triangle r hr)
    rw [← hPa]
    refine Content.row_area P S.pieces S.apart
      (fun s => Content.meet (Content.triCell r) (Content.triCell s)) ?_ ?_ ?_
    · intro s X hX
      exact Content.triCell_core s (Content.meet_core _ _ hX).2
    · intro s hs
      exact Tiling.agreeOff_trans (Content.meet_region _ _) (Tiling.agreeOff_of_iff fun X =>
        and_congr ((Content.triCell_region (R.triangle r hr) X).trans (hPr X).symm)
          (Content.triCell_region (S.triangle s hs) X))
    · intro X hX
      exact (h X).mp ⟨r, hr, (hPr X).mp hX⟩
  /- A column tiles its triangle of `S`, in the same way, with the same common parts. -/
  have hcol : ∀ s ∈ S.pieces,
      Magnitude.sum (R.pieces.map fun r => m r s) = △ s.1 s.2.1 s.2.2 := by
    intro s hs
    obtain ⟨Q, -, -, hQr, hQa⟩ := Content.triCell_eq (S.triangle s hs)
    rw [← hQa]
    refine Content.row_area Q R.pieces R.apart
      (fun r => Content.meet (Content.triCell r) (Content.triCell s)) ?_ ?_ ?_
    · intro r X hX
      exact Content.triCell_core r (Content.meet_core _ _ hX).1
    · intro r hr
      exact Tiling.agreeOff_trans (Content.meet_region _ _) (Tiling.agreeOff_of_iff fun X =>
        (and_congr (Content.triCell_region (R.triangle r hr) X)
          ((Content.triCell_region (S.triangle s hs) X).trans (hQr X).symm)).trans and_comm)
    · intro X hX
      exact (h X).mpr ⟨s, hs, (hQr X).mp hX⟩
  /- The table has one total, by rows or by columns (`sum_exchange`). -/
  calc R.area = Magnitude.sum (R.pieces.map fun r => △ r.1 r.2.1 r.2.2) := rfl
    _ = Magnitude.sum (R.pieces.map fun r => Magnitude.sum (S.pieces.map (m r))) :=
      congrArg Magnitude.sum (List.map_congr_left fun r hr => (hrow r hr).symm)
    _ = Magnitude.sum (S.pieces.map fun s => Magnitude.sum (R.pieces.map fun r => m r s)) :=
      sum_exchange R.pieces S.pieces m
    _ = Magnitude.sum (S.pieces.map fun s => △ s.1 s.2.1 s.2.2) :=
      congrArg Magnitude.sum (List.map_congr_left hcol)
    _ = S.area := rfl

/-- A triangle divided into triangles that lie apart has their sum for its area. -/
theorem triangle_division_area {A B C : Point} (hABC : Triangle A B C) (R : Apart)
    (hR : Divides (fun X => OnOrInsideTriangle X A B C) R) : R.area = △ A B C := by
  /- The triangle alone is a division of itself, with its own area for sum. -/
  let S : Apart :=
    ⟨[(A, B, C)], List.cons_ne_nil _ _, fun t ht => by
      rw [List.mem_singleton] at ht
      subst ht
      exact hABC, List.pairwise_singleton _ _⟩
  have hS : ∀ X : Point, Covers S.pieces X ↔ OnOrInsideTriangle X A B C := by
    intro X
    simp [S, Covers]
  calc R.area = S.area := Apart.area_eq_of_same_region R S fun X => (hR X).trans (hS X).symm
    _ = △ A B C := Magnitude.sum_singleton _

end Elements.Figures
