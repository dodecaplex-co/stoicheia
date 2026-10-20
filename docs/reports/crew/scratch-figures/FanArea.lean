import Elements.Figure.Areas
import Elements.Figure.Sums
import Elements.Figure.Sides

/-!
A scratch proof of brief 0013, kept unbuilt (docs/WORKFLOW.md, section 2): the probe of
19 October 2026 into I.45's and II.14's figures. From the root of a checkout that has built
`Elements`, `lake env lean` on this file checks it. Its arguments were carried into
`Staging/Figures/` (`ConvexFacts.lean`, `Closed.lean`, `ConvexAreaHelpers.lean`).
-/

namespace Elements.Probe

open Tacit

/-- Two separating diagonals meet inside both finite segments. -/
theorem diagonals_cross {A B C D : Point}
    (hAC : OppositeSidesOf A C B D) (hBD : OppositeSidesOf B D A C) :
    ∃ X : Point, Between A X C ∧ Between B X D := by
  obtain ⟨L, hB, hD⟩ := Postulate1 B D hAC.1
  obtain ⟨M, hA, hC⟩ := Postulate1 A C hBD.1
  have hac := hAC.oppositeSides hB hD
  have hbd := hBD.oppositeSides hA hC
  obtain ⟨X, hXL, hAXC⟩ := hac.exists_between
  have hXM := on_line_of_between_ends hAXC hA hC
  have hML : M ≠ L := fun e => hac.1 (e ▸ hA)
  have hBXD : Between B X D := pasch4 hML hXM hXL hB hD hAC.1
    (fun e => hbd.1 (e.symm ▸ hXM))
    (fun e => hbd.2.1 (e.symm ▸ hXM)) hbd.2.2
  exact ⟨X, hAXC, hBXD⟩

/-- Changing the diagonal of a convex quadrilateral preserves its triangle sum. -/
theorem flip {A B C D : Point}
    (hAC : OppositeSidesOf A C B D) (hBD : OppositeSidesOf B D A C) :
    △ A B C + △ A C D = △ B C D + △ A B D := by
  obtain ⟨X, hAXC, hBXD⟩ := diagonals_cross hAC hBD
  have h := (quadArea_rotate_of_cross hAXC hBXD).symm
  simpa only [quadArea, area_cab B D A] using h

noncomputable def fanArea (O : Point) (ps : List Point) : Area :=
  Magnitude.sum ((segments ps).map fun s => △ O s.1 s.2)

/-- Closing a chain adds the triangle on its final side. -/
theorem fanArea_close (O A C : Point) (ps : List Point) :
    fanArea O ((C :: ps) ++ [A]) = fanArea O (C :: ps) + △ O (endOf C ps) A := by
  induction ps generalizing C with
  | nil => simp [fanArea, segments, Magnitude.sum, endOf, add_zero, add_comm]
  | cons D ps ih =>
    change △ O C D + fanArea O ((D :: ps) ++ [A]) =
      (△ O C D + fanArea O (D :: ps)) + △ O (endOf D ps) A
    rw [ih, add_assoc]

/-- Moving a fan's corner across the edge AB is a sequence of diagonal changes. -/
theorem fanArea_transfer (A B C : Point) (ps : List Point)
    (h : ∀ s ∈ segments (C :: ps),
      OppositeSidesOf A s.1 B s.2 ∧ OppositeSidesOf B s.2 A s.1) :
    △ A B C + fanArea A (C :: ps) =
      fanArea B (C :: ps) + △ A B (endOf C ps) := by
  induction ps generalizing C with
  | nil => simp [fanArea, segments, Magnitude.sum, endOf, add_zero, add_comm]
  | cons D ps ih =>
    have hCD := h (C, D) (List.mem_cons_self ..)
    have htail : ∀ s ∈ segments (D :: ps),
        OppositeSidesOf A s.1 B s.2 ∧ OppositeSidesOf B s.2 A s.1 :=
      fun s hs => h s (List.mem_cons_of_mem _ hs)
    change △ A B C + (△ A C D + fanArea A (D :: ps)) =
      (△ B C D + fanArea B (D :: ps)) + △ A B (endOf D ps)
    rw [← add_assoc, flip hCD.1 hCD.2, add_assoc, ih D htail, add_assoc]

/-- The two fans of the same cyclic corner list, based at consecutive corners, agree. -/
theorem fanArea_rotate (A B C : Point) (ps : List Point)
    (h : ∀ s ∈ segments (C :: ps),
      OppositeSidesOf A s.1 B s.2 ∧ OppositeSidesOf B s.2 A s.1) :
    fanArea A (B :: C :: ps) = fanArea B ((C :: ps) ++ [A]) := by
  rw [fanArea_close, area_cab B (endOf C ps) A]
  exact fanArea_transfer A B C ps h

end Elements.Probe

#print axioms Elements.Probe.fanArea_rotate
