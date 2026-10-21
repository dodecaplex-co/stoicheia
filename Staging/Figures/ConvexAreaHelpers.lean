import Staging.Figures.ConvexFacts

/-!
# Areas of fans and changes of diagonal

At each crossing, the four small triangles show that changing a diagonal
preserves the sum. Successive changes compare fans based at consecutive corners.
David Hilbert's theory of content provides the classical route, which we
gratefully acknowledge, together with the contributions of Gérard, F. Schur and
O. Stolz recorded in brief 0006. Here the comparison is between vertex fans;
independence from arbitrary divisions into triangles is the content theorem's further step
(`Apart.area_eq_of_same_region`, in `Content.lean`).
-/

namespace Elements.Figures

open Tacit

/-- Changing the diagonal of a convex quadrilateral preserves its triangle sum. -/
theorem area_diagonal_change {A B C D : Point}
    (hAC : OppositeSidesOf A C B D) (hBD : OppositeSidesOf B D A C) :
    △ A B C + △ A C D = △ B C D + △ A B D := by
  obtain ⟨X, hAXC, hBXD⟩ := diagonals_cross hAC hBD
  have h := (quadArea_rotate_of_cross hAXC hBXD).symm
  simpa only [quadArea, area_cab B D A] using h

/-- The sum of the triangles from a fixed point to a chain of sides. -/
noncomputable def fanArea (O : Point) (ps : List Point) : Area :=
  Magnitude.sum ((segments ps).map fun s => △ O s.1 s.2)

/-- Appending A adds the triangle from O to the previous endpoint and A. -/
theorem fanArea_append (O A C : Point) (ps : List Point) :
    fanArea O ((C :: ps) ++ [A]) = fanArea O (C :: ps) + △ O (endOf C ps) A := by
  induction ps generalizing C with
  | nil => simp [fanArea, segments, Magnitude.sum, endOf, add_zero, add_comm]
  | cons D ps ih =>
    change △ O C D + fanArea O ((D :: ps) ++ [A]) =
      (△ O C D + fanArea O (D :: ps)) + △ O (endOf D ps) A
    rw [ih, add_assoc]

/-- Moving the fan's corner from A to B exchanges the two end triangles through
successive diagonal changes. -/
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
    rw [← add_assoc, area_diagonal_change hCD.1 hCD.2, add_assoc, ih D htail, add_assoc]

/-- When the intervening diagonals cross, the fans based at consecutive corners
have the same sum. -/
theorem fanArea_rotate (A B C : Point) (ps : List Point)
    (h : ∀ s ∈ segments (C :: ps),
      OppositeSidesOf A s.1 B s.2 ∧ OppositeSidesOf B s.2 A s.1) :
    fanArea A (B :: C :: ps) = fanArea B ((C :: ps) ++ [A]) := by
  rw [fanArea_append, area_cab B (endOf C ps) A]
  exact fanArea_transfer A B C ps h

/-- Appending a final side adds exactly its triangle to the fan sum. -/
theorem fanArea_append_pair (O A B : Point) (ps : List Point) :
    fanArea O (ps ++ [A, B]) = fanArea O (ps ++ [A]) + △ O A B := by
  unfold fanArea
  rw [segments_join ps [B] A]
  simp only [segments, List.map_append, List.map_cons,
    List.map_nil, Magnitude.sum_append, Magnitude.sum_singleton]

/-- Reversing the chain preserves a fan's sum with its apex fixed: each triangle
has its last two corners exchanged, and the order of addition is reversed. -/
theorem fanArea_reverse (O : Point) (ps : List Point) :
    fanArea O ps.reverse = fanArea O ps := by
  induction ps with
  | nil => rfl
  | cons A ps ih =>
    cases ps with
    | nil => rfl
    | cons B ps =>
      rw [List.reverse_cons, List.reverse_cons, List.append_assoc]
      change fanArea O (ps.reverse ++ [B, A]) = △ O A B + fanArea O (B :: ps)
      rw [fanArea_append_pair]
      rw [List.reverse_cons] at ih
      rw [ih, area_swap O B A, add_comm]

/-- The outline's fan sum is the fixed-apex sum on the remaining corners. -/
theorem fanSum_cons (A : Point) (ps : List Point) :
    fanSum (A :: ps) = fanArea A ps := by
  simp only [fanSum, fan, List.map_map, fanArea, Function.comp_def]

end Elements.Figures
