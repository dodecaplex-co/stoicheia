import Elements.Figure.Triangles
import Elements.Figure.RuleBase
import Elements.Figure.Incidence

/-!
# Book Zero: choosing a point on a circle

A straight line through an interior point can avoid every other point of a finite
list. Where it cuts the circle supplies a circumference point outside that list.
The construction uses circle intersections and lengths, without Circle 2 or Circle 3.
-/

namespace Elements

open Tacit

variable {A B C D E F : Point} {L M N : Line} {α β : Circle}

namespace RuleProofs.CirclePoints

/-- Two circles about distinct endpoints meet off their joining line; a same-side point avoids
the given list. -/
theorem exists_off_line (hAB : A ≠ B) (avoid : List Point) :
    ∃ P : Point, Triangle A B P ∧ P ∉ avoid := by
  obtain ⟨α, hBα, hAα⟩ := Postulate3 B A hAB.symm
  obtain ⟨β, hAβ, hBβ⟩ := Postulate3 A B hAB
  obtain ⟨C, -, -, hCα, hCβ, -, -⟩ :=
    circles_meet hAα (centre_inside hBα) (centre_inside hAβ) hBβ
  obtain ⟨L, hA, hB⟩ := Postulate1 A B hAB
  have hC : ¬ OnLine C L := by
    intro hCL
    have h₁ : ‖A C‖ = ‖A B‖ := Definition15 hAβ hCβ hBβ
    have h₂ : ‖B C‖ = ‖B A‖ := Definition15 hBα hCα hAα
    have hCA : C ≠ A := RuleProofs.Order.ne_of_centre_of_on hAβ hCβ
    have hCB : C ≠ B := RuleProofs.Order.ne_of_centre_of_on hBα hCα
    rcases between_cases hAB hCB.symm hCA.symm hA hB hCL with h | h | h
    · have := len_lt_of_between h
      rw [h₁] at this
      exact lt_irrefl _ this
    · have := len_lt_of_between h
      rw [h₂] at this
      exact lt_irrefl _ this
    · have := len_lt_of_between h
      rw [h₁] at this
      exact lt_irrefl _ this
  obtain ⟨P, hPC, hP⟩ := exists_point_same_side hC avoid
  refine ⟨P, fun ⟨M, hAM, hBM, hPM⟩ => ?_, hP⟩
  exact not_on_line_of_same_side hPC ((line_unique hAB hAM hBM hA hB) ▸ hPM)



/-- Choose a line through O avoiding the finitely many intersections with a transverse line. -/
theorem line_avoiding_points (O : Point) (avoid : List Point) :
    ∃ L : Line, OnLine O L ∧ ∀ P ∈ avoid, P ≠ O → ¬ OnLine P L := by
  classical
  obtain ⟨T, hT⟩ := exists_point [O]
  have hOT : O ≠ T := fun e => hT (e ▸ List.mem_singleton_self O)
  obtain ⟨R, hOTR, _⟩ := exists_off_line hOT []
  obtain ⟨M, hTM, hRM⟩ := Postulate1 T R hOTR.ne₂₃
  have hOM : ¬ OnLine O M := hOTR.bca.off_line hTM hRM
  let f (P : Point) : Line := Classical.choose (collinear_of_two O P)
  have hf (P : Point) : OnLine O (f P) ∧ OnLine P (f P) :=
    Classical.choose_spec (collinear_of_two O P)
  let g (P : Point) : Point :=
    if h : ∃ X, OnLine X M ∧ OnLine X (f P) then Classical.choose h else O
  obtain ⟨Q, hQM, hQ⟩ := exists_point_on_line M (avoid.map g)
  have hQoff (P : Point) (hP : P ∈ avoid) : ¬ OnLine Q (f P) := by
    intro hQf
    have hex : ∃ X, OnLine X M ∧ OnLine X (f P) := ⟨Q, hQM, hQf⟩
    have hg : OnLine (g P) M ∧ OnLine (g P) (f P) := by
      simp only [g, dite_eq_left hex]
      exact Classical.choose_spec hex
    have hQg : Q ≠ g P := fun e => hQ (e ▸ List.mem_map_of_mem hP)
    exact hOM (line_unique hQg hQf hg.2 hQM hg.1 ▸ (hf P).1)
  have hOQ : O ≠ Q := fun e => hOM (e ▸ hQM)
  obtain ⟨L, hOL, hQL⟩ := Postulate1 O Q hOQ
  refine ⟨L, hOL, fun P hP hPO hPL => ?_⟩
  exact hQoff P hP (line_unique hPO.symm hOL hPL (hf P).1 (hf P).2 ▸ hQL)

end RuleProofs.CirclePoints

/-- Let a point be taken on the circle α. (Points 7) Intersect a line through an interior point
that avoids every other forbidden point. -/
theorem Tacit.exists_point_on_circle (α : Circle) (avoid : List Point) :
    ∃ A : Point, OnCircle A α ∧ A ∉ avoid := by
  obtain ⟨O, hO, _⟩ := Elements.Tacit.exists_point_inside_circle α []
  obtain ⟨L, hOL, hL⟩ := RuleProofs.CirclePoints.line_avoiding_points O avoid
  obtain ⟨A, _, _, hAL, hA, _, _⟩ := line_meets_circle_of_inside hO hOL
  exact ⟨A, hA, fun h => hL A h (fun e => inside_not_on (e ▸ hO) hA) hAL⟩

end Elements
