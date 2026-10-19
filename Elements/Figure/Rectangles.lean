import Elements.Figure.Parallelograms
import Elements.Figure.RuleBase
import Elements.Figure.Circles
import Elements.Foundations.DefinitionsII

/-!
# Book Zero: rectangles and squares

Book II names a rectangle by the two straight lines that contain it, and a square by
the straight line it is described on, and Euclid never doubts that the names follow
the lengths: that the rectangle contained by `AB`, `BC` is the rectangle contained by
`BA`, `BC`, or by `BC`, `AB`; that "since AC is equal to CE, the square on AC is also
equal to the square on CE" (II.9); or that a rectangle with a side that is nothing is
nothing. Nor does he doubt that a rectangle or a square may be named from any corner,
either way round. These are those facts.

None of them cites a proposition. That a rectangle drawn in a figure is the rectangle
contained by its sides needs I.4 and I.34, so it is proved in
`Elements/BookII/Rectangles.lean`.
-/

namespace Elements

open Tacit

variable {A B C D A' B' C' D' : Point} {a b : Length} {x : Area}

/-! ## A point off a straight line

Book II's figures begin with points on one straight line, and the first square or
perpendicular must stand on one side of it. Euclid never doubts that there is a
side to stand on. -/

/-- There is a point off the straight line `AB`, avoiding any points already in the
figure. The circles with centres `A` and `B` through each other cut one another
(System E, Intersection 5), and a point where they cut is off `AB`: on `AB` it would be
as far from `A` as `B` is, and as far from `B` as `A` is, and one of the three points
would lie between the other two (Definition 15; System E, Between 6 and Diagram-segment
1). Then any point on its side will do (System E, Points 5). -/
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
    have hCA : C ≠ A := ne_of_centre_of_on hAβ hCβ
    have hCB : C ≠ B := ne_of_centre_of_on hBα hCα
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

/-! ## The rectangle contained by two straight lines -/

/-- The rectangle contained by `AB`, `CD` depends only on the lengths of `AB` and `CD`:
straight lines equal to them contain the same rectangle. -/
theorem rect_congr (h₁ : ‖A B‖ = ‖A' B'‖) (h₂ : ‖C D‖ = ‖C' D'‖) :
    rect A B C D = rect A' B' C' D' := by
  unfold rect
  rw [h₁, h₂]

/-- Squares on equal straight lines are equal: "since AC is equal to CE, the square on
AC is also equal to the square on CE" (II.9). -/
theorem sq_congr (h : ‖A B‖ = ‖C D‖) : sq A B = sq C D :=
  rect_congr h h

/-- The square on `AB` is the square on `BA`. -/
theorem sq_symm (A B : Point) : sq A B = sq B A :=
  sq_congr (len_symm A B)

/-- The rectangle `ABCD`, read the other way round from `A`, is the rectangle `ADCB`. -/
theorem Rectangle.reverse (h : Rectangle A B C D) : Rectangle A D C B := by
  obtain ⟨hp, hA, hB, hC, hD⟩ := h
  have hAB : A ≠ B := hp.1.1
  have hBC : B ≠ C := hp.2.1
  have hCD : C ≠ D := hp.1.2.1
  have hDA : D ≠ A := hp.2.2.1
  refine ⟨hp.reverse, ?_, ?_, ?_, ?_⟩
  · rw [angle_symm hAB.symm hDA]; exact hA
  · rw [angle_symm hDA.symm hCD]; exact hD
  · rw [angle_symm hCD.symm hBC]; exact hC
  · rw [angle_symm hBC.symm hAB]; exact hB

/-- The rectangle `ABCD`, named from `B`, is the rectangle `BCDA`. -/
theorem Rectangle.rotate (h : Rectangle A B C D) : Rectangle B C D A :=
  ⟨h.1.rotate, h.2.2.1, h.2.2.2.1, h.2.2.2.2, h.2.1⟩

/-- Read either way round, two lengths contain the same areas: the rectangle `PQRS`
read as `PSRQ` has its sides about the angle at `P` in the other order. -/
theorem Contain.symm (h : Contain a b x) : Contain b a x := by
  rcases h with ⟨h0, hx⟩ | ⟨P, Q, R, S, hr, hPQ, hPS, hx⟩
  · exact Or.inl ⟨h0.symm, hx⟩
  · exact Or.inr ⟨P, S, R, Q, hr.reverse, hPS, hPQ, (quadArea_reverse P Q R S).trans hx⟩

/-- The rectangle contained by `AB`, `CD` is the rectangle contained by `CD`, `AB`. -/
theorem rect_comm (A B C D : Point) : rect A B C D = rect C D A B := by
  unfold rect
  have : Contain ‖A B‖ ‖C D‖ = Contain ‖C D‖ ‖A B‖ :=
    funext fun _ => propext ⟨Contain.symm, Contain.symm⟩
  rw [this]

/-- A rectangle with a side that is nothing is nothing: the rectangle contained by `AA`,
`CD` has no area. -/
theorem rect_self_left (A C D : Point) : rect A A C D = 0 := by
  have hex : ∃ x, Contain ‖A A‖ ‖C D‖ x := ⟨0, Or.inl ⟨Or.inl (len_self A), rfl⟩⟩
  rcases Classical.epsilon_spec hex with ⟨-, hx⟩ | ⟨P, Q, R, S, hr, hPQ, -, -⟩
  · exact hx
  · exact absurd (eq_of_len_eq_zero (hPQ.trans (len_self A))) hr.1.1.1

/-- The rectangle contained by `AB`, `CC` has no area. -/
theorem rect_self_right (A B C : Point) : rect A B C C = 0 :=
  (rect_comm A B C C).trans (rect_self_left C A B)

/-- The square on `AA` has no area. -/
theorem sq_self (A : Point) : sq A A = 0 :=
  rect_self_left A A A

/-! ## Squares -/

/-- The square `ABCD`, read the other way round from `A`, is the square `ADCB`. -/
theorem Square.reverse (h : Square A B C D) (hp : Parallelogram A B C D) :
    Square A D C B := by
  obtain ⟨h₁, h₂, h₃, hA, hB, hC, hD⟩ := h
  have hAB : A ≠ B := hp.1.1
  have hBC : B ≠ C := hp.2.1
  have hCD : C ≠ D := hp.1.2.1
  have hDA : D ≠ A := hp.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [len_symm A D, len_symm D C]; exact h₃.symm
  · rw [len_symm D C, len_symm C B]; exact h₂.symm
  · rw [len_symm C B, len_symm B A]; exact h₁.symm
  · rw [angle_symm hAB.symm hDA]; exact hA
  · rw [angle_symm hDA.symm hCD]; exact hD
  · rw [angle_symm hCD.symm hBC]; exact hC
  · rw [angle_symm hBC.symm hAB]; exact hB

/-- A square that is a parallelogram is a rectangle: it is right-angled (Definition 22).
A square whose far corners lie on one side of its base is a parallelogram by I.28
(`Prop28.square`). -/
theorem Square.rectangle (h : Square A B C D) (hp : Parallelogram A B C D) :
    Rectangle A B C D :=
  ⟨hp, h.2.2.2⟩

/-- The four sides of the square `ABCD` are equal: `AD`, the side at `A` other than
`AB`, is equal to `AB`. -/
theorem Square.len_eq (h : Square A B C D) : ‖A D‖ = ‖A B‖ := by
  rw [len_symm A D, ← h.2.2.1, ← h.2.1, ← h.1]

end Elements
