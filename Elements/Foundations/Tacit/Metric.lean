import Elements.Foundations.Tacit.Diagram

/-!
# Tacit rules: lengths, angles and areas

Facts about magnitudes that Euclid treats as clear from the definitions: the
line `AB` is the line `BA`, the angle `ABC` is the angle `CBA`, and two
triangles that agree in all their sides and angles have the same area. System
E, §3.5 (Avigad, Dean and Mumma, 2009).
-/

namespace Elements.Tacit

variable {A B C D E F : Point}

/-- A finite straight line with distinct ends has length. (Metric 1) -/
axiom eq_of_len_eq_zero (h : ‖A B‖ = 0) : A = B

/-- The "straight line" from a point to itself has no length. (Metric 1) -/
axiom len_self (A : Point) : ‖A A‖ = 0

/-- The straight line `AB` is the straight line `BA`. (Metric 3) -/
axiom len_symm (A B : Point) : ‖A B‖ = ‖B A‖

/-- The angle `ABC` is the angle `CBA`. (Metric 4) -/
axiom angle_symm (hAB : A ≠ B) (hCB : C ≠ B) : ∠ A B C = ∠ C B A

/-- No angle exceeds two right angles. (Metric 5) -/
axiom angle_le_two_right (A B C : Point) : ∠ A B C ≤ ∟ + ∟

/-- A "triangle" with a repeated corner has no area. (Metric 6) -/
axiom area_degenerate (A B : Point) : △ A A B = 0

/-- The triangle `ABC` is the triangle `CAB`. (Metric 8) -/
axiom area_rotate (A B C : Point) : △ A B C = △ C A B

/-- The triangle `ABC` is the triangle `ACB`. (Metric 8) -/
axiom area_swap (A B C : Point) : △ A B C = △ A C B

/-- Triangles equal in all their sides and angles are equal in area. Euclid
uses this without comment once he has shown two triangles congruent.
(Metric 9) -/
axiom area_congruent (h₁ : ‖A B‖ = ‖D E‖) (h₂ : ‖B C‖ = ‖E F‖) (h₃ : ‖C A‖ = ‖F D‖)
    (h₄ : ∠ A B C = ∠ D E F) (h₅ : ∠ B C A = ∠ E F D) (h₆ : ∠ C A B = ∠ F D E) :
    △ A B C = △ D E F

end Elements.Tacit
