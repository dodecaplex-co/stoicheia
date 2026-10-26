import Elements.Foundations.Tacit.Diagram

/-!
# Tacit rules: lengths, angles and areas

Facts about magnitudes that Euclid treats as clear from the definitions: the
straight line AB is the straight line BA, the angle ABC is the angle
CBA, and two triangles that agree in all their sides and angles have the same
area. System E, §3.5 (Avigad, Dean and Mumma, 2009).

The following former assumptions are proved in Book Zero:
* `Elements.Figure.RuleBase`: `eq_of_len_eq_zero`.
* `Elements.Figure.AreaRules`: `area_swap`.

One rule here is ours, not System E's: that a circle's radius is not nothing
(`radius_ne_zero`), since every circle is drawn with a distance (Postulate 3).
-/

namespace Elements.Tacit

variable {A B C D E F : Point}

/-- The "straight line" from a point to itself has no length. (Metric 1) -/
axiom len_self (A : Point) : ‖A A‖ = 0

/-- The straight line AB is the straight line BA. (Metric 3) -/
axiom len_symm (A B : Point) : ‖A B‖ = ‖B A‖

/-- The angle ABC is the angle CBA. (Metric 4) -/
axiom angle_symm (hAB : A ≠ B) (hCB : C ≠ B) : ∠ A B C = ∠ C B A

/-- No angle exceeds two right angles. (Metric 5) -/
axiom angle_le_two_right (A B C : Point) : ∠ A B C ≤ ∟ + ∟

/-- A "triangle" with a repeated corner has no area. (Metric 6) -/
axiom area_degenerate (A B : Point) : △ A A B = 0

/-- The triangle ABC is the triangle CAB. (Metric 8) -/
axiom area_rotate (A B C : Point) : △ A B C = △ C A B

/-- Triangles equal in all their sides and angles are equal in area. Euclid
uses this without comment once he has shown two triangles congruent.
(Metric 9) -/
axiom area_congruent (h₁ : ‖A B‖ = ‖D E‖) (h₂ : ‖B C‖ = ‖E F‖) (h₃ : ‖C A‖ = ‖F D‖)
    (h₄ : ∠ A B C = ∠ D E F) (h₅ : ∠ B C A = ∠ E F D) (h₆ : ∠ C A B = ∠ F D E) :
    △ A B C = △ D E F

/-! ## A radius is not nothing (ours)

Euclid draws every circle "with any centre and distance" (Postulate 3), and the plane that
models our words reads a `Circle` as "a circle of positive radius"
(`Elements/Foundations/Words.lean`). System E has no rule of this form: there it follows from
Metric 1, that a length is nothing exactly when its ends are one point, with Generalities 3
and 4, that a centre is inside its circle and an inside point is not on it. Here the half of
Metric 1 that this needs (`eq_of_len_eq_zero`) and Generalities 3 and 4 are theorems of Book
Zero (`Elements.Figure.RuleBase`), so this rule is ours. It says only that a radius is
something, and nothing of how long. -/

/-- A circle's radius is not nothing: the straight line from the centre to a point on the
circle has some length. A rule of our own, not one of System E's: every circle is drawn with
a centre and a distance (Postulate 3). -/
axiom radius_ne_zero {α : Circle} (hA : Centre A α) (hB : OnCircle B α) : ‖A B‖ ≠ 0

end Elements.Tacit
