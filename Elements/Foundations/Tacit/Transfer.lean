import Elements.Foundations.Tacit.Metric

/-!
# Tacit rules: from the figure to magnitudes, and back

"Since `B` lies between `A` and `C`, the whole `AC` is equal to `AB` and `BC`
together" — Euclid moves between the figure and its magnitudes all the time.
These are the transfer inferences of System E, §3.6 (Avigad, Dean and Mumma,
2009). Diagram-angle rule 5 is Postulate 5 itself, and the forward half of
diagram-segment rule 3 is Definition 15.
-/

namespace Elements.Tacit

variable {A B C D : Point} {L M : Line} {α β : Circle}

/-! ## Segments -/

/-- If `B` is between `A` and `C`, then `AB` and `BC` together make up `AC`.
(Diagram-segment 1) -/
axiom len_add_of_between (h : Between A B C) : ‖A B‖ + ‖B C‖ = ‖A C‖

/-- A circle is fixed by its centre and its radius. (Diagram-segment 2) -/
axiom circle_eq (hα : Centre A α) (hβ : Centre A β) (hB : OnCircle B α) (hC : OnCircle C β)
    (h : ‖A B‖ = ‖A C‖) : α = β

/-- A point at the distance of the radius from the centre is on the circle.
(Diagram-segment 3, the half that Definition 15 doesn't give) -/
axiom on_circle_of_len_eq (hA : Centre A α) (hB : OnCircle B α) (h : ‖A C‖ = ‖A B‖) :
    OnCircle C α

/-- A point nearer the centre than the circumference is inside. (Diagram-segment 4) -/
axiom inside_of_len_lt (hA : Centre A α) (hB : OnCircle B α) (h : ‖A C‖ < ‖A B‖) :
    InsideCircle C α

/-- A point inside is nearer the centre than the circumference. (Diagram-segment 4) -/
axiom len_lt_of_inside (hA : Centre A α) (hB : OnCircle B α) (h : InsideCircle C α) :
    ‖A C‖ < ‖A B‖

/-! ## Angles -/

/-- If `C` lies on the ray from `A` through `B`, the angle `BAC` is nothing.
(Diagram-angle 1) -/
axiom angle_eq_zero_of_same_ray (hAB : A ≠ B) (hAC : A ≠ C) (hA : OnLine A L)
    (hB : OnLine B L) (hC : OnLine C L) (h : ¬ Between B A C) : ∠ B A C = 0

/-- If the angle `BAC` is nothing, `C` lies on the ray from `A` through `B`.
(Diagram-angle 1) -/
axiom same_ray_of_angle_eq_zero (hAB : A ≠ B) (hAC : A ≠ C) (hA : OnLine A L)
    (hB : OnLine B L) (h : ∠ B A C = 0) : OnLine C L ∧ ¬ Between B A C

/-- If `D` lies within the angle `BAC`, then `BAC` is made up of `BAD` and `DAC`.
(Diagram-angle 2) -/
axiom angle_add_of_inside (hAL : OnLine A L) (hAM : OnLine A M) (hB : OnLine B L)
    (hC : OnLine C M) (hAB : A ≠ B) (hAC : A ≠ C) (hDL : ¬ OnLine D L) (hDM : ¬ OnLine D M)
    (hLM : L ≠ M) (hBD : SameSide B D M) (hCD : SameSide C D L) :
    ∠ B A C = ∠ B A D + ∠ D A C

/-- If the angle `BAC` is made up of `BAD` and `DAC`, then `D` lies within it.
(Diagram-angle 2) -/
axiom inside_of_angle_add (hAL : OnLine A L) (hAM : OnLine A M) (hB : OnLine B L)
    (hC : OnLine C M) (hAB : A ≠ B) (hAC : A ≠ C) (hDL : ¬ OnLine D L) (hDM : ¬ OnLine D M)
    (hLM : L ≠ M) (h : ∠ B A C = ∠ B A D + ∠ D A C) : SameSide B D M ∧ SameSide C D L

/-- A right angle is equal to the angle adjacent to it. (Diagram-angle 3; the
other half is Definition 10 together with Postulate 4) -/
axiom adjacent_eq_of_right (hA : OnLine A L) (hB : OnLine B L) (h : Between A C B)
    (hD : ¬ OnLine D L) (hright : ∠ A C D = ∟) : ∠ A C D = ∠ D C B

/-- The angle doesn't change if its arms are traced through other points on the
same rays. (Diagram-angle 4) -/
axiom angle_eq_of_same_rays {B' C' : Point} (hAL : OnLine A L) (hB : OnLine B L)
    (hB' : OnLine B' L) (hAM : OnLine A M) (hC : OnLine C M) (hC' : OnLine C' M)
    (hBA : B ≠ A) (hB'A : B' ≠ A) (hCA : C ≠ A) (hC'A : C' ≠ A) (hBB' : ¬ Between B A B')
    (hCC' : ¬ Between C A C') : ∠ B A C = ∠ B' A C'

/-! ## Areas -/

/-- A "triangle" whose corners lie on one line has no area. (Diagram-area 1) -/
axiom area_eq_zero_of_on_line (hA : OnLine A L) (hB : OnLine B L) (hAB : A ≠ B)
    (hC : OnLine C L) : △ A B C = 0

/-- A triangle with no area has its corners on one line. (Diagram-area 1) -/
axiom on_line_of_area_eq_zero (hA : OnLine A L) (hB : OnLine B L) (hAB : A ≠ B)
    (h : △ A B C = 0) : OnLine C L

/-- Cutting a triangle in two from a vertex adds up. (Diagram-area 2) -/
axiom area_add_of_between (hA : OnLine A L) (hB : OnLine B L) (hC : OnLine C L)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hD : ¬ OnLine D L) (h : Between A C B) :
    △ A C D + △ D C B = △ A D B

/-- If `A`, `B` and `C` are different points of a straight line, `D` is off it, and the
triangles `ACD` and `DCB` together make up the triangle `ADB`, then `C` lies between
`A` and `B`. (Diagram-area 2, converse) -/
axiom between_of_area_add (hA : OnLine A L) (hB : OnLine B L) (hC : OnLine C L)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hD : ¬ OnLine D L)
    (h : △ A C D + △ D C B = △ A D B) : Between A C B

end Elements.Tacit
