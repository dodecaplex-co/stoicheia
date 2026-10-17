import Elements.Foundations.Postulates

/-!
# Tacit rules: picking points, and where straight lines and circles cross

Euclid often says "let a point be taken at random", or "from the point C, in
which the circles cut one another", without ever saying why such a point
exists. These rules supply the reasons. They are the construction rules of
System E, §3.3 (Avigad, Dean and Mumma, 2009). Postulates 1, 2 and 3 are the
"lines and circles" rules and Points rule 4, and they live in `Postulates.lean`.

The optional list `avoid` lets a new point be chosen different from any points
already in the figure, as System E's "[distinct from …]" clauses do.

Our reading of these rules owes a great deal to LeanEuclid (Logan Murphy,
Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and Xujie Si, 2024),
whose careful Lean rendering of System E we kept open beside the paper the
whole time. Thank you!
-/

namespace Elements.Tacit

/-! ## Points (System E §3.3) -/

/-- Let a point be taken. (Points 1) -/
axiom exists_point (avoid : List Point) : ∃ A : Point, A ∉ avoid

/-- Let a point be taken on the straight line L. (Points 2) -/
axiom exists_point_on_line (L : Line) (avoid : List Point) :
    ∃ A : Point, OnLine A L ∧ A ∉ avoid

/-- Let a point be taken on L, not on the different straight line M.
(Points 2, with "distinct from M") -/
axiom exists_point_on_line_off_line {L M : Line} (h : L ≠ M) (avoid : List Point) :
    ∃ A : Point, OnLine A L ∧ ¬ OnLine A M ∧ A ∉ avoid

/-- Let a point be taken between B and C. (Points 3) -/
axiom exists_point_between {B C : Point} {L : Line} (hB : OnLine B L) (hC : OnLine C L)
    (hBC : B ≠ C) (avoid : List Point) : ∃ A : Point, OnLine A L ∧ Between B A C ∧ A ∉ avoid

/-- Let a point be taken on the same side of L as B. (Points 5) -/
axiom exists_point_same_side {B : Point} {L : Line} (hB : ¬ OnLine B L) (avoid : List Point) :
    ∃ A : Point, SameSide A B L ∧ A ∉ avoid

/-- Let a point be taken on the other side of L from B. (Points 6) -/
axiom exists_point_opposite_side {B : Point} {L : Line} (hB : ¬ OnLine B L)
    (avoid : List Point) : ∃ A : Point, OppositeSides A B L ∧ A ∉ avoid

/-- Let a point be taken on the circle α. (Points 7) -/
axiom exists_point_on_circle (α : Circle) (avoid : List Point) :
    ∃ A : Point, OnCircle A α ∧ A ∉ avoid

/-- Let a point be taken inside the circle α. (Points 8) -/
axiom exists_point_inside_circle (α : Circle) (avoid : List Point) :
    ∃ A : Point, InsideCircle A α ∧ A ∉ avoid

/-- Let a point be taken outside the circle α. (Points 9) -/
axiom exists_point_outside_circle (α : Circle) (avoid : List Point) :
    ∃ A : Point, OutsideCircle A α ∧ A ∉ avoid

/-! ## Intersections (System E §3.3)

Rules 1, 2, 3, 6 and 7 ("let A be the intersection of …") are immediate from
the meanings of `LinesMeet`, `LineMeetsCircle` and `CirclesMeet`, so only the
rules that say *where* the crossing point lies need stating. -/

/-- A straight line through a point B inside a circle, heading out to a point
C outside it, cuts the circle between B and C. (Intersections 4) -/
axiom line_circle_between {B C : Point} {L : Line} {α : Circle}
    (hB : InsideCircle B α) (hBL : OnLine B L) (hC : OutsideCircle C α) (hCL : OnLine C L) :
    ∃ A : Point, OnCircle A α ∧ OnLine A L ∧ Between B A C

/-- A straight line through a point B inside a circle, produced beyond B
away from C, cuts the circle there. (Intersections 5) -/
axiom line_circle_beyond {B C : Point} {L : Line} {α : Circle}
    (hB : InsideCircle B α) (hBL : OnLine B L) (hCL : OnLine C L) (hCB : C ≠ B) :
    ∃ A : Point, OnCircle A α ∧ OnLine A L ∧ Between A B C

/-- Two circles that cut one another do so on each side of the straight line
through their centres. (Intersections 8) -/
axiom circles_meet_same_side {α β : Circle} {B C D : Point} {L : Line}
    (h : CirclesMeet α β) (hC : Centre C α) (hD : Centre D β) (hCL : OnLine C L)
    (hDL : OnLine D L) (hB : ¬ OnLine B L) :
    ∃ A : Point, OnCircle A α ∧ OnCircle A β ∧ SameSide A B L

/-- The same, on the side away from B. (Intersections 9) -/
axiom circles_meet_opposite_side {α β : Circle} {B C D : Point} {L : Line}
    (h : CirclesMeet α β) (hC : Centre C α) (hD : Centre D β) (hCL : OnLine C L)
    (hDL : OnLine D L) (hB : ¬ OnLine B L) :
    ∃ A : Point, OnCircle A α ∧ OnCircle A β ∧ OppositeSides A B L

end Elements.Tacit
