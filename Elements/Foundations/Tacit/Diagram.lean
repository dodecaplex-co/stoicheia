import Elements.Foundations.Tacit.Constructions

/-!
# Tacit rules: what Euclid reads off the figure

Euclid draws a figure and then uses facts that are "obvious from the picture":
that a point lies between two others, that two points are on the same side of
a line, that a line through the inside of a circle must cut it. He never states
these facts or proves them. These are the diagrammatic inferences of System E,
§3.4 (Avigad, Dean and Mumma, 2009), one axiom for each thing a rule says: most
rules say one thing, and Between 1, which says four, is four axioms.

In one place we follow LeanEuclid's correction of the published rules:
`circles_meet_of_on_inside_outside` (Intersection rule 4) asks that `A` be *on*
the first circle. As printed in the paper ("on or inside"), the rule fails for
a small circle lying wholly inside a large one. Our thanks to LeanEuclid's
authors, Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and
Xujie Si, for spotting it.
-/

namespace Elements.Tacit

variable {A B C D E : Point} {L M N : Line} {α β : Circle}

/-! ## Generalities -/

/-- Two points determine a straight line. (Generalities 1) -/
axiom line_unique (hAB : A ≠ B) (hAL : OnLine A L) (hBL : OnLine B L) (hAM : OnLine A M)
    (hBM : OnLine B M) : L = M

/-- A circle has only one centre. (Generalities 2) -/
axiom centre_unique (hA : Centre A α) (hB : Centre B α) : A = B

/-- The centre of a circle is inside it. (Generalities 3) -/
axiom centre_inside (hA : Centre A α) : InsideCircle A α

/-- A point inside a circle is not on it. (Generalities 4) -/
axiom inside_not_on (hA : InsideCircle A α) : ¬ OnCircle A α

/-! ## Between -/

/-- If `B` is between `A` and `C`, it is between `C` and `A`. (Between 1) -/
axiom between_symm (h : Between A B C) : Between C B A

/-- A point between two others differs from the first. (Between 1) -/
axiom ne_of_between (h : Between A B C) : A ≠ B

/-- The ends of a finite straight line differ. (Between 1) -/
axiom ne_of_between_ends (h : Between A B C) : A ≠ C

/-- If `B` is between `A` and `C`, then `A` is not between `B` and `C`. (Between 1) -/
axiom not_between_of_between (h : Between A B C) : ¬ Between B A C

/-- A straight line through `A` and `B`, with `B` between `A` and `C`, passes
through `C`. (Between 2) -/
axiom on_line_of_between (h : Between A B C) (hA : OnLine A L) (hB : OnLine B L) :
    OnLine C L

/-- A straight line through `A` and `C` passes through every point between them.
(Between 3) -/
axiom on_line_of_between_ends (h : Between A B C) (hA : OnLine A L) (hC : OnLine C L) :
    OnLine B L

/-- If `B` is between `A` and `C`, and `D` is between `A` and `B`, then `D` is between
`A` and `C`. (Between 4) -/
axiom between_of_between_left (h₁ : Between A B C) (h₂ : Between A D B) : Between A D C

/-- If `B` is between `A` and `C`, and `C` is between `B` and `D`, then `B` is between
`A` and `D`. (Between 5) -/
axiom between_of_between_right (h₁ : Between A B C) (h₂ : Between B C D) : Between A B D

/-- Of three different points on a straight line, one is between the other two.
(Between 6) -/
axiom between_cases (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) (hA : OnLine A L)
    (hB : OnLine B L) (hC : OnLine C L) : Between A B C ∨ Between B A C ∨ Between A C B

/-- If `B` is between `A` and `C`, and also between `A` and `D`, then `B` is not
between `C` and `D`: `C` and `D` lie on the same side of `B`. (Between 7) -/
axiom not_between_of_between_between (h₁ : Between A B C) (h₂ : Between A B D) :
    ¬ Between C B D

/-! ## Same side -/

/-- A point off a straight line is on the same side of it as itself. (Same side 1) -/
axiom same_side_refl (h : ¬ OnLine A L) : SameSide A A L

/-- If `A` is on the same side of a straight line as `B`, then `B` is on the same side
as `A`. (Same side 2) -/
axiom same_side_symm (h : SameSide A B L) : SameSide B A L

/-- Points on one side of a line are not on it. (Same side 3) -/
axiom not_on_line_of_same_side (h : SameSide A B L) : ¬ OnLine A L

/-- Two points on the same side of a straight line as a third point are on the same
side as each other. (Same side 4) -/
axiom same_side_trans (h₁ : SameSide A B L) (h₂ : SameSide A C L) : SameSide B C L

/-- A straight line has only two sides. (Same side 5) -/
axiom same_side_or (hA : ¬ OnLine A L) (hB : ¬ OnLine B L) (hC : ¬ OnLine C L)
    (h : ¬ SameSide A B L) : SameSide A C L ∨ SameSide B C L

/-! ## Pasch -/

/-- If `A` and `C` are on the same side of `L`, so is any point between them: if `B` is
between `A` and `C`, then `A` and `B` are on the same side of `L`. (Pasch 1) -/
axiom pasch1 (h : Between A B C) (hAC : SameSide A C L) : SameSide A B L

/-- If `B` is between `A` and `C`, `A` is on `L` and `B` is off it, then `B` and `C` are
on the same side of `L`: a straight line that leaves `L` at `A` does not cross it
again. (Pasch 2) -/
axiom pasch2 (h : Between A B C) (hA : OnLine A L) (hB : ¬ OnLine B L) : SameSide B C L

/-- A line through a point between `A` and `C` separates them. (Pasch 3) -/
axiom pasch3 (h : Between A B C) (hB : OnLine B L) : ¬ SameSide A C L

/-- If two different straight lines `L` and `M` meet at `B`, and `A` and `C` are points
of `M`, different from each other and from `B`, that are not on the same side of
`L`, then `B` is between `A` and `C`. (Pasch 4) -/
axiom pasch4 (hLM : L ≠ M) (hBL : OnLine B L) (hBM : OnLine B M) (hAM : OnLine A M)
    (hCM : OnLine C M) (hAC : A ≠ C) (hAB : A ≠ B) (hCB : C ≠ B) (h : ¬ SameSide A C L) :
    Between A B C

/-! ## Triple incidence

Three straight lines through one point `A` divide the plane into six regions. -/

/-- Take `B` on `L`, `C` on `M` and `D` on `N`, three straight lines through `A`. If `C`
lies within the angle `BAD` (on `D`'s side of `L` and on `B`'s side of `N`), then `B`
and `D` are not on the same side of `M`: the straight line `AC` separates them.
(Triple incidence 1) -/
axiom triple_incidence1 (hAL : OnLine A L) (hAM : OnLine A M) (hAN : OnLine A N)
    (hB : OnLine B L) (hC : OnLine C M) (hD : OnLine D N) (hCD : SameSide C D L)
    (hBC : SameSide B C N) : ¬ SameSide B D M

/-- Take `B` on `L`, `C` on `M` and `D` on `N`, three straight lines through `A`, with
`B` other than `A` and `D` off `M`. If `C` and `D` are on the same side of `L`, and `B`
and `D` are not on the same side of `M`, then `B` and `C` are on the same side of
`N`: `C` lies within the angle `BAD`. (Triple incidence 2) -/
axiom triple_incidence2 (hAL : OnLine A L) (hAM : OnLine A M) (hAN : OnLine A N)
    (hB : OnLine B L) (hC : OnLine C M) (hD : OnLine D N) (hCD : SameSide C D L)
    (hBD : ¬ SameSide B D M) (hDM : ¬ OnLine D M) (hBA : B ≠ A) : SameSide B C N

/-- Take `B` on `L`, `C` on `M` and `D` on `N`, three straight lines through `A`, with
`C` within the angle `BAD` (on `D`'s side of `L` and on `B`'s side of `N`). A point
`E` within the angle `CAD` (on `D`'s side of `M` and on `C`'s side of `N`) is on
`C`'s side of `L`. (Triple incidence 3) -/
axiom triple_incidence3 (hAL : OnLine A L) (hAM : OnLine A M) (hAN : OnLine A N)
    (hB : OnLine B L) (hC : OnLine C M) (hD : OnLine D N) (hCD : SameSide C D L)
    (hBC : SameSide B C N) (hDE : SameSide D E M) (hCE : SameSide C E N) : SameSide C E L

/-! ## Circles -/

/-- A chord through a point inside a circle has that point between its ends.
(Circle 1) -/
axiom between_of_inside_chord (hA : OnLine A L) (hB : OnLine B L) (hC : OnLine C L)
    (hAin : InsideCircle A α) (hBon : OnCircle B α) (hCon : OnCircle C α) (hBC : B ≠ C) :
    Between B A C

/-- A circle is "convex": between two points on or inside it, every point is
inside. (Circle 2) -/
axiom inside_of_between (hA : InsideCircle A α ∨ OnCircle A α)
    (hB : InsideCircle B α ∨ OnCircle B α) (h : Between A C B) : InsideCircle C α

/-- Once a straight line has left a circle, it doesn't come back.
(Circle 3) -/
axiom outside_of_between (hA : InsideCircle A α ∨ OnCircle A α) (hC : ¬ InsideCircle C α)
    (h : Between A C B) : OutsideCircle B α

/-- Two circles cut one another on opposite sides of the line through their
centres. (Circle 4) -/
axiom not_same_side_of_circles_meet (hαβ : α ≠ β) (hCα : OnCircle C α) (hCβ : OnCircle C β)
    (hDα : OnCircle D α) (hDβ : OnCircle D β) (hCD : C ≠ D) (hA : Centre A α)
    (hB : Centre B β) (hAL : OnLine A L) (hBL : OnLine B L) : ¬ SameSide C D L

/-! ## Intersection rules -/

/-- A straight line joining points on opposite sides of `L` crosses `L`.
(Intersection 1) -/
axiom lines_meet_of_opposite_sides (h : OppositeSides A B L) (hAM : OnLine A M)
    (hBM : OnLine B M) : LinesMeet L M

/-- A straight line separating two points of a circle cuts the circle.
(Intersection 2) -/
axiom line_meets_circle_of_opposite_sides (hA : InsideCircle A α ∨ OnCircle A α)
    (hB : InsideCircle B α ∨ OnCircle B α) (h : OppositeSides A B L) : LineMeetsCircle L α

/-- A straight line through a point inside a circle cuts the circle.
(Intersection 3) -/
axiom line_meets_circle_of_inside (hA : InsideCircle A α) (hAL : OnLine A L) :
    LineMeetsCircle L α

/-- Two circles cut one another if the first passes through a point `A` inside the
second, and a point `B` outside the second is inside or on the first. (Intersection
4, in LeanEuclid's corrected form) -/
axiom circles_meet_of_on_inside_outside (hAα : OnCircle A α)
    (hBα : InsideCircle B α ∨ OnCircle B α) (hAβ : InsideCircle A β) (hBβ : OutsideCircle B β) :
    CirclesMeet α β

/-- If each circle passes through a point inside the other, the circles cut one
another. This is the step Euclid takes for granted in I.1. (Intersection 5) -/
axiom circles_meet (hAα : OnCircle A α) (hBα : InsideCircle B α) (hAβ : InsideCircle A β)
    (hBβ : OnCircle B β) : CirclesMeet α β

end Elements.Tacit
