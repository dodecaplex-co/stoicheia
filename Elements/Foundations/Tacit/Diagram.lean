import Elements.Foundations.Tacit.Constructions

/-!
# Tacit rules: what Euclid reads off the figure

Euclid draws a figure and then uses facts that are "obvious from the picture":
that a point lies between two others, that two points are on the same side of a
straight line, that a straight line through the inside of a circle must cut it.
He never states these facts or proves them. These are the diagrammatic inferences
of System E, §3.4 (Avigad, Dean and Mumma, 2009). Each retained assumption is an
axiom: most rules say one thing. Between 1 says four, and was four axioms; two of
them, `between_symm` and `not_between_of_between`, remain, and the other two are proved.
Generalities 2 and Triple incidence 3 are proved in `Elements.Figure.Circles`; Circle 4 is
proved after I.7 in `Elements.BookI.Prop07`; and Circle 1, Circle 2, Circle 3, Points 9 and
Intersection 2 are proved after III.2 in `Elements.BookIII.Prop02`.

In one place we follow LeanEuclid's correction of the published rules:
`circles_meet_of_on_inside_outside` (Intersection rule 4) asks that A be *on*
the first circle. As printed in the paper ("on or inside"), the rule fails for
a small circle lying wholly inside a large one. Our thanks to LeanEuclid's
authors, Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and
Xujie Si, for spotting it.

The following former assumptions are proved in Book Zero:
* `Elements.Figure.RuleBase`: `centre_inside`, `same_side_symm`, `ne_of_between`,
  `on_line_of_between_ends`, `pasch4`, `same_side_refl`, `triple_incidence1`, `pasch3`,
  `inside_not_on`.
* `Elements.Figure.Incidence`: `ne_of_between_ends`, `on_line_of_between`,
  `between_of_between_left`, `between_of_between_right`, `circles_meet_of_on_inside_outside`,
  `line_meets_circle_of_inside`, `not_between_of_between_between`, `same_side_or`,
  `triple_incidence2`, `pasch1`.
-/

namespace Elements.Tacit

variable {A B C D E : Point} {L M N : Line} {α β : Circle}

/-! ## Generalities -/

/-- Two points determine a straight line. (Generalities 1) -/
axiom line_unique (hAB : A ≠ B) (hAL : OnLine A L) (hBL : OnLine B L) (hAM : OnLine A M)
    (hBM : OnLine B M) : L = M

/-! ## Between -/

/-- If B is between A and C, it is between C and A. (Between 1) -/
axiom between_symm (h : Between A B C) : Between C B A

/-- If B is between A and C, then A is not between B and C. (Between 1) -/
axiom not_between_of_between (h : Between A B C) : ¬ Between B A C

/-- Of three different points on a straight line, one is between the other two.
(Between 6) -/
axiom between_cases (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) (hA : OnLine A L)
    (hB : OnLine B L) (hC : OnLine C L) : Between A B C ∨ Between B A C ∨ Between A C B

/-! ## Same side -/

/-- Points on one side of a straight line are not on it. (Same side 3) -/
axiom not_on_line_of_same_side (h : SameSide A B L) : ¬ OnLine A L

/-- Two points on the same side of a straight line as a third point are on the same
side as each other. (Same side 4) -/
axiom same_side_trans (h₁ : SameSide A B L) (h₂ : SameSide A C L) : SameSide B C L

/-! ## Pasch -/

/-- If B is between A and C, A is on L and B is off it, then B and C are
on the same side of L: a straight line that leaves L at A does not cross it
again. (Pasch 2) -/
axiom pasch2 (h : Between A B C) (hA : OnLine A L) (hB : ¬ OnLine B L) : SameSide B C L

/-! ## Triple incidence

Three straight lines through one point A divide the plane into six regions. -/

/-! ## Circles

System E's four rules about circles are all proved: Circle 4 after I.7, and Circle 1,
Circle 2 and Circle 3 after III.2. -/

/-! ## Intersection rules -/

/-- A straight line joining points on opposite sides of L crosses L.
(Intersection 1) -/
axiom lines_meet_of_opposite_sides (h : OppositeSides A B L) (hAM : OnLine A M)
    (hBM : OnLine B M) : LinesMeet L M

/-- If each circle passes through a point inside the other, the circles cut one
another. This is the step Euclid takes for granted in I.1. (Intersection 5) -/
axiom circles_meet (hAα : OnCircle A α) (hBα : InsideCircle B α) (hAβ : InsideCircle A β)
    (hBβ : OnCircle B β) : CirclesMeet α β

end Elements.Tacit
