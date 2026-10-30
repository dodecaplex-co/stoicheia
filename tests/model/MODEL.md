# The model behind the axioms

Stoicheia's proofs rest on <!-- count:axioms -->48<!-- /count --> axioms: Postulates 1 to 5, Definition 15, and <!-- count:tacit-rules -->42<!-- /count --> tacit
rules, most of them the rules of System E (Jeremy Avigad, Edward Dean and John Mumma, ["A
formal system for Euclid's *Elements*"](https://doi.org/10.1017/S1755020309990098), 2009).
Lean checks that
every proof follows from them. Checking the proofs does not show that they can all be true
at once. If they could not, every certificate would be worthless, because anything follows
from a contradiction.

This page gives the reasons for thinking they can. It reads the words in the ordinary
plane, goes through the <!-- count:axioms -->48<!-- /count --> axioms one at a time, says why each one holds there, and shows
the numbers from the programs in this folder that test each one against the plane. It
does the same in the hyperbolic plane, where Postulate 5 fails and every other axiom
passes the tests. It ends with [the formal model](#the-formal-model), in which Lean checks
that the ordinary plane satisfies every one of the <!-- count:axioms -->48<!-- /count -->, and with [what the evidence shows,
and what it does not](#what-this-shows-and-what-it-does-not).

## The plane

The words Euclid leaves undefined are `opaque` in Lean
([Words.lean](../../Elements/Foundations/Words.lean)): Lean knows nothing of them but what
the axioms say. So any reading of the words that makes all <!-- count:axioms -->48<!-- /count --> axioms true is a model.
Here is ours.

| Word | In the plane |
|---|---|
| `Point` | a point of the plane |
| `Line` | a whole straight line |
| `Circle` | a circle of positive radius |
| `OnLine A L` | `A` lies on `L` |
| `SameSide A B L` | `A` and `B` lie in one open half-plane of `L` (so neither is on `L`) |
| `Between A B C` | `B` lies on the segment `AC`, strictly inside it (so `A ≠ C`) |
| `OnCircle A α` | `A` is at the radius's distance from the centre |
| `InsideCircle A α` | `A` is nearer the centre than the radius |
| `Centre A α` | `A` is the centre |
| `Magnitude k`, with `0`, `+` and `<` | the real numbers of at least 0, for each kind: length, angle and area |
| `len A B`, written `‖A B‖` | the distance from `A` to `B` |
| `ang A B C`, written `∠ A B C` | the angle between the rays from `B` through `A` and through `C`, in [0, π]; 0 when `A = B` or `C = B` |
| `area A B C`, written `△ A B C` | the area of the triangle, 0 when the corners lie on one straight line |
| `rightAngle`, written `∟` | π/2 |

The words built from these then mean what they should. `OppositeSides A B L` is "in the
two open half-planes", `OutsideCircle` is "farther than the radius", `Collinear` is "on
one straight line", `LinesMeet L M` is "different and crossing", `LineMeetsCircle` and
`CirclesMeet` are "with two points in common" (so a circle meets itself), Definition 10's
`IsRightAngle A B C` says that `BC` makes equal angles with `BA` and with `BA` produced,
`C` being off the line, and a `Triangle` is three points not on one straight line.

Two conventions do quiet work. An angle with a repeated point is 0, and a "triangle" with
its corners on one line has no area. Both make the degenerate cases come out true, and
the section on [the guards](#the-guards-and-the-mutations) shows where the axioms'
hypotheses keep out the cases the conventions cannot fix.

## How the model is checked

The programs take an axiom, build configurations of points, lines and circles, keep those
that satisfy its hypotheses, and check its conclusion. Where the conclusion says that a
point exists, the program constructs one and checks it. The exhaustive and structured
harnesses also run 42 predicates independently as retained derived properties. They
preserve the existing numerical checks and configurations for those laws, but do not
depend on the corresponding declarations remaining in the axiom registry.

- **Exact where it can be.** Points have integer or fraction coordinates, lines are
  integer equations, and a circle is its centre and the square of its radius. So lying on
  a line or a circle, betweenness, sides, equal lengths and "inside" are decided exactly,
  with no rounding. Angles, sums of angles and lengths, and the witnesses for crossing
  points are computed in floating point and compared to within 10⁻⁹.
- **[search.py](search.py)** draws configurations at random, biased hard toward the
  degenerate ones: repeated points, points on the lines and circles already drawn,
  centres, points between and beyond, equal and concentric and touching circles.
- **[derived.py](derived.py)** keeps 42 numerical predicates under names beginning
  `derived.`: one for each of the 41 retired rules, among them Circle 3's
  (`outside_of_between`), proved after III.2 since 24 October 2026, and Circle 1's
  (`between_of_inside_chord`), proved after III.2 since 26 October 2026 (#477); and one
  for Metric 9 (`area_congruent`), still an axiom, kept here before Common Notion 4 for
  figures takes its place among the axioms, as the owner decided on 28 October 2026
  (#517). The exhaustive and structured harnesses run Metric 9 under that name alone, so
  the counts they give it are in the table of derived properties, and its own row has a
  dot for each of them.
- **[exhaustive.py](exhaustive.py)** visits every configuration on small grids for 76
  predicates in all: 34 axiom laws and the 42 retained derived properties, with degenerate
  configurations included.
- **[structured.py](structured.py)** builds the hypotheses of 15 axiom laws and all 42
  retained derived properties on purpose, where chance rarely meets them (three straight
  lines through one point, a right angle, two circles through a common point), over a
  large lattice and over fractions.
- **[mutations.py](mutations.py)** weakens 15 statements on purpose, each by changing a
  hypothesis or a conclusion: fourteen rules, assumed or now proved, and the placement that
  supports superposition (M9). It checks that each weakened statement has a counterexample.
  So the harness can see a false statement when there is one.
- **[grid_check.py](grid_check.py)** and **[angle_check.py](angle_check.py)** are a second
  opinion, written separately: the incidence, order and circle rules exactly on a grid,
  and the angle, area, Postulate 4, Postulate 5 and superposition rules in floating point.
- **[hyperbolic.py](hyperbolic.py)** runs every axiom in the hyperbolic plane
  ([below](#the-hyperbolic-plane)).
- **[run.py](run.py)** runs them all and checks the results, including every retained
  property with its hypotheses met in each exhaustive or structured run. It reports their
  totals apart from the axiom totals. Before the programs run, two checks tie the axiom
  harness to the Lean: [laws.toml](laws.toml) names a law for each axiom, exactly the axioms of
  `Certificate/axioms.lock` and of `facts.json`, and search.py and hyperbolic.py each
  implement exactly those laws; and [lock.sha256](lock.sha256) pins the lock, which holds
  every axiom's exact statement. When an axiom changes, this run fails until the model has
  followed it ([below](#changing-the-axioms)).

These programs were first written for the [read-through of 16 October
2026](../../docs/reports/read-through-01.md), and came into the repository with [brief
0005](../../docs/briefs/0005-astra-review.md), as Astra's outside review asked. On the way
in, angle_check.py lost a path that only worked on one machine, structured.py gained
generators for thirteen axioms whose hypotheses the random search met only rarely, and
run.py and hyperbolic.py are new.

## What the numbers say

<!-- counts:begin -->
Counts from `run.py --full --write` at commit `089badbd8463`, 2026-10-28, Python 3.14.2. Each number is how many configurations met the axiom's hypotheses (for the search, over the three seeds); none of them was a counterexample. A dot means that harness does not enumerate the axiom.

In the plane: **3,593,770** configurations met an axiom's hypotheses (1,223,826 in the search, 1,868,465 exhaustive, 501,479 structured), with no counterexample, and all 15 mutations were caught. In the hyperbolic plane: 503,267 configurations met an axiom's hypotheses; `Postulate5` failed 1,189 times and every other axiom held.

| Axiom | Search, seeds 1-3 | Exhaustive | Structured | Hyperbolic |
|---|--:|--:|--:|--:|
| `Postulate1` | 18,156 | 600 | · | 8,270 |
| `Postulate2` | 25,446 | 600 | · | 4,851 |
| `Postulate3` | 18,204 | 600 | · | 8,445 |
| `Postulate4` | 0 | 1,072 | 14,711 | 5,875 |
| `Postulate5` | 4 | 144,984 | 46,580 | 6,166 met, 1,189 fail |
| `Definition15` | 2,485 | 2,448 | 27,114 | 6,845 |
| `Tacit.add_assoc` | 60,000 | · | · | 20,000 |
| `Tacit.add_comm` | 60,000 | · | · | 20,000 |
| `Tacit.add_zero` | 60,000 | · | · | 20,000 |
| `Tacit.lt_irrefl` | 60,000 | · | · | 20,000 |
| `Tacit.lt_trans` | 5,651 | · | · | 2,635 |
| `Tacit.lt_trichotomy` | 60,000 | · | · | 20,000 |
| `Tacit.not_lt_zero` | 60,000 | · | · | 20,000 |
| `Tacit.add_lt_add_right` | 28,346 | · | · | 9,528 |
| `Tacit.exists_point` | 60,000 | · | · | 20,000 |
| `Tacit.exists_point_on_line` | 60,000 | · | · | 20,000 |
| `Tacit.exists_point_inside_circle` | 60,000 | · | · | 20,000 |
| `Tacit.exists_centre` | 60,000 | · | · | 20,000 |
| `Tacit.line_circle_between` | 2,860 | 44,088 | 44,974 | 3,799 |
| `Tacit.line_circle_beyond` | 7,266 | 80,320 | 57,135 | 9,633 |
| `Tacit.circles_meet_same_side` | 381 | 216,488 | 40,033 | 8,929 |
| `Tacit.line_unique` | 17,462 | 600 | · | 1,948 |
| `Tacit.between_symm` | 4,808 | 304 | · | 11,386 |
| `Tacit.not_between_of_between` | 4,812 | 304 | · | 11,444 |
| `Tacit.between_cases` | 16,420 | 912 | · | 2,154 |
| `Tacit.not_on_line_of_same_side` | 315 | 45,192 | · | 4,389 |
| `Tacit.same_side_trans` | 211 | 724,792 | 33,327 | 5,113 |
| `Tacit.pasch2` | 318 | 3,872 | 8,435 | 1,401 |
| `Tacit.lines_meet_of_opposite_sides` | 16 | 26,248 | 39,362 | 4,505 |
| `Tacit.circles_meet` | 1,377 | 10,668 | 1,587 | 2,528 |
| `Tacit.len_self` | 60,000 | 25 | · | 20,000 |
| `Tacit.len_symm` | 60,000 | 625 | · | 20,000 |
| `Tacit.radius_ne_zero` | 6,413 | · | · | 11,369 |
| `Tacit.angle_symm` | 15,578 | 14,400 | · | 6,967 |
| `Tacit.angle_le_two_right` | 60,000 | 15,625 | · | 20,000 |
| `Tacit.area_degenerate` | 60,000 | 625 | · | 20,000 |
| `Tacit.area_rotate` | 60,000 | 15,625 | · | 20,000 |
| `Tacit.area_congruent` | 54,696 | · | · | 10,711 |
| `Tacit.len_add_of_between` | 4,707 | 304 | · | 9,920 |
| `Tacit.circle_eq` | 791 | 2,448 | 27,089 | 4,410 |
| `Tacit.angle_eq_zero_of_same_ray` | 14,978 | 1,208 | · | 2,790 |
| `Tacit.same_ray_of_angle_eq_zero` | 15,256 | 1,208 | · | 2,734 |
| `Tacit.angle_add_of_inside` | 4 | 77,960 | 24,987 | 3,814 |
| `Tacit.angle_eq_of_same_rays` | 6,985 | 60,032 | 8,676 | 4,145 |
| `Tacit.area_eq_zero_of_on_line` | 24,842 | 2,112 | · | 4,672 |
| `Tacit.on_line_of_area_eq_zero` | 24,904 | 2,112 | · | 4,702 |
| `Tacit.area_add_of_between` | 25 | 6,176 | 55,499 | 8,532 |
| `Tacit.superposition` | 109 | 363,888 | 71,970 | 8,657 |

Separately, **10,365,519** configurations met a retained derived property's hypotheses, with no counterexample. These do not count toward the axiom totals.

| Derived property | Exhaustive | Structured |
|---|--:|--:|
| `derived.adjacent_eq_of_right` | 1,072 | 25,166 |
| `derived.not_same_side_of_circles_meet` | 1,704 | 939 |
| `derived.centre_unique` | 72 | 4,142 |
| `derived.inside_of_between` | 76,104 | 39,272 |
| `derived.outside_of_between` | 281,664 | 47,802 |
| `derived.between_of_inside_chord` | 3,228 | 37,732 |
| `derived.area_congruent` | 375,479 | 94,050 |
| `derived.exists_point_outside_circle` | 72 | 100,000 |
| `derived.line_meets_circle_of_opposite_sides` | 6,161,192 | 58,077 |
| `derived.triple_incidence3` | 315,152 | 1,246 |
| `derived.inside_of_angle_add` | 77,960 | 25,019 |
| `derived.area_swap` | 15,625 | 100,000 |
| `derived.between_of_area_add` | 6,176 | 56,023 |
| `derived.between_of_between_left` | 128 | 36,856 |
| `derived.between_of_between_right` | 128 | 43,514 |
| `derived.centre_inside` | 72 | 20,150 |
| `derived.circles_meet_of_on_inside_outside` | 49,616 | 358 |
| `derived.circles_meet_opposite_side` | 216,488 | 40,177 |
| `derived.eq_of_len_eq_zero` | 25 | 43,929 |
| `derived.exists_point_between` | 600 | 72,507 |
| `derived.exists_point_on_circle` | 72 | 100,000 |
| `derived.exists_point_on_line_off_line` | 19,460 | 89,876 |
| `derived.exists_point_opposite_side` | 3,160 | 89,623 |
| `derived.exists_point_same_side` | 3,160 | 89,521 |
| `derived.inside_not_on` | 1,260 | 39,905 |
| `derived.inside_of_len_lt` | 5,776 | 19,704 |
| `derived.len_lt_of_inside` | 5,776 | 19,736 |
| `derived.line_meets_circle_of_inside` | 30,204 | 69,874 |
| `derived.ne_of_between` | 304 | 99,883 |
| `derived.ne_of_between_ends` | 304 | 99,885 |
| `derived.not_between_of_between_between` | 560 | 48,699 |
| `derived.on_circle_of_len_eq` | 2,448 | 27,123 |
| `derived.on_line_of_between` | 304 | 7,215 |
| `derived.on_line_of_between_ends` | 304 | 7,275 |
| `derived.pasch1` | 17,160 | 28,583 |
| `derived.pasch3` | 3,856 | 15,576 |
| `derived.pasch4` | 3,552 | 20,921 |
| `derived.same_side_or` | 595,104 | 14,059 |
| `derived.same_side_refl` | 3,160 | 80,714 |
| `derived.same_side_symm` | 45,192 | 54,827 |
| `derived.triple_incidence1` | 77,960 | 7,925 |
| `derived.triple_incidence2` | 77,960 | 8,043 |
<!-- counts:end -->

The full output of each program, headed with the commit, the seeds and the Python that
produced it, is in [results/](results/), and [results/summary.txt](results/summary.txt)
has the same table in plain text.

## The axioms one by one

Each axiom below has what it says in the plane and why it holds there, degenerate cases
included. These short arguments are the reason the axioms are true in the plane; the
numbers above are evidence that the arguments, and the axioms as written in Lean, say
the same thing. A few axioms the programs reach only in part, and there the argument
carries the weight:

- **the magnitude laws**, which the programs check on sample values, while the argument
  covers every non-negative real;
- **the `avoid` lists** of Postulate 2 and the Points rules, which ask for a new point
  outside any finite list: a program can show a few witnesses, and the argument shows
  infinitely many;
- **the crossing points** of lines and circles, which are irrational in general, so the
  programs find them in floating point; the argument finds them by continuity.

Every other axiom's hypotheses are met, exactly, thousands of times or more.

Names are those in `Elements.Tacit` unless they are postulates or Definition 15.

Forty-one former axioms are now theorems with the same names and types. Eight were
retired first: `adjacent_eq_of_right`, `not_same_side_of_circles_meet`, `centre_unique`,
`inside_of_between`, `exists_point_outside_circle`, `line_meets_circle_of_opposite_sides`,
`triple_incidence3` and `inside_of_angle_add`. Thirty-one followed on 19 October 2026:
`exists_point_on_line_off_line`, `exists_point_between`, `exists_point_same_side`,
`exists_point_opposite_side`, `exists_point_on_circle`, `circles_meet_opposite_side`,
`centre_inside`, `inside_not_on`, `ne_of_between`, `ne_of_between_ends`,
`on_line_of_between`, `on_line_of_between_ends`, `between_of_between_left`,
`between_of_between_right`, `not_between_of_between_between`, `same_side_refl`,
`same_side_symm`, `same_side_or`, `pasch1`, `pasch3`, `pasch4`, `triple_incidence1`,
`triple_incidence2`, `line_meets_circle_of_inside`, `circles_meet_of_on_inside_outside`,
`eq_of_len_eq_zero`, `area_swap`, `on_circle_of_len_eq`, `inside_of_len_lt`,
`len_lt_of_inside` and `between_of_area_add`. Circle 3, `outside_of_between`, followed on
24 October 2026, proved after III.2, and Circle 1, `between_of_inside_chord`, on 26 October
2026, proved after III.2 too. Their numerical configurations remain in
[derived.py](derived.py), reported separately from the locked axioms.

### The postulates and Definition 15

| Axiom | In the plane | Why it holds |
|---|---|---|
| `Postulate1` | two different points lie on a line | Two different points determine a straight line. |
| `Postulate2` | a segment `BC` on `L` can be produced beyond `C` to a point outside any finite list | The points `C + t (C − B)` with `t > 0` lie on `L` with `C` strictly between `B` and them. There are infinitely many, so one is outside the list. |
| `Postulate3` | a circle with centre `A` through `B ≠ A` | Its radius is the distance from `A` to `B`, which is positive. |
| `Postulate4` | every right angle in Definition 10's sense is π/2 | `B` is strictly between `A` and `D`, so the rays from `B` through `A` and through `D` are opposite, and `∠ A B C + ∠ C B D = π`. The two angles are equal, so each is π/2. Definition 10's `¬ Collinear A B C` is what makes this true: with `C` at `B` both angles would be 0. |
| `Postulate5` | with `A`, `D` on one side of the line `BC`, and `∠ A B C + ∠ B C D < π`, the lines `AB` and `CD` meet on that side | Put `B` at the origin and `C` at `(c, 0)` with `c > 0`, and `A`, `D` above the axis. Call the angles at `B` and `C` α and β, both between 0 and π. The ray from `B` toward `A` and the ray from `C` toward `D` meet at height `c sin α sin β / sin(α + β)`, which is positive because `0 < α + β < π`. |
| `Definition15` | two radii of a circle are equal | Every point on the circle is at the radius's distance from the centre. |

### Magnitudes

Each kind of magnitude is the real numbers of at least 0, with their own `0`, `+` and `<`.

| Axiom | Why it holds |
|---|---|
| `add_assoc`, `add_comm`, `add_zero` | Addition of reals. |
| `lt_irrefl`, `lt_trans`, `lt_trichotomy` | The order of the reals. |
| `not_lt_zero` | Nothing at least 0 is less than 0. This is why magnitudes are the non-negative reals and not all of them. |
| `add_lt_add_right` | If `a < b` then `a + c < b + c`. |

### Taking points, and where lines and circles cross

| Axiom | In the plane | Why it holds |
|---|---|---|
| `exists_point` | a point outside any finite list | The plane has infinitely many points. |
| `exists_point_on_line` | a point of `L` outside the list | A line has infinitely many points. |
| `exists_point_inside_circle` | a point inside `α` | The open disc is infinite. |
| `exists_centre` | every circle has a centre | A circle of the plane is its centre and a radius; its centre is the witness. |
| `line_circle_between` | a line from a point `B` inside to a point `C` outside crosses the circle between them | Along the segment the distance from the centre is continuous, less than the radius at `B` and more at `C`, so it equals the radius somewhere strictly between. |
| `line_circle_beyond` | a line through `B` inside, produced beyond `B` away from `C`, crosses the circle there | Going from `B` away from `C`, the distance from the centre grows without bound, so it passes the radius at a point `A` with `B` between `A` and `C`. |
| `circles_meet_same_side` | two circles that cut, with centres on `L`, cut on each side of `L` | If the circles differ, their centres differ (concentric circles that differ share no point), `L` is the line of centres, and the two common points are mirror images in it, off it, one on each side. If the circles are the same, `L` is any line through the centre, and the circle reaches both sides. |

`exists_centre` is a rule of our own, not System E's
([brief 0008](../../docs/briefs/0008-centre.md)): Euclid's definition of a circle gives it a
centre (Definitions I.15 and I.16), while System E lets a circle be given without one. In
the hyperbolic plane too a circle is its centre and a radius, and its centre is the witness.
That the rule does not follow from the other laws is Astra's argument, and we are grateful
for it: add to the plane one more circle, with the circumference and the interior of an
ordinary circle and no point its centre. The laws that speak of a circle's centre never apply
to it, `circle_eq` cannot make it the ordinary circle, and every other law holds of it as of
that circle, so the others hold and `exists_centre` fails. It is an informal countermodel
argument, not one checked in Lean. The rule has no guard to drop, so no mutation goes with
it.

### Generalities

| Axiom | Why it holds |
|---|---|
| `line_unique` | Two different points lie on only one line. |

### Between

Give the line through `A` and `C` a coordinate. Then `Between A B C` says that `B`'s
coordinate lies strictly between theirs, and every rule here is a fact about three or four
real numbers.

| Axiom | Why it holds |
|---|---|
| `between_symm` | Strictly between `a` and `c` is strictly between `c` and `a`. |
| `not_between_of_between` | If `b` is between `a` and `c`, then `a` is outside the interval from `b` to `c`. |
| `between_cases` | Of three different numbers, one lies between the other two. |

### Same side and Pasch

Write `L` as `f = 0` for an affine function `f`, such as `ax + by + c`. Then
`SameSide A B L` says `f(A) f(B) > 0`, and along a segment `f` changes linearly:
`f(B) = (1 − t) f(A) + t f(C)` when `B = A + t (C − A)`.

| Axiom | Why it holds |
|---|---|
| `not_on_line_of_same_side` | A positive product has no zero factor. |
| `same_side_trans` | The signs of `f(B)` and `f(C)` both equal that of `f(A)`. |
| `pasch2` | With `f(A) = 0`, `f(B) = t f(C)` with `t > 0`, and `f(B) ≠ 0`. |

### Triple incidence

Three different lines through one point `A` cut the plane into six angles. In each rule
the side conditions force the points other than `A` to be off the lines named, so the
lines are different and the points are not `A`.

All three rules are now theorems, tested as derived properties.

### Circles

Circle 1, Circle 2 and Circle 3 are now theorems, proved after III.2, and tested as derived
properties. In the plane, Circle 1 (`between_of_inside_chord`) holds because a line meets a
circle at most twice, so `B` and `C` are those two points; the points of the line inside the
circle are exactly the open chord between them, and `A` is one. Circle 3
(`outside_of_between`) holds because, were `B` inside or on the circle, `C`, strictly
between `A` and `B`, would be inside by strict convexity of the disc.

### Intersections

| Axiom | Why it holds |
|---|---|
| `lines_meet_of_opposite_sides` | `f` changes sign along the segment `AB`, so it is 0 somewhere on it: `M` (through `A` and `B`) meets `L`, and differs from it because `A` is off `L`. |
| `circles_meet` | With `d` the distance between the centres and `r`, `s` the radii: `A` on `α` and inside `β` gives `|r − d| < s`, and `B` on `β` and inside `α` gives `|s − d| < r`. Together, `|r − s| < d < r + s`, which is exactly when two circles cut in two points (and rules out `d = 0`). |

### Lengths, angles and areas

| Axiom | Why it holds |
|---|---|
| `len_self` | The distance from a point to itself is 0. |
| `len_symm` | Distance is symmetric. |
| `radius_ne_zero` | A circle of the plane has a positive radius, and a point on it is at that distance from the centre, so it is some distance away. |
| `angle_symm` | The angle between two rays does not depend on their order (and the convention keeps it so even with a repeated point). |
| `angle_le_two_right` | Angles lie in [0, π], and π is `∟ + ∟`. |
| `area_degenerate` | A triangle with a repeated corner has no area. |
| `area_rotate` | The area of a triangle does not depend on which corner is named first. |
| `area_congruent` | The three sides fix the area (Heron's formula), so the angle hypotheses are more than the plane needs. |

`radius_ne_zero` is a rule of our own, not System E's, joined by the owner's decision of 25
October 2026 ([#473](https://github.com/jackChallis/stoicheia/issues/473)): every circle
Euclid draws has a centre and a distance (Postulate 3), so its radius is something. In the
hyperbolic plane too a circle is drawn about its centre through another point, and so has a
positive radius. When it joined, the other laws gave it already: Book Zero proved the same
statement from Circle 1 and `circle_eq` (`RuleProofs.Circle.radius_ne_zero`, in
[RuleBase.lean](../../Elements/Figure/RuleBase.lean)). It was assumed so that Book Zero's
positive lengths could rest on it in their place, and so on neither of those rules (#473).

### From the figure to magnitudes, and back

| Axiom | Why it holds |
|---|---|
| `len_add_of_between` | On a segment, the parts add up to the whole. |
| `circle_eq` | A circle is fixed by its centre and its radius. |
| `angle_eq_zero_of_same_ray` | `B` and `C` are on `L`, different from `A`, and `A` is not between them, so they are on one ray from `A`, and the angle is 0. |
| `same_ray_of_angle_eq_zero` | An angle of 0 between rays from `A` makes them one ray, so `C` is on `L` and `A` is not between `B` and `C`. |
| `angle_add_of_inside` | `L ≠ M`, so the angle `BAC` is less than two right angles, and `D`, on `B`'s side of `M` and `C`'s side of `L`, is inside it. A ray inside an angle splits it into two that add up. |
| `angle_eq_of_same_rays` | `B'` is on the ray from `A` through `B`, and `C'` on the ray through `C`, so the rays, and the angle, are the same. |
| `area_eq_zero_of_on_line` | Corners on one line make no area. |
| `on_line_of_area_eq_zero` | With `A ≠ B`, no area means `C` is on the line `AB`. |
| `area_add_of_between` | The triangles `ACD` and `DCB` have the same height from `D`, and their bases `AC` and `CB` add up to `AB`. |

### Superposition

| Axiom | Why it holds |
|---|---|
| `superposition` | Move the plane rigidly, taking `A` to `D` and the ray from `A` through `B` onto the ray from `D` through `G`, and reflect in `L` if `C` lands on the side away from `H`. Rigid motions keep lengths and angles. `B'` lies on the ray, so `D` is not between `B'` and `G`. The triangle guard puts the image of `C` off `L`, so it can be placed on `H`'s side as `C'`. Same side 3 then puts `C'` off `L`; since `D` is on `L`, `D ≠ C'`, and Postulate 1 draws their straight line for the kept side. `Rule.of_placement_of_join` states this reduction, through `Rule.of_placement`. The numerical harness checks the sufficient construction; the formal model proves the reduction and the construction in Lean. The harness's check of the kept side is a construction smoke test: it confirms that the harness builds the line, but it cannot fail on its own, since the line is drawn through `D` and `C'`, and `D ≠ C'` already follows from the check that `C'` is on `H`'s side of `L`. No mutation targets it. |

## The guards and the mutations

Many rules, assumed or proved, carry a guard that looks fussy: a point must be different from another, two
lines or circles must differ, a point must be strictly inside. The mutation test changes a
hypothesis or conclusion in fifteen cases and finds a counterexample in each. Fourteen
concern rules, assumed or now proved; M9 concerns the supporting placement construction for
superposition. It tests why that construction requires a triangle, not whether the restricted derivation calculus
fails without that guard.

| Mutation | What goes wrong |
|---|---|
| `circles_meet_of_on_inside_outside` with `A` on or inside `α` | a small circle wholly inside a large one (the form printed in System E) |
| `triple_incidence2` without `D` off `M` | `D` on `M` |
| `triple_incidence2` without `B ≠ A` | `B` at `A` |
| `not_same_side_of_circles_meet` without `α ≠ β` | two points of one circle on one side |
| `inside_of_angle_add` without `L ≠ M` | `B` and `C` on one ray |
| `Postulate5` concluding the other side | the lines meet on the side of the small angles, not the other |
| `pasch4` without `L ≠ M` | `A`, `B`, `C` all on `L`, in any order |
| `between_of_inside_chord` with `A` on or inside | `A` at `B` |
| The supporting superposition placement for a flat triangle (M9) | no point off `L` at the right distances; this tests the placement, not the derivation calculus |
| Definition 10 without `¬ Collinear A B C` | `C` at `B`, both angles 0, and Postulate 4 false |
| `line_circle_beyond` without `C ≠ B` | with `C` at `B`, no point `A` has `B` strictly between `A` and `B` |
| `circles_meet_same_side` without `B` off `L` | no point is on the same side as a point of `L` |
| `angle_eq_of_same_rays` with opposite rays | the angle becomes its supplement |
| `circles_meet` with `B` on or inside `α` | circles that only touch |
| `line_meets_circle_of_opposite_sides` with the same side | a line that misses the circle |

## The hyperbolic plane

The book's certificates say which proofs use Postulate 5. They do not say, by themselves,
that the other <!-- count:axioms-but-postulate-5 -->47<!-- /count --> axioms could not do its work in disguise: a proof avoiding the named
Postulate 5 might still lean on some other rule just as strong. Astra's review asked for
the way to settle that, a model of the other axioms in which Postulate 5 fails, and
[hyperbolic.py](hyperbolic.py) tests such a model numerically, which supports the answer
without settling it.

It reads the words in the Beltrami-Klein picture of the hyperbolic plane, after Eugenio
Beltrami (1868) and Felix Klein (1871). Robin Hartshorne gives non-Euclidean geometry a
chapter of his [*Geometry: Euclid and Beyond*](../../docs/reading.md#hartshorne2000geometry),
and it is a fine place to meet the hyperbolic plane. Here is the reading:

| Word | In the hyperbolic plane |
|---|---|
| `Point` | a point of the open unit disc (with fraction coordinates in the program) |
| `Line` | a chord: the part of a straight line inside the disc |
| `OnLine`, `Between`, `SameSide` | as in the plane, inside the disc |
| `len` | hyperbolic distance: `cosh² d(P, Q) = (1 − P·Q)² / ((1 − |P|²)(1 − |Q|²))` |
| `Circle`, `OnCircle`, `InsideCircle`, `Centre` | the points at a fixed hyperbolic distance from a centre, and nearer; in this picture, ellipses |
| `ang` | the hyperbolic angle, measured on the hyperboloid; 0 with a repeated point |
| `area` | the angle defect, π minus the angle sum; 0 for corners on one line |
| `rightAngle` | π/2 |

`cosh² d` is a fraction when the points are, so lengths, circles and "inside" are decided
exactly, and so are right angles and equal angles. Before it starts, the program checks
itself: the hyperbolic law of cosines ties its distances to its angles, mirror images
keep lengths and angles exactly, lines through a line's pole cross it at right angles,
and every triangle's angles add up to less than two right angles.

**What it finds.** Postulate 5 fails, often (the numbers are [above](#what-the-numbers-say)):
two chords can make interior angles less than two right angles with a third and never
meet inside the disc. Every other axiom passes, with no counterexample. That is what the
hand arguments lead one to expect. The incidence and order rules are the plane's,
restricted to the open disc, which is convex. Hyperbolic circles are convex and cross as
plane circles do. Angles at a point add and are supplementary as in the plane, so a right
angle is π/2. The defect adds up when a triangle is cut from a vertex, because the two
angles at the cut make π, and it is kept by every motion and positive for every true
triangle. And the hyperbolic plane's motions can lay any triangle down at any point,
along any ray, on either side. The harness also constructs and checks the straight line
through the starting point and placed third corner, the kept side. These are numerical
tests of the sufficient placement for the restricted rule, by `Rule.of_placement`;
there is no Lean proof of the hyperbolic model here. As in the plane
([above](#superposition)), the check of the kept side is a construction smoke test: it
cannot fail on its own, since the line is drawn through the starting point and the placed
third corner, and that corner is checked to lie strictly on the chosen side of the line
the triangle is laid along, so is not the starting point, which is on that line; and no
mutation targets it. Marvin Jay Greenberg's
[*Euclidean and Non-Euclidean Geometries*](../../docs/reading.md#greenberg2008euclidean)
tells this story in full, models and all.

**What it shows.** It supports, numerically, that none of the other <!-- count:axioms-but-postulate-5 -->47<!-- /count --> axioms carries the
parallel postulate in disguise. If every one of them does hold in the hyperbolic plane,
as the hand arguments say, then whatever follows from them without Postulate 5 is true
there, and a statement that fails there, such as I.32's "the three interior angles of the
triangle are equal to two right angles", cannot be proved from them alone. The numbers do
not establish that non-derivability: a test can find a counterexample, but it cannot show
that none exists, so the conclusion waits on a proof that the hyperbolic reading
satisfies every other law, planned after the Euclidean model
([below](#the-formal-model)). Whether a particular proposition's statement fails
there is a question about that proposition, so the pages keep saying "this proof uses
Postulate 5", and an independence claim on any page should name this evidence and say
that it is numerical. No axiom is marked as Euclidean beyond Postulate 5, and nothing in
this run suggests that one should be.

## The formal model

The evidence above is strong, but it is not a proof. The proof is a Lean model of the
axioms, begun on 18 October 2026
([#73](https://github.com/jackChallis/stoicheia/issues/73)) in a separate package,
[`model/`](../../model/README.md): a Lake package of its own in this repository, with a
pinned Mathlib, built by CI's `formal-model` job. Stoicheia itself stays plain Lean:
nothing in the main library imports the model. One repository keeps the laws, their
reading in the plane and the proofs that the reading satisfies them at a single revision,
as Astra advised, with our thanks. The model has four parts.

1. **The words as a signature.** In the library the 17 words are `opaque` constants and
   the axioms are `axiom`s about them, so nothing can be plugged in for them. The model
   states the same words as the fields of a Lean structure, `Signature`, the carriers of
   the magnitudes with their zero, addition and order among them, and the laws as a
   proposition about any such structure, `Laws`, with Postulate 5 apart from the other
   <!-- count:axioms-but-postulate-5 -->47<!-- /count -->. A Lean program generates the laws from the elaborated declarations themselves, not
   from their printed text, and every build checks the translation: taken back to the
   library's words, each law is compared with the library's declaration, by the kernel
   and expression by expression. The four pure modules
   `Elements.Foundations.Superposition.Syntax`, `.Semantics`, `.Soundness` and
   `.Restriction` are shared by identity, preserving universe arguments. The generator
   audits every declaration in those modules through types, values, proofs, constructors
   and recursor rules: no geometric word, project axiom or `sorryAx` may be reached.
   Other unsupported project or foreign constants are rejected. The library's
   `primitives` is an ordinary generated interpretation over the signature.
2. **The plane, with Mathlib.** The package reads the words as [the plane](#the-plane)
   above does: points as `EuclideanSpace ℝ (Fin 2)`, lines as its one-dimensional affine
   subspaces, circles as spheres of positive radius, magnitudes as `ℝ≥0`, length as
   distance, the area by a determinant, and `∟` as π/2. One care: Mathlib's unoriented
   angle is π/2 when a point is repeated, and our reading needs 0 there, so the plane's
   angle is Mathlib's only when both arms are nonzero.
3. **Every law of the lock proved in the plane**, degenerate cases included: all <!-- count:axioms -->48<!-- /count -->, each
   a theorem of its own. The hardest were taken first, since they might have reshaped the
   representation: where circles meet, and on which side; angle addition, both ways; the
   side on which Postulate 5's lines meet; restricted superposition, from placement by
   isometry and reflection, Same side 3, Postulate 1 and `Rule.of_placement_of_join`; the area
   rules; and the finite `avoid` lists. `superposition_placement` proves the supporting
   placement construction; it is not a second locked law. The generator gathers the <!-- count:axioms -->48<!-- /count --> into
   `euclidean_laws`, which says that the plane satisfies `Laws`, with no hypothesis left,
   and `model_exists : ∃ S : Signature, Laws S` follows. Every build checks that nothing
   in the model imports an `Elements` module other than the four pure ones, retains the
   unknown-`Elements.Point` sentinel, and checks that beneath each of these proofs lie only
   Lean's own axioms, `propext`, `Classical.choice` and `Quot.sound`: no axiom of the
   project and no `sorryAx`.
4. **The lock's hash tying them.** [model/lock.sha256](../../model/lock.sha256) holds the
   hash of `Certificate/axioms.lock`, as [lock.sha256](lock.sha256) does here, and the
   model's build fails unless it is the lock's. So any change to the lock fails that
   build until the model is brought to it, and a change to an axiom, or to a word an
   axiom reaches, sends someone back to the translation and to the proofs of the laws
   that changed.

So Lean checks that the ordinary Euclidean plane satisfies every law in this revision's
foundations. This establishes a model relative to Lean's logical foundations and
Mathlib's construction of the real numbers. It does not establish that every formal
statement captures Euclid's intended meaning. Nor does it settle the independence of
Postulate 5: a hyperbolic instance of every law but Postulate 5, with Postulate 5 proved
false there, planned after the Euclidean one, would make that a theorem too. How the
package is built, and how each check works, is in its [README](../../model/README.md).

## What this shows, and what it does not

- **The consistency of the axioms is a theorem,** relative to Lean's logic and Mathlib's
  construction of the real numbers: Lean checks, in [the formal model](#the-formal-model),
  that the ordinary plane satisfies every locked law
  ([#73](https://github.com/jackChallis/stoicheia/issues/73)). So the axioms cannot
  contradict one another unless those foundations do.
- **The interpretation** is the reading of the words above, with a short argument for
  each of the <!-- count:axioms -->48<!-- /count --> axioms and many configurations tested against each, exactly wherever
  the coordinates allow. The formal model makes the same reading in Lean and proves each
  law there, so that the axioms can all be true together no longer rests on these
  arguments and tests alone.
- **It depends on** the 17 words staying `opaque`, which `scripts/check_fidelity.py`
  checks, and on the axioms being the ones this page and the formal model were checked
  against, which [lock.sha256](lock.sha256) and
  [model/lock.sha256](../../model/lock.sha256) pin.
- **Non-derivability is not proved.** That the other <!-- count:axioms-but-postulate-5 -->47<!-- /count --> axioms cannot give Postulate 5,
  and that a statement failing in the hyperbolic plane cannot be proved without it, rest
  on the numerical hyperbolic check [above](#the-hyperbolic-plane) until a hyperbolic
  model is built in Lean. A test can find a counterexample but cannot show that there is
  none, so numerical tests establish neither consistency nor non-derivability.
- **It does not show** that the Lean statements say what Euclid meant: that is the work
  of the review records and the gap catalogues. The formal model shows that the laws have
  a model, not that a formal statement captures Euclid's intended meaning, nor that a
  word the propositions use, such as `rect` or `circumference`, means in the plane what
  Euclid means.

## Changing the axioms

Adding, removing or restating an axiom is the owner's decision, recorded in a decision
entry of its own in [`docs/decisions/`](../../docs/decisions/README.md), as the earlier
ones are on the [decisions page](../../docs/briefs/0002-decisions.md). Once it is made,
the model follows the axiom in the same pull request as the Lean:

1. **The lock.** `python3 scripts/check_fidelity.py --write-lock` writes
   `Certificate/axioms.lock` from the new `facts.json`, and
   `shasum -a 256 Certificate/axioms.lock`, run from the repository's root, gives the
   line for [lock.sha256](lock.sha256).
2. **The law's name.** [laws.toml](laws.toml) gains, loses or keeps the axiom's line: its
   name as the lock gives it, then its law's name in the harness. An axiom that must fail
   in the hyperbolic plane, as Postulate 5 does, is also listed under `fails`.
3. **The law.** [search.py](search.py) and [hyperbolic.py](hyperbolic.py) each implement
   every law, so each gains, loses or changes it, written as every law there is: a
   function `_` under `@axiom('<name>', …)`. The laws that stay keep their order. Its
   helpers go inside it, and it keeps to itself, by an allow-list collected from the laws
   (`LAW_GLOBALS` and the lists beside it in
   [safe_push.py](../../scripts/safe_push.py)): it uses its own parameters and the names
   it binds; the helpers of its program that the laws already call, the builtins, `math`
   functions, table and value they use (hyperbolic.py's `SEEDS`, read through a subscript;
   search.py's `RA`), each in the role they use it in; the random numbers it is handed,
   drawn and never reseeded; and plain syntax: assignments, `if`, `for`, `while`, `return`,
   arithmetic, comparisons, comprehensions and functions of its own, with no import,
   `global`, `lambda`, `try`, `with`, class or default argument. And it changes no
   container but one it made in its own body (`ws = []`, then `ws.append(w)`), and that
   through the name it gave it: never through a second name for a container it did not
   make, nor through an element of its own (`x[0] += [1]`). The pre-flight's check
   (`self_contained`) reads the law's code, does not run it, and refuses whatever the list
   does not name, so reflection has no way in. A law still shares the random numbers with
   the laws after it, and how many it draws moves which configurations they see, never
   what they check. A law that needs what the list lacks, a new helper say, waits for a
   pull request of its own that adds the helper and widens the list. The other programs
   check some laws only. A law added reaches them later, in a pull request of its own. But
   `structured.py` and `exhaustive.py` run some laws by name on configurations of their
   own (`run('<law>', ...)`). If either program names the law of an axiom that is removed,
   or restated so that its law reads other letters, that program must drop or re-key the
   law first, in a pull request of its own, before the axiom moves. That preparation is
   already complete for the 42 predicates in [derived.py](derived.py): both programs
   call their `derived.` names, and `run.py` requires each report independently of the
   axiom registry.
4. **This page.** The axiom's row in [the axioms one by one](#the-axioms-one-by-one), with
   the reason it holds in the plane, a word on the hyperbolic plane where it needs one,
   and the counts in the prose. `run.py --full --write` brings the numbers above and
   [results/](results/) up to date.
5. **The run.** `python3 -I tests/model/run.py --ties` checks the names and the hash in a
   second, and `--fast` runs what CI runs.

A word that joins the lock's vocabulary, as a definition does when a statement first uses
it, changes the lock and so its hash, while every axiom, and every word an axiom reaches,
stays as it was: then step 1 and step 5 are all, with a line in the comment of
[lock.sha256](lock.sha256) saying so, as its renewal of 17 October does. A word an axiom
reaches that changes is a changed definition (below).

These are values pinned to the axioms, and the pre-flight lets them land with the change
they follow; a law changed while its axiom stands, or any other change to the programs,
lands in a pull request of its own ([WORKFLOW](../../docs/WORKFLOW.md), section 10,
"Landing work: pull requests"). A word whose definition the axioms reach is read in
[model.py](model.py), so a changed definition changes code there, which lands on its own
too.

## Running it

From the repository's root, or anywhere:

```
python3 -I tests/model/run.py --fast            # what CI runs, under 20 seconds
python3 -I tests/model/run.py --full            # about seven minutes
python3 -I tests/model/run.py --full --write    # and save results/ and the counts above
python3 -I tests/model/run.py --ties            # the ties to the Lean alone, in a second
```

Each program also runs on its own, for example `python3 -I tests/model/search.py 20000 2`
(samples per axiom, then the seed), and `ONLY=pasch2,circles_meet` limits search.py and
hyperbolic.py to the axioms named.
