# Book I: the brief

*The current decisions for Book I in one place: its words, how its statements say Euclid's
phrases, its representations, its shared steps, the choices its statements make, and its
exceptions. It gathers what [the plan](0001-plan.md), [the decisions](0002-decisions.md)
and the first mates' reports ([first-mate-02](../reports/crew/first-mate-02.md),
[first-mate-03](../reports/crew/first-mate-03.md),
[first-mate-04](../reports/crew/first-mate-04.md)) settled, and agrees with the code. A
disagreement found later is recorded and reconciled, as
[FORMALIZATION.md](../FORMALIZATION.md) asks. The reasons are in the linked reports; this
page keeps the outcomes.*

## The words

Book I's words are the foundations every later book uses, in `Elements/Foundations/`.

| File | What it holds |
|---|---|
| `Words.lean` | The words Euclid leaves undefined, each `opaque`: `Point`, `Line`, `Circle`, `OnLine`, `SameSide`, `Between`, `OnCircle`, `InsideCircle`, `Centre`; and words defined from them, `Collinear`, `OppositeSides`, `OutsideCircle`, `LinesMeet`, `LineMeetsCircle`, `CirclesMeet`. |
| `Magnitudes.lean` | Lengths, angles and areas: `Magnitude` of each kind, which can be added and compared and nothing more, with `‖A B‖`, `∠ A B C`, `△ A B C` and the right angle `∟`. Each kind has a `0`, a convenience from System E for the "line" from a point to itself. The sum of a list of magnitudes, `Magnitude.sum`, says "any number" (II.1, I.45, II.14). |
| `Definitions.lean` | The definitions that do work: Definition 10 (`IsRightAngle`, with `IsAcute` and `IsObtuse`), Definition 15 (an axiom, `Definition15`: the radii of a circle are equal), the triangles (`Triangle`, `Equilateral`), the square of Definition 22 (`Square`) and parallels (`Parallel`, Definition 23); and two that no statement or proof uses yet, the isosceles and right-angled triangles of Definitions 20 and 21 (`Isosceles`, `RightAngledTriangle`). |
| `Phrases.lean` | Phrases Euclid never defines, as abbreviations: `SameSideOf`, `OppositeSidesOf`, `OnRay`, `InsideTriangle`, `AreParallel`, `Parallelogram` and its area `quadArea`; points in order on a straight line, `InOrder`, with `segments` and `endOf` (II.1); and a rectilineal figure given with its triangles (Definitions I.14 and I.19), as triangles that lie apart, `Apart`, or fitted together, `Fitted` and `Rectilineal`, each with its area as given, with `OnFiniteLine`, `OnOrInsideTriangle`, `Corners` and `triples`. |
| `Postulates.lean` | The five postulates, each an `axiom`. |
| `CommonNotions.lean` | The five Common Notions, each a theorem; Common Notions 3 and 5 rest on tacit laws of magnitudes. |
| `Tacit/` | <!-- count:tacit-rules -->74<!-- /count --> tacit rules taken as axioms, from System E save one of our own, that every circle has a centre (`exists_centre`, from Definitions I.15 and I.16, by the owner's decision of 18 October 2026): `Diagram.lean`, `Transfer.lean`, `Constructions.lean`, `Metric.lean`, `Magnitudes.lean` and `Superposition.lean`. |

## How the statements say Euclid's phrases

| Euclid | Lean |
|---|---|
| "the straight line AB" | the points `A`, `B`, and, where a straight line is needed, the `Line` through them (Postulate 1) |
| "AB is equal to CD" | `‖A B‖ = ‖C D‖` |
| "the angle ABC" | `∠ A B C` |
| "the triangle ABC is equal to the triangle DEF" | `△ A B C = △ D E F` |
| "on the same side of AB" | `SameSideOf C D A B` |
| "AB is parallel to CD" | `AreParallel A B C D` |
| "the parallelogram ABCD" | `Parallelogram A B C D`, its area `quadArea A B C D` |
| "the square ABDE" | `Square A B D E` |
| "greater", "less" | `<` between magnitudes of one kind |

A problem is an `∃` theorem returning what it constructs; a theorem is an implication.
Hypotheses come from the setting-out, conclusions from "I say that".

## Representations

- **A straight line is whole.** A `Line` is the whole straight line, named by any two of its
  points, so producing one usually costs nothing: the proofs of I.2 and I.5 use no
  Postulate 2. Where a proof must cut off from a straight line produced, `produce_longer`
  first makes it long enough.
- **Magnitudes, not numbers.** Lengths, angles and areas are separate kinds that add and
  compare. No proof uses coordinates or real numbers; I.47 is about areas, with no
  multiplication.
- **Right angles.** Definition 10 is a predicate, and Postulate 4 makes every right angle
  equal to `∟`, so that each use of Postulate 4 shows on the certificate.
- **Superposition** is one rule, after LeanEuclid's form of System E's two, allowed in I.4
  and I.8 alone. That limits where it is used, not what it can do: as a construction
  principle it is stronger than System E's restricted inference rule
  ([Superposition.lean](../../Elements/Foundations/Tacit/Superposition.lean)), and a
  restricted rule is being prototyped
  ([#75](https://github.com/jackChallis/stoicheia/issues/75)).
- **What the figure shows** is supplied by System E's tacit rules and the facts proved
  from them: an Intersection rule says when straight lines and circles must meet, and an
  Intersections rule lets a proof take a point where they do. Eight rules are now theorems
  with their existing names and types; [FORMALIZATION](../FORMALIZATION.md#rules-now-proved)
  gives their derivations and homes.
- **A rectilineal figure** (I.45) is given with its division into triangles, and the division
  is checked: triangles that lie apart (`Apart`), allowing a figure with a hole;
  triangles fitted together in a suitable order (`Fitted`, `Rectilineal`), for a figure
  with one boundary; or Euclid's and Oliver Byrne's triangles from one corner, under two
  conditions that `Fitted.fan` shows make them fit together. Equal to the figure means equal
  to those triangles together. The scope is `restricted`: existence of a division from the
  figure's outline, coverage of its region, and independence of the sum from the division
  chosen remain unproved ([#116](https://github.com/jackChallis/stoicheia/issues/116)).
  The last is the step Euclid takes for granted, which David Hilbert proved, for his
  measure of area ([the gap catalogue](../reports/gaps-book-I.md#i45)).
  The tag is `figure-with-dissection`. The main theorem keeps Euclid's two triangles ABD and
  DBC, unchecked: an area-sum theorem, whose checked case is `Prop45.fan` for the corners D,
  A, B, C.

## Shared steps

The rule of [FORMALIZATION.md](../FORMALIZATION.md), section 6, as Book I applies it:

- **Book Zero**, `Elements/Figure/`, proved from the foundations alone: `Basics.lean`
  (imports the rest), `Lines.lean` (order on a straight line; `produce_longer`),
  `Sides.lean`, `Rays.lean`, `Angles.lean`, `Lengths.lean`, `Triangles.lean`,
  `Circles.lean`, `Parallels.lean`, `Parallelograms.lean`, `Areas.lean`
  (`area_lt_of_cut`, the strict area comparison in I.39 and I.40), `Sums.lean` (the sums
  of lists, and `InOrder.between_end`) and `Rectilineal.lean` (a fitted figure's triangles
  lie apart, `Fitted.inside_pairwise`).
- **Shared steps that cite a proposition:** `Elements/BookI/Helpers.lean`, with
  `Prop5.base` (I.5's angles at the base, with the sides produced anywhere); and
  `Elements/BookI/HelpersParallels.lean`, for those that cite I.28, I.30 or I.31, with
  `Prop30.meet` (a straight line meeting one of two parallels meets the other, after
  Proclus: Heath, vol. 1, pp. 207 and 316), `Prop30.parallel`, `Prop31.parallelogram`,
  `Prop28.interior` and `Prop28.square`.
- **Corollaries after their propositions:** `Prop15.porism`, `Prop29.alternate`,
  `Prop29.interior`, `Prop29.exterior`, `Prop31.line`, `Prop34.bisect`, and
  `Prop46.square_eq` with `Prop46.side_eq` (squares on equal straight lines are equal, and
  conversely, as Heath reports Proclus proving under I.46).
- **Companions after their propositions** (the exceptions, below): I.40's, I.45's and
  I.47's; and, in `Prop45.lean` before `Prop45.fan`, the bridge `Fitted.fan`, which cites
  I.13.

19 October 2026: the statement of `Prop47.general` was challenged by an independent reader
who wrote none of it, and approved as written by the coordinator.

## The statements' choices

Each was approved before its voyage, and the reasons are in the first mates' reports.

- **I.1** takes an optional point P, and puts the triangle on P's side of AB when P is off
  it: I.9 and I.11 need a particular side.
- **I.9** says that its bisector lies within the angle.
- **I.15** keeps its Porism, which Heiberg brackets, as a theorem of its own.
- **I.22** builds its triangle at a given corner.
- **I.23** puts G on the ray from A through B and F on P's side of AB, as Heath's figure has
  them (vol. 1, p. 294).
- **I.38** lets its two triangles share their vertex, as I.42 needs, and **I.37** reads "in
  the same parallels" the same way, so that I.39 and I.41 need no case for it.
- **I.44** carries out Euclid's "let it be placed" itself (`Prop44.place`).
- **I.48** says that each of its three squares lies on one side of the side it is described
  on.

## Policies

- **Postulate 5.** No proof before I.29 uses Postulate 5, or a rule declared in
  `Elements.Tacit.Euclidean`; I.31's proof does not use it either. `check_fidelity.py`
  enforces the boundary.
- **Superposition** only in I.4 and I.8.

## Exceptions

The review records in `review/I/` are the authority, proposition by proposition. Stage 2 of
[brief 0006](0006-statements.md) answered I.40 and I.45 with companions. `Prop47.general`
makes the transfer from outward squares to squares on either side explicit. I.40 and I.47
have scope `full`; I.45 is `restricted` to a supplied checked division, with outline
coverage and independence of division still unproved (#116):

| Proposition | Scope | Main theorem | Companions | Tag |
|---|---|---|---|---|
| I.40 | full | the equal bases meet end to end, as BC and CE | `Prop40.general`, for equal bases anywhere on one straight line; `Prop40.join` and `Prop40.special` | |
| I.45 | restricted | the figure is two triangles, unchecked | `Prop45.apart`, for a supplied checked division into triangles that lie apart; `Prop45.figure` and `Prop45.fan`, the main companion, beside it; `Prop45.append` and `Prop45.sum`, the construction | `figure-with-dissection` |
| I.47 | full | the three squares stand outward from the triangle | `Prop47.general`, for squares independently on either side of each base | |

These main theorems stay as Euclid's worked configuration, with companions extending them
under the hypotheses and limits above ([FORMALIZATION.md](../FORMALIZATION.md), section 2).

Reconciled 19 October 2026: I.39 and I.40 follow Euclid's closing reductio. The contrary
supposition makes the constructed intersection differ from D; either order on the same
ray contradicts equal areas. I.40's general companion uses the same argument for equal
bases anywhere on one straight line, including coincident vertices.

For three propositions superposition supplies a step, as the
[overlap catalogue](../reports/overlaps.md) records:

| Proposition | Rule | What the proof does |
|---|---|---|
| I.2 | superposition | Euclid's construction, by I.1 and two circles; it never uses the rule |
| I.3 | superposition | Euclid's construction, by I.2 and a circle; it never uses the rule |
| I.23 | superposition | Euclid's construction, by I.22 and I.8; it rests on the rule through I.8, which with I.4 alone may call on it directly, and through I.20 |

19 October 2026: I.7's former overlap with Circle 4 is retired. Circle 4 is now a
corollary after I.7 in `Elements/BookI/Prop07.lean`, proved from I.7, Definition I.15
and `circle_eq`; using it to prove I.7 would be circular. The right-angle rule
`adjacent_eq_of_right` and the converse angle-addition rule `inside_of_angle_add` are
corollaries after I.13. The other five retired rules are proved in Book Zero's
`Circles.lean`. The lock now holds <!-- count:axioms -->80<!-- /count --> axioms, including <!-- count:tacit-rules -->74<!-- /count --> tacit rules.

The stage-5 review will give the hardest formal blocks (I.7, I.35, I.47) a paragraph of
their own in the mishnah.
