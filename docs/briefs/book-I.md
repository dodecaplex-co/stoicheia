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
| `Tacit/` | <!-- count:tacit-rules -->42<!-- /count --> tacit rules taken as axioms, from System E save two of our own, that every circle has a centre (`exists_centre`, from Definitions I.15 and I.16, by the owner's decision of 18 October 2026) and that a circle's radius is not nothing (`radius_ne_zero`, by the owner's decision of 25 October 2026): `Diagram.lean`, `Transfer.lean`, `Constructions.lean`, `Metric.lean`, `Magnitudes.lean` and `Superposition.lean`. |

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
  points. I.2 finds its points on those lines without Postulate 2. I.5 takes its produced
  sides as given, but still rests on Postulate 2 through proved rules, in its own Lean the
  order rule `Tacit.between_of_between_right`, beneath `OnRay.between_of_len_lt`, and
  Metric 8, `Tacit.area_swap`, and through I.4, which it cites.
  Where a proof must cut off from a straight line produced, `produce_longer`
  first makes it long enough.
- **Magnitudes, not numbers.** Lengths, angles and areas are separate kinds that add and
  compare. No proof uses coordinates or real numbers; I.47 is about areas, with no
  multiplication.
- **Right angles.** Definition 10 is a predicate, and Postulate 4 makes every right angle
  equal to `∟`, so that each use of Postulate 4 shows on the certificate.
- **Superposition** is a restricted inference in System E's style,
  [`Tacit.superposition`](../../Elements/Foundations/Tacit/Superposition.lean), used
  directly only in I.4 and I.8. A checked derivation over symbols may infer one equality
  of lengths, angles or triangles about the given figure from its given facts, the guards
  and a hypothetical placement. The guards require ABC to be a triangle, D and G to be
  distinct points of L, and H to be off L. The placement puts A on D, B′ on the ray from D
  through G and C′ on H's side of L, keeps the three sides and three angles, and keeps the
  side AC as a straight line through D and C′. The placed corners and side have fresh
  symbols that no exported formula can name; no derivation step constructs anything.
  Besides its logical steps, the derivation may cite only a fixed list: Metric 3, 4 and 9;
  that a length equal to one with distinct ends has distinct ends; one point at one
  distance on a ray; one ray for one angle, in its incidence and direction; and I.7. Each
  cited law is supplied with its proof. Our reading
  admits I.7 inside I.8's placement because its statement asserts no existence, though its
  earlier proof uses constructions. Since the second axiom retirement the same holds of
  four of the laws I.4 cites (distinct ends, one point at one distance on a ray, and both
  halves of one ray for one angle), whose proofs now use construction rules, and of the
  first two of them in I.8; only Metric 3, 4 and 9 are proved with none. These are
  restrictions on represented derivations: equivalence with System E's two printed rules
  is not claimed, nor is non-derivability of placement from the whole foundation. I.22 and I.23 construct congruent figures by
  Euclid's route.
- **What the figure shows** is supplied by System E's tacit rules and the facts proved
  from them: an Intersection rule says when straight lines and circles must meet, and an
  Intersections rule lets a proof take a point where they do. Forty-one rules are now theorems
  with their existing names and types; [FORMALIZATION](../FORMALIZATION.md#rules-now-proved)
  gives their derivations and homes.
- **A rectilineal figure** (I.45) is given by its outline (`Outline`, in
  `Elements/Foundations/Figures.lean`): finitely many simple closed lines of sides, apart or
  nested, so that it may have a corner pointing inwards, holes, separate pieces or contacts
  at corners, its region read from the sides by the parity of a ray's crossings. Equal to the
  figure means equal to its area (`Outline.area`), the sum that every division of it into
  triangles that lie apart gives. Book Zero proves that every outline has such a division
  (`division_exists`), and that any two divisions covering the same points have the same sum
  (`Apart.area_eq_of_same_region`): the step Euclid takes for granted, which David Hilbert
  proved, for his measure of area, and whose argument we follow
  ([the gap catalogue](../reports/gaps-book-I.md#i45), [brief 0013](0013-figures.md)). The
  general statement is `Prop45.outline`, and the scope is `full`
  ([#116](https://github.com/jackChallis/stoicheia/issues/116)). The older companions take
  the figure with its division into triangles, checked: triangles that lie apart (`Apart`),
  allowing a figure with a hole; triangles fitted together in a suitable order (`Fitted`,
  `Rectilineal`), for a figure with one boundary; or Euclid's and Oliver Byrne's triangles
  from one corner, under two conditions that `Fitted.fan` shows make them fit together, into
  the figure bounded by the closed line through the corners in order
  (`Prop45.fan_boundary`). Equal to the figure there means equal to those triangles
  together, which is its area. The tag `figure-with-dissection` names these older forms, and
  is no longer a limitation. The main theorem keeps Euclid's two triangles ABD and DBC,
  unchecked: an area-sum theorem, whose checked case is `Prop45.fan` for the corners D, A,
  B, C.

## Shared steps

The rule of [FORMALIZATION.md](../FORMALIZATION.md), section 6, as Book I applies it:

- **Book Zero**, `Elements/Figure/`, proved from the foundations alone: `Basics.lean`
  (imports the rest), `Lines.lean` (order on a straight line; `produce_longer`),
  `Sides.lean`, `Rays.lean`, `Angles.lean`, `Lengths.lean`, `Triangles.lean`,
  `Circles.lean`, `Parallels.lean`, `Parallelograms.lean`, `Areas.lean`
  (`area_lt_of_cut`, the strict area comparison in I.39 and I.40), `Sums.lean` (the sums
  of lists, and `InOrder.between_end`) and `Rectilineal.lean` (a fitted figure's triangles
  lie apart, `Fitted.inside_pairwise`); and brief 0013's figures given by their outlines,
  `Convex/`, `Cells.lean`, `Content.lean`, `Outlines.lean`, `Arrangements.lean`,
  `Divisions.lean` and `FanBoundary.lean`, with their helpers in the folders of the same
  names, on the words of `Elements/Foundations/Figures.lean`. `Superposition.lean`,
  imported separately by I.4 and I.8, proves the seven geometric laws their hypothetical
  placements cite, one theorem each (I.8 also cites I.7's, proved in I.8's own file); the
  certificate lists the construction rules beneath each (`cited_laws`).
- **Shared steps that cite a proposition:** `Elements/BookI/Helpers.lean`, with
  `Prop5.base` (I.5's angles at the base, with the sides produced anywhere); and
  `Elements/BookI/HelpersParallels.lean`, for those that cite I.28, I.30 or I.31, with
  `Prop30.meet` (a straight line meeting one of two parallels meets the other, after
  Proclus: Heath, vol. 1, pp. 207 and 316), `Prop30.parallel`, `Prop31.parallelogram`,
  `Prop28.interior` and `Prop28.square`; and `Elements/BookI/OutlineBound.lean`, after
  I.29, with `outline_bounded` (a figure given by its outline lies within a triangle), which
  cites I.23 and uses Postulate 5.
- **Corollaries after their propositions:** `Prop15.porism`, `Prop29.alternate`,
  `Prop29.interior`, `Prop29.exterior`, `Prop31.line`, `Prop34.bisect`, and
  `Prop46.square_eq` with `Prop46.side_eq` (squares on equal straight lines are equal, and
  conversely, as Heath reports Proclus proving under I.46).
- **Companions after their propositions** (the exceptions, below): I.40's, I.45's and
  I.47's; and, in `Prop45.lean`, two bridges: `Fitted.fan`, before `Prop45.fan`, which cites
  I.13; and `Prop45.fan_boundary`, beside `Prop45.outline`, which joins the checked fan to
  its outline and cites I.13 through `Fitted.fan`.

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
have scope `full`; so does I.45, through `Prop45.outline`, from 22 October 2026, after it
was `restricted` to a supplied checked division from 20 October (#116):

| Proposition | Scope | Main theorem | Companions | Tag |
|---|---|---|---|---|
| I.40 | full | the equal bases meet end to end, as BC and CE | `Prop40.general`, for equal bases anywhere on one straight line; `Prop40.join` and `Prop40.special` | |
| I.45 | full | the figure is two triangles, unchecked | `Prop45.outline`, the main companion, for any figure given by its outline; `Prop45.apart`, `Prop45.figure` and `Prop45.fan`, for a figure given with a checked division into triangles; `Prop45.append` and `Prop45.sum`, the construction | `figure-with-dissection`, for the older supplied-division companions |
| I.47 | full | the three squares stand outward from the triangle | `Prop47.general`, for squares independently on either side of each base | |

These main theorems stay as Euclid's worked configuration, with companions extending them
under the hypotheses and limits above ([FORMALIZATION.md](../FORMALIZATION.md), section 2).

Reconciled 19 October 2026: I.39 and I.40 follow Euclid's closing reductio. The contrary
supposition makes the constructed intersection differ from D; either order on the same
ray contradicts equal areas. I.40's general companion uses the same argument for equal
bases anywhere on one straight line, including coincident vertices.

The [overlap catalogue](../reports/overlaps.md) records the retired shortcuts.
The former construction overlaps for I.2, I.3 and I.23 used the existential
superposition rule and are retired. I.2 and I.3 do not rest on superposition. I.23's points
come from I.22 and its angle equality from I.8; its proof rests on the restricted rule
through I.8 and I.20, which supplies the triangle inequalities.

19 October 2026: I.7's former overlap with Circle 4 is retired. Circle 4 is now a
corollary after I.7 in `Elements/BookI/Prop07.lean`, proved from I.7, Definition I.15
and `circle_eq`; using it to prove I.7 would be circular. The right-angle rule
`adjacent_eq_of_right` and the converse angle-addition rule `inside_of_angle_add` are
corollaries after I.13. The other five retired rules are proved in Book Zero's
`Circles.lean`. By the owner's decision of 19 October 2026 ("Please do both. 79 is rather large with so
many books in front of us."), 31 more rules became
theorems in Book Zero's `RuleBase.lean`, `Incidence.lean`, `AreaRules.lean` and
`CirclePoints.lean`, proved that day. On 24 October 2026 Circle 3 followed, proved after
III.2 in `Elements/BookIII/Prop02.lean`, with Circle 2, Points 9 and Intersection 2 moved
beside it, and on 26 October 2026 Circle 1, proved there too. With our own rules that every
circle has a centre and, from 25 October 2026, that its radius is not nothing, the lock
now holds <!-- count:axioms -->48<!-- /count --> axioms, including <!-- count:tacit-rules -->42<!-- /count --> tacit rules.

The stage-5 review will give the hardest formal blocks (I.7, I.35, I.47) a paragraph of
their own in the mishnah.
