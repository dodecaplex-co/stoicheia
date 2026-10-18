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
| `Magnitudes.lean` | Lengths, angles and areas: `Magnitude` of each kind, which can be added and compared and nothing more, with `‖A B‖`, `∠ A B C`, `△ A B C` and the right angle `∟`. Each kind has a `0`, a convenience from System E for the "line" from a point to itself. |
| `Definitions.lean` | The definitions that do work: Definition 10 (`IsRightAngle`, with `IsAcute` and `IsObtuse`), Definition 15 (an axiom, `Definition15`: the radii of a circle are equal), the triangles (`Triangle`, `Equilateral`, `Isosceles`, `RightAngledTriangle`), the square of Definition 22 (`Square`) and parallels (`Parallel`, Definition 23). |
| `Phrases.lean` | Phrases Euclid never defines, as abbreviations: `SameSideOf`, `OppositeSidesOf`, `OnRay`, `InsideTriangle`, `AreParallel`, `Parallelogram` and its area `quadArea`. |
| `Postulates.lean` | The five postulates, each an `axiom`. |
| `CommonNotions.lean` | The five Common Notions, each a theorem; Common Notions 3 and 5 rest on tacit laws of magnitudes. |
| `Tacit/` | 81 tacit rules, from System E: `Diagram.lean`, `Transfer.lean`, `Constructions.lean`, `Metric.lean`, `Magnitudes.lean` and `Superposition.lean`. |

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
  and I.8 alone.
- **What the figure shows** is a tacit rule, a named axiom, from System E: an Intersection
  rule says when straight lines and circles must meet, and an Intersections rule lets a
  proof take a point where they do.
- **A rectilineal figure** (I.45) is two triangles. That is the figure Euclid's proof takes;
  his words allow any figure (see the exceptions).

## Shared steps

The rule of [FORMALIZATION.md](../FORMALIZATION.md), section 6, as Book I applies it:

- **Book Zero**, `Elements/Figure/`, proved from the foundations alone: `Basics.lean`
  (imports the rest), `Lines.lean` (order on a straight line; `produce_longer`),
  `Sides.lean`, `Rays.lean`, `Angles.lean`, `Lengths.lean`, `Triangles.lean`,
  `Circles.lean`, `Parallels.lean`, `Parallelograms.lean` and `Areas.lean`
  (`OnRay.eq_of_area_eq`, the "greater to the less" of I.39 and I.40).
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

The review records in `review/I/` are the authority, proposition by proposition. These are
the exceptions the outside review named, with the work that answers each:

| Proposition | Scope | What is restricted | Tag | Planned |
|---|---|---|---|---|
| I.40 | restricted | the equal bases meet end to end, as BC and CE | `adjacent-bases` | stage 2: `Prop40.general` for bases anywhere on one straight line, with `Prop40.special` |
| I.45 | restricted | the figure is two triangles | `two-triangles` | stage 2: `Prop45.figure` for a supplied dissection into triangles |

Both stay as Euclid's worked configuration, with the general theorem beside them as a
companion ([FORMALIZATION.md](../FORMALIZATION.md), section 2).

Two proofs follow Euclid with one step changed: I.39, and I.40 after it, make the end of
his reductio direct, the parallel through A being shown to pass through D
(`OnRay.eq_of_area_eq`). And two propositions are already contained in a rule, as the
[overlap catalogue](../reports/overlaps.md) records:

| Proposition | Rule | What the proof does |
|---|---|---|
| I.7 | Circle 4 (`not_same_side_of_circles_meet`) | Euclid's argument, by I.5; it never uses the rule |
| I.23 | superposition | Euclid's construction, by I.22 and I.8; it rests on the rule through I.8, which with I.4 alone may call on it directly |

The stage-5 review will give the hardest formal blocks (I.7, I.35, I.47) a paragraph of
their own in the mishnah.
