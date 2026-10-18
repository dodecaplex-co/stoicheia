# Mixed angles: a prototype for III.16 and III.31

Issue #56, for the decision on issue #57. The Lean is
[`Staging/Stage4b/MixedAngles.lean`](../../Staging/Stage4b/MixedAngles.lean), on the branch
`lean/mixed-angle-prototype`. It follows the design in Astra's answer on issue #51, whose
III.16 and III.31 parts it implements; thanks to Astra for a design that turned out to need
no new assumption at all.

**In short.** The representation Astra proposed works in plain Lean on the existing
foundations. Every check Astra asked for is proved, and so are the comparisons of III.16
and III.31 themselves, for every acute angle (III.16), every right angle placed along the
chord, and every straight line in the circle that does not pass through the centre
(III.31). There is no `sorry` in the file and no new axiom: every declaration rests only on
the postulates, Definition I.15, the System E rules already in `Elements/Foundations/`,
and earlier propositions (I.12, I.17, I.19, I.23, III.16 and III.31). The recommendation for
#57 is **go**, on the conditions in the last section.

## 1. The representation

**Regions.** A region is a predicate on points, `Point → Prop`.

- **A rectilineal angle** `BAC` has the region `WithinAngle B A C`: the points on `C`'s side
  of the straight line `AB` and on `B`'s side of `AC`. This is the phrase Book Zero already
  uses ("within the angle"), made a definition. Its arms are not in it.
- **A mixed angle** is a geometric object of its own, `MixedAngle`, recorded by its vertex,
  its straight arm, its circle, and the branch and side of the circumference that bound it.
  Euclid uses two kinds, one for each side of the circumference:
  - `MixedAngle.ofSegment A B α S`, **the angle of a segment** (Definition III.7): the
    straight arm is the ray `AB`, with `B` on the circle `α`; the branch is the one on `S`'s
    side of `AB`; the side is within the circle. Its region is the points within `α` on `S`'s
    side of `AB`. The angle of the semicircle in III.16 is the case of a diameter.
  - `MixedAngle.ofContact A E α B`, **the angle of contact**, III.16's remaining angle, the
    horn-like angle: the straight arm is the ray `AE`, touching `α` at `A`; the branch is the
    one on `E`'s side of the straight line `AB`, which passes within the circle; the side is
    without. Its region is the points without `α` and within the angle `EAB`.

  The conditions that make each a true mixed angle (`B` on the circle; `AE` touching it) are
  hypotheses of the theorems, as they are of the propositions. A segment's region runs on
  far from `A` (it is the whole segment), and the horn's region includes points beyond the
  circle far from `A`; neither matters, since only the neighbourhood of the vertex enters a
  comparison.

**Comparison by local containment.** "Near the vertex" is said with circles about `A`, as
Euclid would draw them, and no numbers:

- `LocallyWithin A R S`: some circle about `A` holds no point of `R` that is not in `S`;
- `NearVertex A R`: every circle about `A`, however small, holds a point of `R`;
- `LocallyLess A R S`: `LocallyWithin A R S`, and `NearVertex A` of the points of `S` not in
  `R` (strictness);
- `LocallyEqual A R S`: each locally within the other.

Containment of whole regions would be the wrong condition, as Astra warned: a straight ray
that enters a circle leaves it again, so an acute angle is never wholly within the
semicircle, only near its vertex. Comparisons are made at one vertex with the straight arms
aligned, as Euclid makes them; a rectilineal angle is brought to the vertex by I.23.

## 2. What is proved

Every declaration below is proved; the file has no `sorry`. "Plain words" read the Lean
back, not Heath.

### The definitions

| Declaration | Plain words |
|---|---|
| `WithinAngle B A C P` | `P` is on `C`'s side of `AB` and on `B`'s side of `AC`. |
| `MixedAngle`, `.ofSegment`, `.ofContact` | A mixed angle: the angle of a segment, or the angle of contact (above). |
| `MixedAngle.vertex` | Its vertex. |
| `MixedAngle.region` | Its region (above). |
| `LocallyWithin A R S` | Some circle about `A` holds no point of `R` outside `S`. |
| `NearVertex A R` | Every circle about `A` holds a point of `R`. |
| `LocallyLess A R S` | Near `A`, `R` is within `S`, and `S` has points outside `R` as near `A` as we please. |
| `LocallyEqual A R S` | Near `A`, each of `R`, `S` is within the other. |

### Check (a): with straight boundaries, the comparison is the order of angles

| Declaration | Plain words |
|---|---|
| `WithinAngle.locallyLess_iff` | For angles `BAD`, `BAC` with the common arm `AB`, `D` and `C` on one side of it: `BAD` is locally less than `BAC` exactly when `∠ B A D < ∠ B A C`. |
| `WithinAngle.locallyEqual_iff` | The same angles are locally equal exactly when `∠ B A D = ∠ B A C`. |
| `WithinAngle.locallyLess_of_lt` | The less angle is locally less; the witnesses are points within the angle `DAC`. |
| `sameSideOf_of_angle_lt` | On one side of `AB`, the less angle lies within the greater: `D` is on `B`'s side of `AC`. |

### Check (b): naming points and placement do not matter

| Declaration | Plain words |
|---|---|
| `WithinAngle.congr` | Other points of the same two rays name the same region. |
| `WithinAngle.comm` | `BAC` and `CAB` have one region. |
| `WithinAngle.eq_of_angle_eq` | Equal angles placed along `AB` on one side have one region. |
| `WithinAngle.locallyLess_placement` | So a rectilineal angle placed along `AB` compares with any region according to its size alone, whichever equal angle is placed. |
| `MixedAngle.ofSegment_congr` | Another point of the ray `AB`, or another point on `S`'s side, names the same angle of a segment. |
| `MixedAngle.ofContact_congr` | Other points of the rays `AE` and `AB` name the same angle of contact. |
| `locallyLess_congr` | Regions with the same points compare alike. |

### Check (c): the horn is not an empty angle, and not a rectilineal one

| Declaration | Plain words |
|---|---|
| `Prop16.horn_nearVertex` | Every circle about `A` holds a point of the remaining angle of III.16: within the angle `EAB` and without the circle. |
| `Prop16.horn_no_ray` | For every point `F` within the angle `EAB`, the points of the ray `AF` near `A` are not in the horn: they are within the circle. |

Together these keep both of Astra's pitfalls in view: the horn has points as near the
vertex as we please, so the upper bounds below are not met by an empty region; and no
straight ray from the vertex runs within it, so it cannot be replaced by a rectilineal angle
or by the rays that enter it.

### Check (d): the comparisons of III.16

In Heath's letters: the circle `ABC` about `D`, `AB` a diameter, `AE` at right angles to it
at `A`. The hypotheses are those of `BookIII.Prop16`.

| Declaration | Plain words |
|---|---|
| `Prop16.semicircle_gt` | For every `F` on `E`'s side of `AB` with `∠ B A F < ∟`, the angle `BAF` is locally less than the angle of the semicircle, `ofSegment A B ABC E`. |
| `Prop16.horn_lt` | For every `F` on the circle's side of `AE` with `∠ E A F < ∟`, the remaining angle, `ofContact A E ABC B`, is locally less than the angle `EAF`. |
| `Prop16.semicircle_gt_acute` | Every acute rectilineal angle `XYZ` can be placed at `A` along `AB` on `E`'s side [I. 23], and there it is locally less than the angle of the semicircle. |
| `Prop16.horn_lt_acute` | Every acute rectilineal angle `XYZ` can be placed at `A` along `AE` towards the circle [I. 23], and there the remaining angle is locally less than it. |
| `Prop16.semicircle_lt_right` | The angle of the semicircle is locally less than the right angle `BAE`. |

So the angle of the semicircle lies strictly between every acute angle and the right angle,
and the horn strictly between nothing and every acute angle: the comparisons say what Heath's
enunciation says, for actual nondegenerate rectilineal angles, quantified over all of them.

### The comparisons of III.31

In Heath's letters: the circle `ABCD` with diameter `BC` and centre `E`, `A` on it, `BA`
carried through to `F`. The hypotheses are those of `BookIII.Prop31`.

| Declaration | Plain words |
|---|---|
| `Prop31.greater_gt_right` | Every right angle `CAR` placed along `AC` on `B`'s side is locally less than the angle of the greater segment, `ofSegment A C ABCD B`. |
| `Prop31.less_lt_right` | For `D` on the other side of `AC` from `B`, the angle of the less segment, `ofSegment A C ABCD D`, is locally less than every right angle `CAR` placed along `AC` on `D`'s side. |
| `Prop31.chord_greater_gt_right` | For any straight line `AC` in a circle about `E`, not through the centre, at either end: every right angle placed along `AC` on the centre's side is locally less than the angle of the segment on that side. |
| `Prop31.chord_less_lt_right` | The same straight line: the angle of the segment on the side away from the centre is locally less than every right angle placed along `AC` on that side. |
| `Prop31.diameter_through` | The diameter through `C` ends at a point `B` other than `A`, on the centre's side of `AC`. |

The last two are Astra's form, "for every nondiameter chord, at either endpoint"; Euclid's
figure is the case where `B` is the far end of the diameter through `C`. The less segment
turns out to lie wholly within the right angle `CAF`, not only near `A`; the greater
segment's containment is local.

### The steps they share

| Declaration | Plain words |
|---|---|
| `near_inside_of_angle` | If `A`, `B`, `C` are on or within a circle and `BAC` is a true angle, some circle about `A` holds no point of the angle, or of its arms, that is not within the circle. The radius is `AN`, `N` the foot of the perpendicular from `A` to `BC` [I. 12, I. 17, I. 19]. |
| `exists_near_across` | If the points of the ray `AU` near `A` are within a circle and every point of the ray `AV` is without it, every circle about `A` holds points within the angle `UAV` on each side of the circumference. |
| `near_inside_of_ray` | The points of a ray from a point of a circle towards a point on or within it are within the circle near `A`. |
| `Prop16.outside_of_onRay` | III.16's first part, for the points of the ray `AE`. |
| `Prop16.inside_sameSideOf` | The whole circle lies on `B`'s side of `AE`. |
| `Prop16.near_inside` | III.16's second part made local: for `F` within the angle `EAB`, near `A` the angle `FAB` and the ray `AF` lie within the circle. |
| `WithinAngle.mono`, `.mono'`, `.not_sameSideOf`, `.of_between`, `.exists_near` | Angles within angles (Triple incidence 1 and 3), a point between two arms is within the angle, and every circle about the vertex holds a point within it. |
| `sameSideOf_self`, `onLine_of_collinear`, `sameSideOf_congr_collinear`, `sameSideOf_congr_line`, `sameSideOf_congr_point`, `onRay_trans`, `sameSideOf_of_between` | Sides and rays: Book Zero's kind of fact. |
| `exists_centre`, `exists_onRay_inside`, `exists_inside_both` | Every point is a centre; a ray from the centre has points within the circle; of two circles about one point, one lies within the other. |
| `not_locallyWithin` | A region locally within another has no points outside it near the vertex. |

### The routes

III.16's comparisons follow Euclid's idea, that no straight line can be interposed: the
straight line `AF` falls within the circle at a point `G` (III.16's second part), and near
`A` the whole angle between `AG` and the diameter is within the circle. What Euclid leaves
unsaid is "near `A`": how near is given by the perpendicular from `A` to `GD`, by I.12,
I.17 and I.19. A review record would mark this a `helper` for the local bound. III.31's
comparisons are Euclid's "manifest" containments, proved: the right angle `BAC` lies within
the greater segment near `A`, by the same local bound, and the less segment lies within the
right angle `CAF` everywhere (a point of it beyond `AB` would put a point within the circle
on the straight line `AB` but outside `AB` itself, against Circle 1 and Pasch 2 and 3).

The III.16 lemmas cite nothing after III.16. The III.31 lemmas cite III.31 (that `BAC` is
right) and so sit after it. Four of the III.31 declarations rest on Postulate 5, through
III.31's own proof (I.32), as III.31 already does.

## 3. What resisted, and what is left open

Nothing resisted: every lemma was proved as first stated, and no statement was weakened to
make a proof go through. These questions are open, and belong to the decision on #57:

- **Congruent placement at another vertex.** Check (b) covers naming points, and equal
  rectilineal angles placed at one vertex. That a mixed angle is unchanged when the whole
  figure is laid down elsewhere (the angle of a semicircle in one circle equal to that in an
  equal circle) is not stated: the foundations move only triangles (superposition, in I.4 and
  I.8 alone). III.16 and III.31 do not need it, since every comparison is made at one vertex.
- **Strictness on arbitrary regions.** `LocallyLess` asks for points of the larger region
  outside the smaller; it does not ask that they be interior points. For the regions here,
  which are open, this is no weakness, and every witness the proofs construct lies strictly
  inside both the angle and the side of the circumference it names. But for an artificial
  region, an angle with a ray taken out of it, the definition would count the angle itself
  as greater. If the definitions go to the foundations for wider use, a stronger strictness
  (a whole small circle of witnesses about each point) is worth weighing; III.16 and III.31
  do not need it.
- **No arithmetic of mixed angles.** There is no addition, no multiple and no ratio of mixed
  angles, and no law that every two are comparable. The horn is something (check (c)) and less
  than every acute angle, so no Archimedean law could hold of both kinds together; nothing
  here asserts one, as Astra advised (Heath, volume II, p. 40, on Proclus).
- **Where the proofs live.** Staged files normally hold statements with `sorry`
  (WORKFLOW, section 2). This file holds proofs because it tests a representation, as the
  prototype of a new foundation does; the coordinator decides whether it stays in `Staging/`,
  moves to `docs/reports/crew/` as a scratch proof, or is split between the foundations and
  `Elements/BookIII/` on adoption.

## 4. Is an axiom needed?

No. Every fact used is already in the foundations or proved from them: the postulates,
Definition I.15, System E's rules for sides, betweenness, circles and angles (Circle 1 to 3,
Pasch 1 to 3, Triple incidence 1 to 3, Intersections 4 and 5), and I.12, I.17, I.19, I.23,
III.16 and III.31. `#print axioms` on each of the 47 theorems lists only declarations of
`Elements/Foundations/` and Lean's own `propext`, `Classical.choice` and `Quot.sound`;
`sorryAx` appears in none. Nothing goes to the owner as an axiom.

## 5. Recommendation for #57

**Go for full**, for III.16 and III.31, on these conditions:

1. **The words.** `WithinAngle`, `MixedAngle` with its two kinds, `LocallyWithin`,
   `NearVertex` and `LocallyLess` move to `Elements/Foundations/DefinitionsIII.lean`, with
   the coordinator's approval, `check_fidelity.py --write-lock`, a decisions entry, and the
   model lock and `tests/model/MODEL.md` read again (WORKFLOW, section 2, item 1). They are
   definitions, not axioms, and add nothing to what is assumed.
2. **The statements.** III.16 gains the two comparisons and III.31 the two, as restatements
   of `theorem Prop16` and `theorem Prop31` (staged as `Elements.BookIII.Staging.Prop16` and
   `.Prop31`), so that Lean stands under Heath's angle sentences, which have none today. The
   forms proved here are ready to be those conjuncts: `Prop16.semicircle_gt` and
   `Prop16.horn_lt` quantified over `F`, and `Prop31.greater_gt_right` and
   `Prop31.less_lt_right` over `R`. `Prop16.horn_nearVertex` belongs beside them, or in the
   record, as the check that the horn is not empty. The general forms (any acute angle by
   I.23; any chord not through the centre) are companions.
3. **The shared steps.** `near_inside_of_angle` and `exists_near_across` cite I.12, I.17 and
   I.19, and go to `Elements/BookIII/Squares.lean`; the small facts on sides and rays go to
   Book Zero.
4. **The records.** III.16 and III.31 drop `mixed-angles-omitted` and take a new tag, defined
   in `review/terms.toml` before use, carrying Astra's wording: the comparisons use local
   containment of curved angular regions, and no general arithmetic or ratio theory of mixed
   angles is claimed. The passage for the local bound is a `helper`.
5. **The challenge.** As with every new representation, readers who did not write these
   definitions challenge them before approval, starting from the open questions in section 3.
