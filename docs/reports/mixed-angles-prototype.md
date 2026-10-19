# Mixed angles: a prototype for III.16 and III.31

Issue #56, for the decision on issue #57. The Lean was `Staging/Stage4b/MixedAngles.lean`,
which has since moved into the edition (the note below). It follows the design in Astra's
answer on issue #51, whose III.16 and III.31 parts it implements; thanks to Astra for a
design that turned out to need no new assumption at all.

*Moved into the edition on 18 October 2026, by [brief 0011](../briefs/0011-mixed-angles.md),
and the staged file is gone. Its words are in `Elements/Foundations/DefinitionsIII.lean`;
the facts that cite no proposition in Book Zero, `Elements/Figure/Regions.lean`; the steps
that cite one in `Elements/BookIII/MixedAngles.lean`; and the steps, companions and
comparisons at another vertex of III.16 and III.31 in their own files. This report describes
the prototype as the coordinator approved it, with the one rename brief 0008 asked for
(`exists_centre` became `exists_circle_about`, at `ca8bd4d`): its names, line numbers and
census are that file's, and brief 0011 says what changed on the move.*

*Revised 18 October 2026, twice. The first revision answered the challenge on #56: the
strict comparison asks for whole small circles of excess, and in III.16's figure the angle
of contact is shown not to depend on the straight line that names its branch. The second
answers the re-challenge and two reviews of that revision: `FallsShort` now certifies that
the mixed angle is something, both comparisons refuse a straight angle,
`MixedAngle.WellFormed` says when the named points give Euclid's angle, and placement at
another vertex is proved in the form section 3 states. A verifier who did not write the
second revision then read it at `dfb9291` and handed back at `4705a9c` with a fix of its
own; its editorial findings are answered, and the coordinator's decisions on placement and
on where the proofs live are recorded (section 3, condition 6). The appendix lists every
finding and what was done.*

**In short.** The representation Astra proposed works in plain Lean on the existing
foundations, with no new axiom and no `sorry`. Proved: Astra's checks (a) and (c) in full;
check (b) for naming points and for equal rectilineal angles at one vertex, and, for the
angle of contact, in III.16's figure; the comparisons of III.16 for every acute angle and of
III.31 for every right angle and every straight line in the circle not through the centre;
that the four angles compared are the angles Euclid draws; and placement at another vertex,
as an invariance of the comparisons with equal rectilineal angles (section 3). Not proved:
the angle of contact for a touching straight line in general, a motion of a mixed angle
itself, and any arithmetic of mixed angles; III.16 and III.31 need none of these. The
recommendation for #57 is **go**, on the conditions of section 5.

## 1. The representation

**Regions.** A region is a predicate on points, `Point → Prop`.

- **A rectilineal angle** BAC has the region `WithinAngle B A C`: the points on C's side of
  the straight line AB and on B's side of AC. This is the phrase Book Zero already uses
  ("within the angle"), made a definition. Its arms are not in it, and a straight angle has
  an empty region.
- **A mixed angle** is a geometric object of its own, `MixedAngle`, recorded by its vertex,
  its straight arm, its circle, and the branch and side of the circumference that bound it.
  Euclid uses two kinds, one for each side of the circumference:
  - `MixedAngle.ofSegment A B α S`, **the angle of a segment** (Definition III.7): the
    points within `α` on S's side of AB. The region depends only on the straight line AB,
    but a comparison places a rectilineal angle along the ray from A through B, so B names
    the ray that runs into the circle: in III.31 the other end of the straight line, and for
    the angle of the semicircle in III.16 a point of the diameter beyond the centre.
  - `MixedAngle.ofContact A E α B`, **the angle of contact**, III.16's remaining angle, the
    horn-like angle: the points without `α` and within the angle EAB. Its straight arm is
    the ray AE; B names its branch by a straight line AB into the circle.

  Nothing about the kinds is assumed when they are formed. `MixedAngle.WellFormed` says what
  Euclid's figure asks: for the angle of a segment, A on the circle, the ray AB passing
  within it, and S off AB; for the angle of contact, A on the circle, AE touching it
  (Definition III.2), the ray AB passing within it, and B off AE. The angles III.16 and
  III.31 compare are shown to have it. A segment's region runs on far from A, and the horn's
  includes points beyond the circle far from A; neither matters, since only the
  neighbourhood of the vertex enters a comparison.

**Comparison by local containment.** "Near the vertex" is said with circles about A, as
Euclid would draw them, and no numbers:

- `LocallyWithin A R S`: some circle about A holds no point of R that is not in S;
- `Surrounds R P`: some circle about P holds only points of R;
- `NearVertexOpen A R`: every circle about A, however small, holds a point that R surrounds;
- `LocallyLess A R S`: `LocallyWithin A R S`, and `NearVertexOpen A` of the points of S not
  in R (strictness);
- `LocallyEqual A R S`: each locally within the other;
- `MixedAngle.Exceeds m B C`: B, X, C are not on one straight line, X being the vertex of
  `m`, and the angle BXC is locally less than `m` at X;
- `MixedAngle.FallsShort m B C`: B, X, C are not on one straight line, `m` comes as near X
  as we please (`NearVertexOpen`), and `m` is locally less than the angle BXC at X.

The vertex is the mixed angle's own, so a comparison cannot be made at another point.
Without the true-angle condition, every mixed angle that is something would exceed a
straight angle, whose region is empty. Without the second condition of `FallsShort`, an
empty region would fall short of every true angle; with it, every "less" certifies that its
mixed angle is not empty. The first condition of `FallsShort` follows from its third
(`MixedAngle.not_collinear_of_locallyLess`) and is kept so that the two words say alike that
the rectilineal angle is a true one.

Containment of whole regions would be the wrong condition, as Astra warned: a straight ray
that enters a circle leaves it again, so an acute angle is never wholly within the
semicircle, only near its vertex. Comparisons are made at one vertex with the straight arms
aligned, as Euclid makes them; a rectilineal angle is brought to the vertex by I.23.
Strictness asks for whole small circles, not single points: with single points, an arm or a
slit would count as an excess. A straight line holds no circle, so neither can happen
(`not_locallyLess_arm`, `not_locallyLess_slit`).

## 2. What is proved

**The census.** The namespace `Elements.MixedAngles` holds 117 theorems: the 109 written in
the file, and 8 that Lean generates for the type and the two `@[simp]` lemmas
(`MixedAngle.ofSegment.inj`, `.injEq` and `.sizeOf_spec`, the same three for `ofContact`,
and the `_simp_1` forms of `MixedAngle.region_ofSegment` and `region_ofContact`). It also
holds 14 definitions written in the file and the type `MixedAngle` with its two kinds.
`#print axioms`, run on every theorem, gives:

| Theorems | What `#print axioms` lists |
|---|---|
| 9 written: `LocallyEqual.symm`, `MixedAngle.Exceeds.nearVertexOpen`, `MixedAngle.region_ofContact`, `MixedAngle.region_ofSegment`, `NearVertexOpen.mono`, `NearVertexOpen.of_nearVertex`, `Prop16.outside_of_onRay`, `WithinAngle.comm`, `not_locallyWithin`; and 4 generated, the `inj` and `sizeOf_spec` of each kind | Nothing: they rest on no axiom |
| 1 written, `locallyLess_congr`; 4 generated, the `injEq` and `_simp_1` forms | Lean's own `propext` (and `Quot.sound` for `locallyLess_congr`) |
| The other 99 written | Axioms of `Elements/Foundations/`, 71 in all across them, every one in `Certificate/axioms.lock`; and some of Lean's own `propext`, `Classical.choice` and `Quot.sound` |
| 2 of those 99: `Prop31.any_greater_gt_right`, `Prop31.any_less_lt_right` | Postulate 5 among them, through III.31, whose proof uses I.32; no other theorem uses it |

`sorryAx` appears in none. Of the 109, 14 rest on III.16 or III.31, directly or through
another theorem, and so go after those propositions: `Prop16.semicircle_gt_acute`,
`Prop16.horn_lt_acute`, `Prop16.horn_wellFormed` (III.16's porism), the six placement
theorems of `Prop16`, `Segment.tangent_parts`, `Segment.exists_tangent` and
`Segment.congruent` (III.16), and the two `Prop31.any_` forms (III.31). The forms for any
angle or any straight line, and the placement theorems, are companions. The other 95 cite
neither.

The tables below name all 109 written theorems, by what they do. "Plain words" read the
Lean back, not Heath.

### The definitions

| Declaration | Plain words |
|---|---|
| `WithinAngle B A C P` | P is on C's side of AB and on B's side of AC. |
| `MixedAngle`, `.ofSegment`, `.ofContact` | A mixed angle: the angle of a segment, or the angle of contact (section 1). |
| `MixedAngle.vertex`, `MixedAngle.region` | Its vertex; its region (section 1). |
| `MixedAngle.WellFormed` | The named points give the angle Euclid draws (section 1). |
| `LocallyWithin`, `NearVertex`, `Surrounds`, `NearVertexOpen`, `LocallyLess`, `LocallyEqual` | Containment near A, points near A, a whole circle about P, whole circles near A, less near A, equal near A (section 1). |
| `MixedAngle.Exceeds m B C`, `MixedAngle.FallsShort m B C` | `m` is greater, or less, than the true angle BXC placed at its vertex X; a "less" also says that `m` comes as near X as we please. |
| `Prop16.Outside A E α`, `Prop16.FallsWithin A E α` | III.16's two parts at A: every point of the straight line AE but A is without the circle; every other straight line through A has a point within it. |

### Check (a): with straight boundaries, the comparison is the order of angles (18)

| Declaration | Plain words |
|---|---|
| `WithinAngle.locallyLess_iff` | For angles BAD, BAC with the common arm AB, D and C on one side of it: BAD is locally less than BAC exactly when `∠ B A D < ∠ B A C`. |
| `WithinAngle.locallyEqual_iff` | The same angles are locally equal exactly when `∠ B A D = ∠ B A C`. |
| `WithinAngle.locallyLess_of_lt` | The less angle is locally less; the excess is whole circles within the angle DAC. |
| `sameSideOf_of_angle_lt`, `WithinAngle.iff_angle_lt` | On one side of AC, R is within the angle CAT exactly when the angle CAR is less than the angle CAT. |
| `not_locallyLess_arm`, `not_locallyLess_slit` | An angle is not locally less than itself with an arm added; an angle with a ray taken out is not locally less than the angle. |
| `LocallyLess.irrefl`, `.asymm`, `.trans`, `.congr_left`, `.congr_right` | No angle is less than itself; not each of two is less than the other; less than a less is less; locally equal angles compare alike. |
| `LocallyEqual.refl`, `.symm`, `.trans`, `.of_iff`; `LocallyWithin.refl`, `.trans` | Local equality is an equivalence, and regions with the same points are locally equal. |

### Check (b): naming points and placement at one vertex do not matter (11)

| Declaration | Plain words |
|---|---|
| `WithinAngle.congr`, `WithinAngle.comm` | Other points of the same two rays name the same region; BAC and CAB have one region. |
| `WithinAngle.eq_of_angle_eq`, `WithinAngle.locallyLess_placement` | Equal angles placed along AB on one side have one region, so a rectilineal angle placed there compares with any region according to its size alone. |
| `MixedAngle.region_ofSegment`, `MixedAngle.region_ofContact` | The regions, unfolded. |
| `MixedAngle.ofSegment_congr_collinear`, `.ofSegment_congr` | Another point of the straight line AB, or another point on S's side, names the same region of a segment. |
| `MixedAngle.ofContact_congr` | Other points of the rays AE and AB name the same angle of contact. |
| `Prop16.horn_locallyEqual` | In III.16's figure, for every B′ on B's side of AE (every straight line AB′ from A into the circle), the angle of contact named by B′ is locally equal to the one named by the diameter. |
| `locallyLess_congr` | Regions with the same points compare alike. |

### Check (c): the angles compared are something (9)

| Declaration | Plain words |
|---|---|
| `Prop16.horn_nearVertex`, `Prop16.semicircle_nearVertex`, `Prop31.less_nearVertex`, `Segment.nearVertexOpen` | Every circle about the vertex holds a whole circle of the horn, of the angle of the semicircle, of the angle of the less segment, and of the angle of any segment drawn as `Segment.exceeds_iff` draws it. |
| `Prop16.horn_no_ray` | For every F within the angle EAB, the points of the ray AF near A are within the circle, so not in the horn: the horn is no rectilineal angle. |
| `MixedAngle.Exceeds.nearVertexOpen` | What exceeds a rectilineal angle is something. |
| `MixedAngle.not_exceeds_straight`, `.not_fallsShort_straight`, `.not_collinear_of_locallyLess` | No mixed angle exceeds or falls short of a straight angle; what a mixed angle is locally less than is a true angle. |

### The angles are Euclid's (4)

| Declaration | Plain words |
|---|---|
| `Prop16.semicircle_wellFormed`, `Prop16.horn_wellFormed` | The angle of the semicircle and the angle of contact of III.16 satisfy `WellFormed`; AE touches the circle by III.16's porism. |
| `Prop31.greater_wellFormed`, `Prop31.less_wellFormed` | The angles of the greater and the less segment of III.31 satisfy it. |

### The comparisons of III.16 (6)

In Heath's letters: the circle ABC about D, AB a diameter, AE at right angles to it at A.
The steps take III.16's two parts as hypotheses (`Prop16.Outside A E ABC` and
`Prop16.FallsWithin A E ABC`), so they do not cite III.16; the two forms for any acute angle
supply the parts from `BookIII.Prop16`.

| Declaration | Plain words |
|---|---|
| `Prop16.semicircle_gt` | For every F on E's side of AB with `∠ B A F < ∟`, the angle of the semicircle, `ofSegment A B ABC E`, exceeds the angle BAF. |
| `Prop16.horn_lt` | For every F on the circle's side of AE with `∠ E A F < ∟`, the remaining angle, `ofContact A E ABC B`, falls short of the angle EAF. |
| `Prop16.semicircle_lt_right` | The angle of the semicircle falls short of the right angle BAE. |
| `Prop16.remaining` | Within the right angle BAE, every point is in the angle of the semicircle, in the remaining angle, or on the circumference, and each of those is within the right angle. |
| `Prop16.semicircle_gt_acute`, `Prop16.horn_lt_acute` | Every acute rectilineal angle XYZ can be placed at A [I. 23], along AB on E's side or along AE towards the circle, and there the angle of the semicircle exceeds it, and the remaining angle falls short of it. Companions. |

So the angle of the semicircle lies strictly between every acute angle and the right angle,
and the horn strictly between nothing and every acute angle (`LocallyLess.trans` chains
them), for actual true rectilineal angles, quantified over all of them.

### The comparisons of III.31 (5)

In Heath's letters: the circle ABCD with diameter BC and centre E, A on it, BA carried
through to F. The steps take III.31's first part, that the angle BAC is right, as a
hypothesis.

| Declaration | Plain words |
|---|---|
| `Prop31.greater_gt_right` | The angle of the greater segment, `ofSegment A C ABCD B`, exceeds every right angle CAR placed along AC on B's side. |
| `Prop31.less_lt_right` | For D on the other side of AC from B, the angle of the less segment, `ofSegment A C ABCD D`, falls short of every right angle CAR placed along AC on D's side. |
| `Prop31.any_greater_gt_right`, `Prop31.any_less_lt_right` | For any straight line AC in a circle, not through the centre, at either end: the angle of the segment on the centre's side exceeds, and the one on the other side falls short of, every right angle placed along AC on its side. Companions: they take the right angle from III.31. |
| `Prop31.diameter_through` | The diameter through C ends at a point B other than A, on the centre's side of AC. |

The forms for any straight line are Astra's, "for every nondiameter chord, at either
endpoint"; Euclid's figure is the case where B is the far end of the diameter through C. The
less segment lies wholly within the right angle CAF, not only near A; the greater segment's
containment is local.

### Placement at another vertex (15)

| Declaration | Plain words |
|---|---|
| `Segment.exceeds_iff`, `Segment.fallsShort_iff` | Let A be on a circle, the ray AC run into it, AT satisfy III.16's two parts, and T and R be on S's side of AC. The angle of the segment exceeds the angle CAR exactly when R is within the angle CAT, and falls short of it exactly when R is not. |
| `Segment.congruent` | Two equal circles; in each a straight line, the two equal and neither through its centre; on each a segment, the two of one kind (the centre on the segment's side in both, or in neither); equal rectilineal angles CAR, C′A′R′ placed along the two straight lines, each on its segment's side. Then the angle of the one segment exceeds, or falls short of, the one angle exactly when the angle of the other does so of the other. |
| `Segment.exists_tangent`, `Segment.tangent_parts` | Let A and C be on a circle, the straight line AC not through the centre. At A a straight line AT can be drawn at right angles to the radius, on any given side of AC [I. 11]. A straight line at right angles to the radius at a point of the circle satisfies III.16's two parts. |
| `Segment.angle_tangent_of_sameSideOf`, `.angle_tangent_of_oppositeSidesOf` | The angle CAT is the angle OAC and a right angle, or, with the centre across AC, makes two right angles with it [I. 13]. |
| `Prop16.semicircle_exceeds_iff`, `.semicircle_fallsShort_iff`, `.semicircle_congruent` | For F on E's side of the diameter AB, the angle of the semicircle exceeds the angle BAF exactly when it is acute, and falls short of it exactly when it is not; so in any two circles, whatever their radii, the angles of the semicircles compare alike with equal angles placed along the diameters on their sides. |
| `Prop16.horn_fallsShort_iff`, `.horn_not_exceeds`, `.horn_congruent` | The angle of contact falls short of the true angle EAF exactly when F is on the circle's side of AE, and exceeds no rectilineal angle; so in any two circles the angles of contact compare alike with angles placed along AE on corresponding sides. |
| `WithinAngle.of_not_sameSideOf`, `oppositeSidesOf_of_not_sameSideOf` | If R, T are on one side of AC and R is not within the angle CAT, the angle CAT lies within the angle CAR; a point off a straight line not on one side is on the other. |

### The steps they share (41)

| Declaration | Plain words |
|---|---|
| `near_inside_of_angle` | If A, B, C are on or within a circle and BAC is a true angle, some circle about A holds no point of the angle, or of its arms, that is not within the circle. The radius is AN, N the foot of the perpendicular from A to BC [I. 12]. |
| `exists_near_across`, `near_across` | If the points of the ray AU near A are within a circle and every point of the ray AV is without it, every circle about A holds points, and whole circles, within the angle UAV on each side of the circumference. |
| `near_inside_of_ray`, `near_inside_of_onRay` | The points of a ray from a point of a circle towards a point on or within it are within the circle near A. |
| `Prop16.Outside.ne`, `Prop16.outside_of_onRay`, `Prop16.sameSideOf_of_inside`, `Prop16.inside_sameSideOf` | Under III.16's first part, AE has two ends, the points of the ray AE are without the circle, and the whole circle lies on one side of AE, B's side. |
| `Prop16.near_inside`, `Prop16.horn_within` | III.16's second part made local: for F within the angle EAB, near A the angle FAB and the ray AF are within the circle, and the horn lies within the angle EAF. |
| `surrounds_sameSideOf`, `surrounds_inside`, `surrounds_outside`, `WithinAngle.surrounds`, `Surrounds.and`, `Surrounds.not_line` | A point on one side of a straight line, within a circle, without it, or within an angle has a whole circle about it there; two such regions hold one together; a straight line holds no circle. |
| `NearVertexOpen.nearVertex`, `.of_nearVertex`, `.mono`, `.mono_near`, `WithinAngle.nearVertexOpen`, `not_locallyWithin` | Passing between points and whole circles near the vertex, and keeping only the neighbourhood of the vertex. |
| `WithinAngle.mono_left`, `.mono_right`, `.not_sameSideOf`, `.of_between`, `.exists_near` | Angles within angles (Triple incidence 1 and 3); a point between two arms is within the angle; every circle about the vertex holds a point within it. |
| `foot_nearest`, `len_lt_of_add_lt` | Every point of a straight line but the foot of the perpendicular from A is farther from A [I. 17, I. 19]; if OP, PQ together are less than a length, so is OQ, whether or not O, P, Q make a triangle [I. 20; System E, Between 6]. |
| `sameSideOf_self`, `onLine_of_collinear`, `Collinear.change_point`, `sameSideOf_congr_collinear`, `sameSideOf_congr_line`, `sameSideOf_congr_point`, `OnRay.of_sameRay`, `SameSideOf.of_between_line` | Sides, rays and straight lines: Book Zero's kind of fact. |
| `exists_circle_about`, `exists_onRay_inside`, `exists_inside_both` | Every point is a centre; a ray from the centre has points within the circle; of two circles about one point, one lies within the other. |

Two of these overlap statements that brief 0006 stages. `foot_nearest` takes the foot of
the perpendicular as I.12 gives it, which for A off BC is the staged `Foot A B C N`
(`Staging/Stage4/Foot.lean`); it is not stated through `Foot`, which is not yet approved
and whose existence and uniqueness are still stubs. `len_lt_of_add_lt` is I.20 with its
degenerate case, which `Staging/Stage3/Degenerate.lean` states as an equality,
`Prop20.collinear_iff`, still a stub; derived from it, it would rest on the stub. Condition 3
gives their homes.

### The routes

III.16's comparisons follow Euclid's idea, that no straight line can be interposed: the
straight line AF falls within the circle at a point G (III.16's second part), and near A the
whole angle between AG and the diameter is within the circle. What Euclid leaves unsaid is
"near A": how near is given by the perpendicular from A to GD, by I.12, I.17 and I.19. A
review record would mark this a `helper` for the local bound. III.31's comparisons are
Euclid's "manifest" containments, proved: the right angle BAC lies within the greater
segment near A, by the same local bound, and the less segment lies within the right angle
CAF everywhere (a point of it beyond AB would put a point within the circle on the straight
line AB but outside AB itself, against Circle 1 and Pasch 2 and 3).

That the excess holds whole circles, not single points, is not Euclid's to say; it is the
reading's. It costs one fact for each kind of region, that a point on one side of a
straight line, within a circle or without it has a whole circle about it there, proved with
I.12, I.17, I.19 and I.20.

Placement at another vertex goes by the tangent. The angle of a segment exceeds exactly the
angles CAR within the angle CAT, AT at right angles to the radius on the segment's side
(`Segment.exceeds_iff`); in equal circles, on equal straight lines, the triangles OAC and
O′A′C′ have their sides equal, so the angles OAC and O′A′C′ are equal [I. 8], and the angle
CAT is that angle and a right angle, or makes two right angles with it [I. 13]. No figure is
moved but the triangles of I.8.

## 3. What placement covers, and what is open

**Placement at another vertex.** It is proved as an invariance of the comparisons: equal
rectilineal angles, placed alike at the vertices of the angles of two segments of one kind,
on equal straight lines in equal circles, are compared alike (`Segment.congruent`); for the
angle of the semicircle and the angle of contact this holds in any two circles
(`Prop16.semicircle_congruent`, `Prop16.horn_congruent`). Its limits:

- `Segment.congruent` covers straight lines that do not pass through the centre; a diameter
  is covered by `Prop16.semicircle_congruent` alone.
- The segments must be of one kind, as a hypothesis. That cannot be dropped: on one straight
  line in one circle the greater segment's angle exceeds a right angle and the less
  segment's falls short of it (III.31).
- The rectilineal angles are placed along each straight line on its segment's side.
- `Prop16.horn_congruent` is stated in III.16's figure, with the branch named by the
  diameter.
- It is not a motion of a mixed angle, nor an equality between mixed angles at two vertices:
  the representation has no such word, since `LocallyEqual` compares regions at one vertex.
  The foundations move only triangles (superposition, in I.4 and I.8), and the proof moves
  nothing but the triangles of I.8.
- The staged placement of brief 0006 (`Staging/Stage3/Placement.lean`) is not used. It is
  assembled from cases still stubbed with `sorry`, and brief 0006 lets only III.24 and
  `Arcs.lean` cite it; the route by I.8 does without it.

The coordinator takes this form as the check of "congruent placement" that Astra asked for
and #56 lists ([decisions](../briefs/0002-decisions.md), 18 October 2026, "Mixed angles: the
prototype approved, its proofs kept in Staging"). III.16 and III.31 make every comparison at
one vertex, so they need nothing more.

**The general angle of contact.** `Prop16.horn_locallyEqual` is proved in III.16's figure,
where AE is at right angles to the diameter AB. For a straight line given only as touching
the circle (`Touches A E α`), that the angle does not depend on which straight line into the
circle names its branch is not proved: the route would draw the diameter through A and show
AE at right angles to it, which is III.18, later than III.16. III.16 and III.31 do not need
it: III.16's angle of contact is drawn at right angles to the diameter, and III.31 has none.

**No arithmetic of mixed angles.** There is no addition, no multiple and no ratio of mixed
angles, and no law that every two are comparable. The horn is something (check (c)) and less
than every acute angle, so no Archimedean law could hold of both kinds together; nothing
here asserts one, as Astra advised (Heath, vol. 2, p. 40).

**Where the proofs live.** Other staged files hold statements with `sorry`. This file holds
proofs because it tests a representation, as WORKFLOW, section 2, asks of each new
foundation ("Prototype each new foundation"). The coordinator approved the prototype on 18
October, and decided that its proofs stay in `Staging/Stage4b/MixedAngles.lean` until #57
decides their move into `Elements/` ([decisions](../briefs/0002-decisions.md), 18 October
2026, "Mixed angles: the prototype approved, its proofs kept in Staging"). The rule that
allows it is WORKFLOW, section 2, "What proofs `Staging/` may hold", which brief 0006's pull
request adds: `Staging/` may hold the proofs of a prototype the coordinator has approved.

**The namespace.** While staged, every declaration is in `Elements.MixedAngles`, so that
nothing enters a proposition's namespace before #57 is decided. On adoption the companions
go into `Elements.BookIII`, and the rest where condition 3 says.

## 4. Is an axiom needed?

No. Every fact used is already in the foundations or proved from them: the postulates,
Definition I.15, System E's rules for sides, betweenness, circles, lengths and angles
(among them Circle 1 to 3, Pasch 2 to 4, Between 6, Triple incidence 1 to 3, Diagram-angle 3,
Intersection 1, and Intersections 4 and 5), the common notions, and I.8, I.11, I.12, I.13,
I.17, I.19, I.20, I.23, III.16 and III.31. The census of section 2 lists what each theorem
rests on: 71 axioms of `Elements/Foundations/`, all in `Certificate/axioms.lock`, besides
Lean's own, and no `sorryAx`. Nothing goes to the owner as an axiom.

## 5. Recommendation for #57

**Go for full, for III.16 and III.31.** What supports it is proved: the comparisons of both
propositions, for every rectilineal angle Euclid's enunciations speak of, through the mixed
angle's own vertex, with every "less" certifying that its mixed angle is not empty; the
checks of the reading; that the angles are Euclid's; and placement in the form of section 3.
What is not proved is named in section 3, and neither proposition needs it. The conditions:

1. **The words.** `WithinAngle`, `MixedAngle` with its two kinds, `vertex`, `region`,
   `WellFormed`, `LocallyWithin`, `Surrounds`, `NearVertexOpen`, `LocallyLess`,
   `LocallyEqual`, `Exceeds` and `FallsShort` move to
   `Elements/Foundations/DefinitionsIII.lean`, with the coordinator's approval,
   `check_fidelity.py --write-lock`, a decisions entry, and the model lock and
   `tests/model/MODEL.md` read again (WORKFLOW, section 2, item 1). They are definitions, not
   axioms, and add nothing to what is assumed. `NearVertex` may go with them or stay a step.
   `Prop16.Outside` and `Prop16.FallsWithin` go with them, or are written out in the steps'
   hypotheses, as the coordinator prefers. The docstrings of the declarations that move
   carry no issue numbers and no check labels (done in this revision); the longer notes are
   cut to STYLE's sentence or two as they move.
2. **The statements.** III.16 gains its two comparisons and III.31 its two, as restatements
   of `theorem Prop16` and `theorem Prop31` (staged as `Elements.BookIII.Staging.Prop16` and
   `.Prop31`), so that Lean stands under Heath's angle sentences. The conjuncts are the
   conclusions of `Prop16.semicircle_gt` and `Prop16.horn_lt` quantified over F, and of
   `Prop31.greater_gt_right` and `Prop31.less_lt_right` over R, written through the object,
   as `(ofSegment A B ABC E).Exceeds B F`. The non-emptiness of the horn and of the less
   segment is part of `FallsShort`, so these conclusions carry it, not the record. The
   restated proofs prove the existing parts first (III.16's two parts, III.31's right angle)
   and pass them to the steps. #57 takes these steps over rather than writing them again.
   The general forms (any acute angle by I.23; any straight line not through the centre) and
   the placement theorems are companions.
3. **The shared steps.** Each goes after the propositions it rests on, so nothing that
   cites Book I goes into the foundations.
   - `len_lt_of_add_lt` (I.20) goes beside `Prop20.collinear_iff` in
     `Elements/BookI/HelpersTriangles.lean`, which brief 0006 adds.
   - What rests on I.12, I.17, I.19 or I.20 goes to `Elements/BookIII/Squares.lean`, with
     Book III's other steps that cite Book I: `foot_nearest` (beside `Foot.exists` and
     `Foot.unique`, and stated through `Foot` if `Foot` is adopted first),
     `near_inside_of_angle`, `near_across`, the `surrounds_` facts, `WithinAngle.surrounds`
     and `WithinAngle.nearVertexOpen`, `NearVertexOpen.mono_near`, and the checks and order
     laws that use them: `WithinAngle.locallyLess_of_lt`, `.locallyLess_iff`,
     `.locallyEqual_iff`, `LocallyLess.trans`, `.congr_left` and `.congr_right`.
   - What cites no proposition goes to Book Zero, or beside the words: the facts on sides,
     rays and circles, the other `WithinAngle`, `Surrounds` and `NearVertexOpen` facts,
     `exists_near_across`, `near_inside_of_ray`, `near_inside_of_onRay`, and the other
     checks and laws. The `Prop16.` and `Prop31.` steps are not among them, even where they
     cite no proposition: the next bullet governs them.
   - The `Prop16.` and `Prop31.` steps are helpers for one proposition, and go before it, in
     its file (FORMALIZATION, section 6); among them `Prop16.Outside.ne`,
     `Prop16.outside_of_onRay` and `Prop16.sameSideOf_of_inside`, which cite no proposition.
     The `Segment.` steps that do not cite III.16 take III.16's first part, or both, as
     hypotheses, as the `Prop16.` steps do, and use those three, so they go in III.16's file
     after them: `Segment.exceeds_iff`, `.fallsShort_iff` and `.nearVertexOpen`, which rest
     on I.12, I.17, I.19 and I.20; `.angle_tangent_of_oppositeSidesOf`, which cites I.13;
     and `.angle_tangent_of_sameSideOf`, which cites no proposition. These homes follow from
     the choice of this bullet, and depart from the list of FORMALIZATION, section 6, for
     shared steps, under which the four that rest on Book I would go to `Squares.lean` and
     the fifth to Book Zero. The theorems that cite III.16 or III.31 (section 2) go after
     those propositions; `Segment.congruent` also cites I.8, I.11 and I.13.
4. **The records.** III.16 and III.31 drop `mixed-angles-omitted` and take a new tag, defined
   in `review/terms.toml` before use, carrying Astra's wording: the comparisons use local
   containment of curved angular regions, and no general arithmetic or ratio theory of mixed
   angles is claimed. The passage for the local bound is a `helper`.
5. **The challenge.** As with every new representation, readers who did not write these
   definitions challenge them before approval. This revision answers the re-challenge and
   two reviews (appendix), and a verifier who did not write it has read it at `dfb9291` and
   handed back at `4705a9c` with a fix of its own, checking the census, every claim of
   "proved" and the homes of condition 3 against the Lean. Its findings are answered in the
   appendix; the changes since are editorial, and the record of the coordinator's
   decisions.
6. **Where the proofs live.** Recorded: the coordinator's decision of section 3 is on the
   [decisions](../briefs/0002-decisions.md) page, 18 October 2026. It rests on WORKFLOW,
   section 2, "What proofs `Staging/` may hold", which brief 0006's pull request adds.

## Appendix: the challenges and reviews, and what was done

Every finding below was answered with a change, in
`Staging/Stage4b/MixedAngles.lean` or here, unless its row says otherwise.

### The first challenge on #56

| Finding | Done |
|---|---|
| *Material.* The strictness of `LocallyLess` counted edge points as excess: an angle was "less" than itself with an arm added, or than a slit angle; in III.31 and III.16 the excess was already met by points of an arm | `Surrounds` and `NearVertexOpen` added, and `LocallyLess` asks for whole circles of excess. Each kind of region is shown to hold a whole circle about each of its points, with `foot_nearest` and `len_lt_of_add_lt` (I.12, I.17, I.19, I.20). The reader's two cases fail: `not_locallyLess_arm`, `not_locallyLess_slit` |
| *Material.* Check (b) only partly done for the angle of contact | `Prop16.horn_locallyEqual`, for every B′ on B's side of AE, in III.16's figure. The general form is open (section 3) |
| *Editorial.* The comparison not tied to the mixed angle's vertex | `MixedAngle.Exceeds` and `MixedAngle.FallsShort`, through `m.vertex` |
| *Editorial.* No order laws | `LocallyLess.irrefl`, `.asymm`, `.trans`, `.congr_left`, `.congr_right`; `LocallyEqual` and `LocallyWithin` laws; `NearVertexOpen.mono_near` |
| *Editorial.* Heath's "remaining angle" had no lemma | `Prop16.remaining` |
| *Editorial.* The docstring said B is on the circle and AE touches it; the lemmas assume neither | Reworded; AE touches by III.16's porism, now proved in `Prop16.horn_wellFormed` |
| *Editorial.* The forms "ready to be conjuncts" cited the theorems they would belong to | The `Prop16.` steps take III.16's two parts as hypotheses (now `Prop16.Outside` and `Prop16.FallsWithin`), and `greater_gt_right` and `less_lt_right` take the right angle BAC; only companions cite III.16 and III.31 |

### The re-challenge

| Finding | Done |
|---|---|
| *Material.* `FallsShort` is satisfied by an empty region, and III.31's less segment had no non-emptiness check | `FallsShort` now includes `NearVertexOpen m.vertex m.region`, so every "less" certifies its own angle. `Prop31.less_nearVertex` proves it for the less segment, and `less_lt_right` and `any_less_lt_right` use it; `Prop16.semicircle_nearVertex` added beside `horn_nearVertex` |
| *Material.* `Exceeds` and `FallsShort` accepted a straight angle: the semicircle "exceeded" the straight angle BAB′ | Both require that the rectilineal angle be a true one. `MixedAngle.not_exceeds_straight`, `not_fallsShort_straight` and `Exceeds.nearVertexOpen` added; every comparison proved again |
| *Editorial.* Condition 2 let `horn_nearVertex` go "in the record" | No longer needed: `FallsShort` carries the non-emptiness (condition 2) |
| *Editorial.* `ofSegment`'s region depends on the line AB, but a comparison reads the ray; placement along the arm is not enforced | The `MixedAngle` and `Exceeds` docstrings say that B names the ray into the circle and how III.16 and III.31 place the rectilineal angle; `MixedAngle.ofSegment_congr_collinear` added |
| *Editorial.* `MixedAngle` has no well-formedness condition | `MixedAngle.WellFormed`, with the four `_wellFormed` theorems |
| *Editorial.* "Every check Astra asked for is proved" overclaims | The summary now says what is proved and what is not |

### The reviews of the first revision

| Finding | Done |
|---|---|
| *Standards, material.* Proofs in `Staging/`, against the rule that staged files hold statements with `sorry` | Not changed in the file: the coordinator decides (section 3, condition 6). The module docstring now cites the paragraph of WORKFLOW, section 2, that asks for prototypes, which reads the same before and after that section's revision |
| *Standards, material.* Heath's letters in backticks in the notes; hypotheses given by local names | Letters plain; hypotheses said in words |
| *Standards, material.* `h1` and `h2` repeated as a clump in many signatures | III.16's parts are written once, as `Prop16.Outside` and `Prop16.FallsWithin`, and the hypotheses are named `hAE_out` and `hAE_in` |
| *Standards, editorial.* "chord" for a straight line | Removed; `chord_greater_gt_right` and `chord_less_lt_right` renamed `any_greater_gt_right` and `any_less_lt_right` |
| *Standards, editorial.* The body of `LocallyWithin` written out in six places | Stated through `LocallyWithin` |
| *Standards, editorial.* Overlaps with the staged `Foot` and `Prop20.collinear_iff` | Not reused, for the reasons in section 2 and in the file's section on small facts; their homes are in condition 3 |
| *Standards, editorial.* Mysterious names; companions not in `Elements.BookIII` | Renamed: `Collinear.change_point`, `OnRay.of_sameRay`, `SameSideOf.of_between_line`, `WithinAngle.mono_left` and `mono_right`, and the locals `hEE'_AB` and `hEE'_AB'`. The namespace stays while staged (section 3) |
| *Standards, editorial.* Issue numbers and check labels in the docstrings of declarations meant to move; long notes | No declaration docstring carries either now; the module docstring keeps its issue numbers, since it does not move. The long notes are cut on the move (condition 1) |
| *Standards, editorial.* "(Heath, volume II, p. 40, on Proclus)" | Written in STYLE's form, "(Heath, vol. 2, p. 40)" |
| *Spec, material.* Congruent placement not proved, yet "go for full" | Proved in the form of section 3, with its limits stated |
| *Spec, material.* "Every check is proved" contradicts section 3 | Corrected in the summary. The comment on #56 that says so is outside the repository, for the coordinator |
| *Spec, editorial.* The comment on #56 gives 47 theorems | For the coordinator; the census is in section 2 |
| *Spec, editorial.* `horn_locallyEqual` proved only in III.16's figure | Every claim of it is now scoped to that figure (section 3) |
| *Spec, editorial.* The companions are #57's deliverable | #57 takes them over (condition 2) |

### The verification of the second revision's first draft

| Finding | Done |
|---|---|
| *Blocking.* The report was not rewritten | This report |
| *Blocking.* Nothing was committed | The Lean is committed by itself first, then this report with the remaining changes |
| *Material.* The module docstring left out two hypotheses of `Segment.congruent`: the segments of one kind, and the angles placed on the segments' sides | The docstring states both, and why the kind cannot be dropped. `Segment.congruent` was also strengthened: it draws the straight lines at right angles to the radii itself (`Segment.exists_tangent`, I.11), so it no longer asks for them |
| *Editorial.* `FallsShort`'s docstring gave a wrong reason for its first condition | It now says the condition follows from the third (`MixedAngle.not_collinear_of_locallyLess`, proved) and is kept so that both words say the rectilineal angle is true |
| *Editorial.* The independence of the angle of contact claimed beyond III.16's figure | Scoped in the `MixedAngle`, `ofContact_congr` and module docstrings |
| *Editorial.* The WORKFLOW citation true only after a later revision | Rephrased so that it is true before and after |
| *Editorial.* Issue numbers and check labels; the overlaps; local names `h1 h2 h3` | Done as in the rows above; the locals renamed off the letters |

### The verification of the second revision

A verifier who did not write it read the second revision, fixed one finding itself, and
handed back at `4705a9c`.

| Finding | Done |
|---|---|
| *Material, for the coordinator.* The proofs sit in `Staging/`, and the rule on main has staged files hold statements with `sorry` | The coordinator's decision is recorded (section 3, condition 6). Condition 5 now counts this verification |
| *Editorial.* `surrounds_inside` and `surrounds_outside` named their rules "Intersection 5" and "Intersection 4", which are not the rules they use, and section 4 merged two families of rules | Fixed by the verifier: the docstrings now name "Intersections 5" and "Intersections 4", the labels of the construction rules the proofs use (`line_circle_beyond`, `line_circle_between`), and section 4 reads "Intersection 1, and Intersections 4 and 5". `exists_near_across`'s "Circles 2 and 3", a family the foundations do not have, now reads "Circle 2 and 3" |
| *Editorial.* Condition 3 gave no home to five `Segment.` steps | Added: they go in III.16's file, after the `Prop16.` steps they use. Not `Squares.lean`, as proposed: III.16's file imports it, and these steps use `Prop16.` steps, which condition 3 puts in III.16's file, those that cite no proposition included. Condition 3 says that this departs from FORMALIZATION, section 6's list for shared steps |
| *Editorial.* The row for `Segment.exists_tangent` left out that C is on the circle and that AC does not pass through the centre | Both stated |
| *Editorial.* `Staging.lean`'s module doc does not list `Stage4b/`; the comment on #56 gives 47 theorems | `Stage4b/` is listed. The comment on #56 is outside the repository, for the coordinator; the census is in section 2 (117 theorems, 109 written and 8 generated) |
| *Editorial.* The page of "(Heath, vol. 2, p. 40)" was not checked against the scan | Checked by the verifier: in the archive.org text of the scan, the running head "40 BOOK III [III. 16" stands above Proclus's argument on the angle of contact. No change |
| *Editorial.* Every finding of the previous verification, and the census, the closure and the tables, read against the Lean | Resolved, and no defect found |
| *Editorial, found in answering these.* The revision note said that the angle of contact does not depend on its naming line, without "in III.16's figure" | Scoped, as everywhere else |

### The review of the commit that recorded the decision

Readers who did not write it reviewed `eb5c88b`, against the guides and against #56.

| Finding | Done |
|---|---|
| *Material.* The decisions page put words in quotation marks as the owner's that the owner did not write | The quotation marks are gone: the entry says what the owner approved, and links the approval on #51 |
| *Material.* The decision rests on the paragraph "What proofs `Staging/` may hold", which only brief 0006's pull request adds | No change to the text: the prototype's pull request comes after brief 0006's, and says so |
| *Editorial.* `Staging.lean`'s module doc still speaks of brief 0005's stages and of statements with `sorry` | Left to brief 0006's change to those lines, which rewrites them. The `Stage4b/` line is widened when brief 0007's staged statements join the prototype there |
| *Editorial.* Condition 3 left open whether a `Prop16.` step that cites no proposition goes to Book Zero or to III.16's file, and the homes of the five `Segment.` steps rest on that choice | Condition 3 now says that `Prop16.` and `Prop31.` steps go in their propositions' files, and that the `Segment.` homes follow from it and depart from FORMALIZATION, section 6's list for shared steps |
| *Editorial.* Three places put the verification at `4705a9c`, though the verifier read `dfb9291` and `4705a9c` is its own fix | Reworded in all three: read `dfb9291`, handed back at `4705a9c` with a fix of its own |
| *Editorial.* The report named the branch, which is deleted on landing | The branch is no longer named; the link to the Lean is kept |
| *Spec, editorial.* Section 3 left to Astra and the coordinator whether the proved form answers "congruent placement", and the decision said nothing on it | The coordinator takes the proved form as that check: one sentence in the decisions entry, and section 3 says so |
