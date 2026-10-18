# Mixed angles: a prototype for III.16 and III.31

Issue #56, for the decision on issue #57. The Lean is
[`Staging/Stage4b/MixedAngles.lean`](../../Staging/Stage4b/MixedAngles.lean), on the branch
`lean/mixed-angle-prototype`. It follows the design in Astra's answer on issue #51, whose
III.16 and III.31 parts it implements; thanks to Astra for a design that turned out to need
no new assumption at all.

*Revised 18 October 2026, after the challenge on #56: the strict comparison now asks for
whole small circles of excess, not single points; the angle of contact is shown not to
depend on the straight line that names its branch; the comparisons are stated through the
mixed angle's own vertex; order laws and Heath's "remaining angle" are added; and the steps
take III.16's parts and III.31's right angle as hypotheses, so that restated theorems can
use them. The appendix lists each finding and what was done.*

**In short.** The representation Astra proposed works in plain Lean on the existing
foundations. Every check Astra asked for is proved, and so are the comparisons of III.16
and III.31 themselves, for every acute angle (III.16), every right angle placed along the
chord, and every straight line in the circle that does not pass through the centre
(III.31). There is no `sorry` in the file and no new axiom: every declaration rests only on
the postulates, Definition I.15, the System E rules already in `Elements/Foundations/`,
and earlier propositions (I.12, I.17, I.19, I.20, I.23, and III.16 and III.31 for the
companions only). The recommendation for #57 is **go**, on the conditions in the last
section.

## 1. The representation

**Regions.** A region is a predicate on points, `Point → Prop`.

- **A rectilineal angle** `BAC` has the region `WithinAngle B A C`: the points on `C`'s side
  of the straight line `AB` and on `B`'s side of `AC`. This is the phrase Book Zero already
  uses ("within the angle"), made a definition. Its arms are not in it.
- **A mixed angle** is a geometric object of its own, `MixedAngle`, recorded by its vertex,
  its straight arm, its circle, and the branch and side of the circumference that bound it.
  Euclid uses two kinds, one for each side of the circumference:
  - `MixedAngle.ofSegment A B α S`, **the angle of a segment** (Definition III.7): the
    straight arm is the ray `AB`; the branch is the one on `S`'s side of `AB`; the side is
    within the circle. Its region is the points within `α` on `S`'s side of `AB`, so it
    depends only on the straight line `AB`, and `B` may be any point of the ray. In III.31
    `B` is the other end of the chord; for the angle of the semicircle in III.16 it is a
    point of the diameter beyond the centre (the diameter produced if need be).
  - `MixedAngle.ofContact A E α B`, **the angle of contact**, III.16's remaining angle, the
    horn-like angle: the straight arm is the ray `AE`; the branch is the one on `E`'s side
    of a straight line `AB` into the circle; the side is without. Its region is the points
    without `α` and within the angle `EAB`. Which straight line into the circle names the
    branch does not matter near `A` (`Prop16.horn_locallyEqual`, check (b)).

  Nothing about the kinds is assumed when they are formed; the theorems that use them say
  what the figure is. In III.16 they are `BookIII.Prop16`'s hypotheses: `A` on the circle,
  `D` the centre, `B` beyond `D` on the straight line `AD` (`Between A D B`, so `B` need not
  be on the circle), and `AE` at right angles to `AB`. `AE` then touches the circle by
  III.16's porism; `Touches` is not assumed. In III.31, `A`, `B` and `C` are on the circle.
  A segment's region runs on far from `A` (it is the whole segment), and the horn's region
  includes points beyond the circle far from `A`; neither matters, since only the
  neighbourhood of the vertex enters a comparison.

**Comparison by local containment.** "Near the vertex" is said with circles about `A`, as
Euclid would draw them, and no numbers:

- `LocallyWithin A R S`: some circle about `A` holds no point of `R` that is not in `S`;
- `Surrounds R P`: some circle about `P` holds only points of `R`;
- `NearVertexOpen A R`: every circle about `A`, however small, holds a point `P` that `R`
  surrounds;
- `LocallyLess A R S`: `LocallyWithin A R S`, and `NearVertexOpen A` of the points of `S`
  not in `R` (strictness);
- `LocallyEqual A R S`: each locally within the other;
- `MixedAngle.Exceeds m B C` and `MixedAngle.FallsShort m B C`: the rectilineal angle `BXC`,
  where `X` is the vertex of `m`, is locally less than `m`, or `m` than it. The vertex is the
  mixed angle's own, so a comparison cannot be made at another point.

Containment of whole regions would be the wrong condition, as Astra warned: a straight ray
that enters a circle leaves it again, so an acute angle is never wholly within the
semicircle, only near its vertex. Comparisons are made at one vertex with the straight arms
aligned, as Euclid makes them; a rectilineal angle is brought to the vertex by I.23.

Strictness asks for whole small circles, not single points. With single points, an arm or a
slit would count as an excess: an angle would be "less" than itself with one arm added, and
the excess of the greater segment over the right angle in III.31 would already be met by
the points of the arm `AB`. A straight line holds no circle, so neither can happen now
(`not_locallyLess_arm`, `not_locallyLess_slit`).

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
| `Surrounds R P` | Some circle about `P` holds only points of `R`. |
| `NearVertexOpen A R` | Every circle about `A` holds a point about which some circle holds only points of `R`. |
| `LocallyLess A R S` | Near `A`, `R` is within `S`, and the points of `S` outside `R` hold whole circles as near `A` as we please. |
| `LocallyEqual A R S` | Near `A`, each of `R`, `S` is within the other. |
| `MixedAngle.Exceeds m B C` | The angle `BXC`, `X` the vertex of `m`, is locally less than `m` at `X`. |
| `MixedAngle.FallsShort m B C` | `m` is locally less than the angle `BXC` at its vertex `X`. |

### Check (a): with straight boundaries, the comparison is the order of angles

| Declaration | Plain words |
|---|---|
| `WithinAngle.locallyLess_iff` | For angles `BAD`, `BAC` with the common arm `AB`, `D` and `C` on one side of it: `BAD` is locally less than `BAC` exactly when `∠ B A D < ∠ B A C`. |
| `WithinAngle.locallyEqual_iff` | The same angles are locally equal exactly when `∠ B A D = ∠ B A C`. |
| `WithinAngle.locallyLess_of_lt` | The less angle is locally less; the excess is whole circles within the angle `DAC`. |
| `sameSideOf_of_angle_lt` | On one side of `AB`, the less angle lies within the greater: `D` is on `B`'s side of `AC`. |
| `not_locallyLess_arm` | A true angle `BAC` is not locally less than itself with the arm `AC` added. |
| `not_locallyLess_slit` | An angle with a ray `AD` taken out, `D` within it, is not locally less than the angle. |
| `LocallyLess.irrefl`, `.asymm`, `.trans` | No angle is less than itself; not each of two is less than the other; less than a less is less. |
| `LocallyLess.congr_left`, `.congr_right` | Locally equal angles compare alike, on either side. |
| `LocallyEqual.refl`, `.symm`, `.trans`, `.of_iff`; `LocallyWithin.refl`, `.trans` | Local equality is an equivalence, and regions with the same points are locally equal. |

### Check (b): naming points and placement do not matter

| Declaration | Plain words |
|---|---|
| `WithinAngle.congr` | Other points of the same two rays name the same region. |
| `WithinAngle.comm` | `BAC` and `CAB` have one region. |
| `WithinAngle.eq_of_angle_eq` | Equal angles placed along `AB` on one side have one region. |
| `WithinAngle.locallyLess_placement` | So a rectilineal angle placed along `AB` compares with any region according to its size alone, whichever equal angle is placed. |
| `MixedAngle.ofSegment_congr` | Another point of the ray `AB`, or another point on `S`'s side, names the same angle of a segment. |
| `MixedAngle.ofContact_congr` | Other points of the rays `AE` and `AB` name the same angle of contact. |
| `Prop16.horn_locallyEqual` | For every `B'` on `B`'s side of `AE`, that is, any straight line `AB'` from `A` into the circle, the angle of contact named by `B'` is locally equal to the one named by the diameter. |
| `locallyLess_congr` | Regions with the same points compare alike. |

### Check (c): the horn is not an empty angle, and not a rectilineal one

| Declaration | Plain words |
|---|---|
| `Prop16.horn_nearVertex` | Every circle about `A` holds a whole circle of the remaining angle of III.16: within the angle `EAB` and without the circle. |
| `Prop16.horn_no_ray` | For every point `F` within the angle `EAB`, the points of the ray `AF` near `A` are not in the horn: they are within the circle. |

Together these keep both of Astra's pitfalls in view: the horn holds whole circles as near
the vertex as we please, so the upper bounds below are not met by an empty region or an
edge; and no straight ray from the vertex runs within it, so it cannot be replaced by a
rectilineal angle or by the rays that enter it.

### Check (d): the comparisons of III.16

In Heath's letters: the circle `ABC` about `D`, `AB` a diameter, `AE` at right angles to it
at `A`. The hypotheses are those of `BookIII.Prop16`, with its two parts as `h1` (every
point of `AE` but `A` is without the circle) and `h2` (every other straight line through
`A` falls within it), so that the lemmas do not cite III.16.

| Declaration | Plain words |
|---|---|
| `Prop16.semicircle_gt` | For every `F` on `E`'s side of `AB` with `∠ B A F < ∟`, the angle of the semicircle, `ofSegment A B ABC E`, exceeds the angle `BAF`. |
| `Prop16.horn_lt` | For every `F` on the circle's side of `AE` with `∠ E A F < ∟`, the remaining angle, `ofContact A E ABC B`, falls short of the angle `EAF`. |
| `Prop16.semicircle_lt_right` | The angle of the semicircle falls short of the right angle `BAE`. |
| `Prop16.remaining` | Within the right angle `BAE`, every point is in the angle of the semicircle, in the remaining angle, or on the circumference, and each of those is within the right angle: the remaining angle is what is left of the right angle. |
| `Prop16.semicircle_gt_acute` | Every acute rectilineal angle `XYZ` can be placed at `A` along `AB` on `E`'s side [I. 23], and the angle of the semicircle exceeds it there. A companion: it supplies `h1` and `h2` from III.16. |
| `Prop16.horn_lt_acute` | Every acute rectilineal angle `XYZ` can be placed at `A` along `AE` towards the circle [I. 23], and the remaining angle falls short of it there. A companion, likewise. |

So the angle of the semicircle lies strictly between every acute angle and the right angle,
and the horn strictly between nothing and every acute angle (`LocallyLess.trans` chains
them): the comparisons say what Heath's enunciation says, for actual nondegenerate
rectilineal angles, quantified over all of them.

### The comparisons of III.31

In Heath's letters: the circle `ABCD` with diameter `BC` and centre `E`, `A` on it, `BA`
carried through to `F`. The hypotheses are those of `BookIII.Prop31`, with its first part,
that the angle `BAC` is right, as a hypothesis.

| Declaration | Plain words |
|---|---|
| `Prop31.greater_gt_right` | The angle of the greater segment, `ofSegment A C ABCD B`, exceeds every right angle `CAR` placed along `AC` on `B`'s side. |
| `Prop31.less_lt_right` | For `D` on the other side of `AC` from `B`, the angle of the less segment, `ofSegment A C ABCD D`, falls short of every right angle `CAR` placed along `AC` on `D`'s side. |
| `Prop31.chord_greater_gt_right` | For any straight line `AC` in a circle about `E`, not through the centre, at either end: the angle of the segment on the centre's side exceeds every right angle placed along `AC` on that side. A companion: it takes the right angle from III.31. |
| `Prop31.chord_less_lt_right` | The same straight line: the angle of the segment on the side away from the centre falls short of every right angle placed along `AC` on that side. A companion, likewise. |
| `Prop31.diameter_through` | The diameter through `C` ends at a point `B` other than `A`, on the centre's side of `AC`. |

The chord forms are Astra's, "for every nondiameter chord, at either endpoint"; Euclid's
figure is the case where `B` is the far end of the diameter through `C`. The less segment
turns out to lie wholly within the right angle `CAF`, not only near `A`; the greater
segment's containment is local.

### The steps they share

| Declaration | Plain words |
|---|---|
| `near_inside_of_angle` | If `A`, `B`, `C` are on or within a circle and `BAC` is a true angle, some circle about `A` holds no point of the angle, or of its arms, that is not within the circle. The radius is `AN`, `N` the foot of the perpendicular from `A` to `BC` [I. 12]. |
| `foot_nearest` | Every point of a straight line other than the foot of the perpendicular from `A` is farther from `A` [I. 17, I. 19]. |
| `len_lt_of_add_lt` | If `OP`, `PQ` together are less than a length, so is `OQ`, whether or not `O`, `P`, `Q` make a triangle [I. 20; System E, Between 6]. |
| `surrounds_sameSideOf`, `surrounds_inside`, `surrounds_outside`, `WithinAngle.surrounds` | A point on one side of a straight line, within a circle, without it, or within an angle has a whole circle about it there. |
| `Surrounds.and`, `Surrounds.not_line` | Two regions that each hold a circle about `P` hold one together; a straight line holds no circle. |
| `NearVertexOpen.nearVertex`, `.of_nearVertex`, `.mono`, `.mono_near`, `WithinAngle.nearVertexOpen` | Passing between points and whole circles near the vertex, and keeping only the neighbourhood of the vertex. |
| `exists_near_across`, `near_across` | If the points of the ray `AU` near `A` are within a circle and every point of the ray `AV` is without it, every circle about `A` holds points, and whole circles, within the angle `UAV` on each side of the circumference. |
| `near_inside_of_ray` | The points of a ray from a point of a circle towards a point on or within it are within the circle near `A`. |
| `Prop16.outside_of_onRay` | III.16's first part, for the points of the ray `AE`. |
| `Prop16.inside_sameSideOf` | The whole circle lies on `B`'s side of `AE`. |
| `Prop16.near_inside` | III.16's second part made local: for `F` within the angle `EAB`, near `A` the angle `FAB` and the ray `AF` lie within the circle. |
| `Prop16.horn_within` | For `F` within the angle `EAB`, near `A` the horn lies within the angle `EAF`. |
| `WithinAngle.mono`, `.mono'`, `.not_sameSideOf`, `.of_between`, `.exists_near` | Angles within angles (Triple incidence 1 and 3), a point between two arms is within the angle, and every circle about the vertex holds a point within it. |
| `sameSideOf_self`, `onLine_of_collinear`, `collinear_of_collinear`, `sameSideOf_congr_collinear`, `sameSideOf_congr_line`, `sameSideOf_congr_point`, `onRay_trans`, `sameSideOf_of_between` | Sides, rays and straight lines: Book Zero's kind of fact. |
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

That the excess holds whole circles, not single points, is not Euclid's to say; it is the
reading's. It costs one fact for each kind of region, that a point on one side of a
straight line, within a circle or without it has a whole circle about it there, proved with
I.12, I.17, I.19 and I.20.

No step of III.16 or III.31 cites III.16 or III.31: they take III.16's two parts, and
III.31's right angle, as hypotheses. Only the companions cite them: `semicircle_gt_acute`
and `horn_lt_acute` cite III.16, and `chord_greater_gt_right` and `chord_less_lt_right`
cite III.31. Those two rest on Postulate 5, through III.31's own proof (I.32), as III.31
already does; nothing else in the file does.

## 3. What is left open

The first version proved every lemma as first stated. The challenge on #56 found the
strictness too weak and three gaps in the checks; all were closed (appendix), and the new
statements were proved as stated too. These questions are open, and belong to the decision
on #57:

- **Congruent placement at another vertex.** Check (b) covers naming points, the straight
  line that names the horn's branch, and equal rectilineal angles placed at one vertex. That
  a mixed angle is unchanged when the whole figure is laid down elsewhere (the angle of a
  semicircle in one circle equal to that in an equal circle) is not stated: the foundations
  move only triangles (superposition, in I.4 and I.8 alone). III.16 and III.31 do not need
  it, since every comparison is made at one vertex.
- **The general angle of contact.** `Prop16.horn_locallyEqual` is proved in III.16's figure.
  The same for any straight line touching any circle, with no diameter drawn, belongs with
  the move to the foundations; it would follow the same route, with the diameter through the
  point of contact drawn first.
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
Definition I.15, System E's rules for sides, betweenness, circles, lengths and angles
(among them Circle 1 to 3, Pasch 2 to 4, Between 6, Triple incidence 1 to 3, and
Intersections 4 and 5), and I.12, I.17, I.19, I.20, I.23, III.16 and III.31.
`#print axioms` on each of the 78
theorems lists only declarations of `Elements/Foundations/` and Lean's own `propext`,
`Classical.choice` and `Quot.sound` (eight depend on none); `sorryAx` appears in none.
Nothing goes to the owner as an axiom.

## 5. Recommendation for #57

**Go for full**, for III.16 and III.31, on these conditions:

1. **The words.** `WithinAngle`, `MixedAngle` with its two kinds, `vertex`, `region`,
   `LocallyWithin`, `Surrounds`, `NearVertexOpen`, `LocallyLess`, `LocallyEqual`, `Exceeds`
   and `FallsShort` move to `Elements/Foundations/DefinitionsIII.lean`, with the
   coordinator's approval, `check_fidelity.py --write-lock`, a decisions entry, and the
   model lock and `tests/model/MODEL.md` read again (WORKFLOW, section 2, item 1). They are
   definitions, not axioms, and add nothing to what is assumed. `NearVertex` may go with
   them or stay a step.
2. **The statements.** III.16 gains the two comparisons and III.31 the two, as restatements
   of `theorem Prop16` and `theorem Prop31` (staged as `Elements.BookIII.Staging.Prop16` and
   `.Prop31`), so that Lean stands under Heath's angle sentences, which have none today. The
   conjuncts are the conclusions of `Prop16.semicircle_gt` and `Prop16.horn_lt` quantified
   over `F`, and of `Prop31.greater_gt_right` and `Prop31.less_lt_right` over `R`, written
   through the object, as `(ofSegment A B ABC E).Exceeds B F`. The restated proofs prove the
   existing parts first (III.16's two parts, III.31's right angle) and then pass them to the
   steps, which take them as hypotheses and so cite nothing after their proposition.
   `Prop16.horn_nearVertex` belongs beside them, or in the record, as the check that the
   horn is not empty. The general forms (any acute angle by I.23; any chord not through the
   centre) are companions.
3. **The shared steps.** `near_inside_of_angle`, `foot_nearest`, `len_lt_of_add_lt`, the
   `surrounds_` facts and `near_across` cite I.12, I.17, I.19 and I.20, and go to
   `Elements/BookIII/Squares.lean`; the small facts on sides and rays go to Book Zero. The
   `Prop16.` and `Prop31.` steps go before their propositions, in their files
   (FORMALIZATION, section 6). The checks of the reading (a), (b) and (c), with the order
   laws, go beside the words or in `Squares.lean`, as the coordinator decides.
4. **The records.** III.16 and III.31 drop `mixed-angles-omitted` and take a new tag, defined
   in `review/terms.toml` before use, carrying Astra's wording: the comparisons use local
   containment of curved angular regions, and no general arithmetic or ratio theory of mixed
   angles is claimed. The passage for the local bound is a `helper`.
5. **The challenge.** As with every new representation, readers who did not write these
   definitions challenge them before approval, starting from the open questions in section 3.
   The first challenge is answered in the appendix.

## Appendix: the challenges, and what was done

One reader challenged the prototype on #56, with two material findings and five editorial
ones. Every finding was applied, in `Staging/Stage4b/MixedAngles.lean` and here; none was
answered without a change.

| Finding | Done |
|---|---|
| *Material.* The strictness of `LocallyLess` counted edge points as excess: an angle was "less" than itself with an arm added, or than a slit angle; in III.31 and III.16 the excess was already met by points of an arm. So a Lean "greater" did not yet certify Euclid's | Strengthened, as proposed: `Surrounds` and `NearVertexOpen` added, and `LocallyLess` asks for whole circles of excess. Each kind of region is shown to hold a whole circle about each of its points (`surrounds_sameSideOf`, `surrounds_inside`, `surrounds_outside`, `WithinAngle.surrounds`), with `foot_nearest` and `len_lt_of_add_lt` (I.12, I.17, I.19, I.20). Checks (a) to (d) proved again under the new definition; the reader's two cases now fail, as `not_locallyLess_arm` and `not_locallyLess_slit` prove |
| *Material.* Check (b) only partly done for the angle of contact: nothing showed that another straight line into the circle names the same horn | `Prop16.horn_locallyEqual` added and proved, for every `B'` on `B`'s side of `AE`, including the case where `B'` is on the other side of the diameter. The general form for any touching straight line is left for the move to the foundations (section 3) |
| *Editorial.* The comparison is not tied to the mixed angle's vertex; `vertex` unused | `MixedAngle.Exceeds` and `MixedAngle.FallsShort` added, through `m.vertex`; the III.16 and III.31 comparisons are stated with them |
| *Editorial.* No order laws for `LocallyLess` and `LocallyEqual`, though the page chains comparisons | `LocallyLess.irrefl`, `.asymm`, `.trans`, `.congr_left`, `.congr_right`; `LocallyEqual.refl`, `.symm`, `.trans`, `.of_iff`; `LocallyWithin.refl`, `.trans`. `NearVertexOpen.mono_near` shrinks a whole circle to the neighbourhood where the containment holds |
| *Editorial.* Heath's "remaining angle" had no lemma tying it to the right angle | `Prop16.remaining`: within the right angle `BAE`, the angle of the semicircle, the horn and the circumference, and nothing else |
| *Editorial.* The `MixedAngle` docstring and section 1 said `B` is on the circle and `AE` touches it; the III.16 lemmas assume neither | Both reworded: `B` beyond the centre on the diameter, produced if need be; `AE` at right angles, touching by III.16's porism. `BookIII.Prop16`'s hypotheses kept |
| *Editorial.* The forms "ready to be conjuncts" cited the theorems they would belong to | Every `Prop16.` step takes III.16's two parts as `h1` and `h2`, and `greater_gt_right` and `less_lt_right` take the right angle `BAC`; only the companions cite III.16 and III.31. Conditions 2 and 3 say where the steps go |
