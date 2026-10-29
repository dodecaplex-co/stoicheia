# Book III: circles

*The design for Book III (16 October 2026, brought up to date on 17 October, on 18
October for stage 3 of [brief 0006](0006-statements.md), and on 19 October for its stage 4
with the mixed-angle and centre work): how Lean says Book III's words,
where the facts about them live, and how its thirty-seven propositions are stated. The
code states what we formalized; where the code, this brief, a review record and the pages
disagree, the disagreement is recorded and every document it touches is reconciled
([FORMALIZATION.md](../FORMALIZATION.md), section 1). The first mate's working detail, one
note per proposition, is in [first-mate-III.md](../reports/crew/first-mate-III.md).*

**19 October 2026, after brief 0008's step 6.** The current account below reflects the
restated declarations at `17987153`: proofs obtain existence-only centres internally,
and `Arc.Drawn` asks only for its endpoints and side. The earlier dated decisions and
exception table remain historical; the dated notes say where they have been superseded.

## What Book III needs

Book I draws circles and reads off them; Book III is about them. It finds a circle's
centre, compares the straight lines in it and from a point to it, makes circles and
straight lines touch, measures the angles that stand on its circumferences, and in
III.26–III.30 compares the circumferences themselves:

> In equal circles equal angles stand on equal circumferences, whether they stand at the
> centres or at the circumferences. (III.26)

Three things in it needed more than Books I and II built. Our foundations now give every
circle a centre (`exists_centre`); statements keep named centres where their geometry uses
them. A circumference is a magnitude to Euclid, compared,
added and taken away, and we have only lengths, angles and areas. And twice (III.16,
III.31) he speaks of angles "contained by a straight line and a circumference", which
our rectilineal angles, each made by two straight lines, are not. The companions of III.16
and III.31 now compare those mixed angles as regions near their vertices.

## The words

The definitions are in `Elements/Foundations/DefinitionsIII.lean`. None is an
assumption.

| Euclid | Lean | Used in |
|---|---|---|
| Def. 1, equal circles | `EqualCircles α β`: a radius of the one is equal to a radius of the other | III.24, III.26–III.29 |
| Def. 2, a straight line touching a circle | `Touches A B α`: `AB` meets the circle, and, produced either way, does not cut it (`¬ LineMeetsCircle`) | III.16 Por., III.17–III.19, III.32, III.36, III.37 |
| Def. 3, circles touching | `TouchesInternally α β C` (they meet at `C`, are two circles, and no point of `β` is outside `α`), `TouchesExternally α β C` (they meet at `C`, and no point is within both), `CirclesTouch` (either within the other, or without) | III.6, III.11–III.13 |
| Defs. 4, 5, equally distant, at a greater distance | `‖E F‖ = ‖E G‖`, `‖E H‖ < ‖E K‖` for the feet of the perpendiculars from the centre `E`; the foot itself, `Foot E A B F`, the centre when `AB` passes through it, from stage 4 of [brief 0006](0006-statements.md) | III.14, III.15; `Foot` in their companions |
| Def. 6, a segment | a circle, a straight line `AB` in it, and a point `E` of the circumference on one side, "the segment AEB"; as a figure with its points, `Arc`: the circle, the ends of the base and a point naming the side, with the segment's points `InSegment` and its circumference's `OnArc`; segments that coincide, `Arc.Congruent` (Common Notion 4); for III.25's construction, its points alone, as a predicate | III.23–III.25, III.33, III.34; `Arc` in III.24–III.26, III.28 |
| Def. 7, the angle of a segment | `MixedAngle.ofSegment`, compared as a region near its vertex | III.16 and III.31's companions |
| Def. 8, the angle in a segment | `∠ A E B`, `E` on the circumference of the segment | III.21 on |
| Def. 9, the angle standing on a circumference | `standing α B A C`, the circumference on which the angle `BAC` stands | III.27, III.30 |
| (Def. 6, 9) the circumference BKC | `circumference α B K C`: the part of `α` from `B` to `C` on `K`'s side of `BC`; for an `Arc`, `Arc.measure` | III.24's companions, III.26, III.28, III.29 |
| Def. 10, a sector | none: no proposition of Book III uses it | |
| Def. 11, similar segments | no word: `∠ A E B = ∠ C F D`, equal angles in them | III.23, III.24, III.26 |

**19 October 2026, Definition 3.** The row above records the earlier reading. By
[brief 0008](0008-centre.md), section 7, `CirclesCut α β` now means that the circles meet
at two points and each has a point within the other. Contact within replaces the clause
that the circles are different with a point of β within α; the common point C and the
clause that no point of β is outside α stay. Contact without stays as above.

**Touching, for a straight line.** "Meeting the circle and being produced, does not cut
the circle": `Touches A B α` says the straight line `AB` meets `α` and does not meet it in
two points. That no point of it is within the circle is then Book Zero's
`Touches.not_inside` (System E, Intersection 3).

**Touching, for circles.** Heath reports two readings of Definition 3 (vol. 2, p. 3): that
the circles do not cut near the point of contact, it being left to prove that they do not
cut elsewhere; or that they do not cut at all, and "Todhunter thinks the latter opinion
correct". Heath does not think it proved, and prefers to read the definition "as meaning
simply that the circles meet at a point but do not cut at that point". He adds that
Euclid "does practically assume" in III.11–III.13, without stating it, that "circles
touching at one point do not intersect anywhere else", and that the definition must at
least admit that a circle touching another internally has, "immediately before 'meeting'
it", passed through points within it, and one touching externally through points outside.

Lean takes the whole-circle reading, Todhunter's as Heath reports it, and makes "do not
cut" precise by Heath's inside and outside: touching within, no point of the inner circle
falls outside the outer (`TouchesInternally`); touching without, no point lies within both
(`TouchesExternally`). Heath's own reading is local, at the point of contact, and Lean
has no neighbourhoods to say it in. So the definition carries what Heath says Euclid
leaves tacit in III.11–III.13: touching circles do not cross anywhere. III.13 keeps its
content, for the definition does not say that the circles meet at one point only: two
points of contact, within or without, are what III.13 refutes, by III.11 and III.2. (Read
"do not cut one another" as "have only one point in common", and III.13 would be the
definition; that reading is set aside.) III.11's statement says which circle is within
(`TouchesInternally ABC ADE A`, `ADE` within `ABC`); III.13 asks for either. III.11's
mishnah owns Heath's note on Definition 3 and says all this.

**19 October 2026, local contact.** The claim above that Lean has no neighbourhoods is
superseded: predicates for regions near a vertex now serve the mixed-angle comparisons.
Contact read locally, at the point of contact, and its equivalence to the whole-circle
reading have not been formalised.

**25 October 2026, local contact formalised (#126).** The sentence above is overtaken:
contact at the point of contact is now defined beside the whole-circle reading
(`TouchesInternallyAt`, `TouchesExternallyAt` and `CirclesTouchAt`, with `Touching.Near`,
in `Elements/Foundations/DefinitionsIII.lean`), and III.13's companions prove the two
readings the same for any two circles (`Prop13.circlesTouch_iff`;
[decision entry](../decisions/2026-10-25-routes-iii-touching.md)). Book III's statements
keep the whole-circle reading.

**19 October 2026, contact within.** The whole-circle reading remains ours. The point
of the inner circle within the outer now belongs to `TouchesInternally`, expressing the
passage within that Heath says Definition III.3 must imply. It lets III.6 draw FEB through
that point. III.11 uses III.6 to distinguish its centres; III.13 carries the point within
to the supposed second contact. The bridge in `Audit/` recovers the earlier readings of
III.5, III.6, III.11 and III.13 from the restated ones under the existing axioms, with no
extra hypotheses. The point does not turn this into Heath's preferred local reading.

**Circumferences.** Euclid compares circumferences only in one circle or in equal circles:
III.26–III.30, IV.11 and IV.16, and VI.33. A new kind of magnitude for them would need
new tacit rules, among them a rule of superposition for segments, and System E has
none, and we add no axiom for Book III. So a circumference is measured, by a
definition, as Definition 9 suggests: by the angle that stands on it at the
circumference, taken twice.

**19 October 2026, circumferences.** No axiom is added for circumferences. The earlier
decision to add none for Book III is superseded by the approved rule `Tacit.exists_centre`,
which gives every circle a centre ([brief 0008](0008-centre.md), approved 18 October).

**26 October 2026, the radius rule.** A second rule of ours has joined `exists_centre`: a
circle's radius is not nothing (`Tacit.radius_ne_zero`), added by the owner's decision of
25 October 2026 ([its decisions entry](../decisions/2026-10-25-radius-rule.md)). It is a
rule for Book Zero, not one added for Book III's sake, but Book III's proofs rest on it:
every positive length in the edition now comes from it, and III.5 and III.6 rest on it in
place of Diagram-segment 2 and Circle 1, which neither now rests on
([the entry for that move](../decisions/2026-10-25-book-zero-radius-rule.md)).

`circumference α B K C` is `∠ B A C + ∠ B A C` for a point `A` of `α` on the other side of
`BC` from `K`; Lean chooses one such angle (`Classical.epsilon`), as `rect` chooses one
area. It is the angle the circumference subtends at the centre when it is less than
a semicircle (III.20); a semicircle is two right angles, and the whole circle four. In one
circle, or in equal circles, two circumferences are equal exactly when these angles are,
and that is all Euclid asks of them. The measure carries no radius, so in unequal circles
equal measures do not make equal circumferences. The statements that compare
circumferences keep his "in equal circles", and the proofs use it as he does: in III.26
"the radii are equal", and the bases, by I.4. Not every statement needs it, though
(below).

`standing α B A C`, the circumference on which the angle `BAC` stands, is the same measure
named from the other side: the part of `α` cut off by `AB`, `AC`, away from `A`. Book
Zero proves that the two names agree (`standing_eq_circumference`) and that either may be
named from any point of its side (`circumference_congr`, `standing_congr`).

What this costs, and what it does not:

- The angle measure cannot tell circumferences of unequal circles apart. Euclid never
  compares them, so no statement of his says otherwise.
- Some of Euclid's conclusions become short by the measure. Equal angles at the
  circumferences give equal measures at once, in any two circles. So III.26 and III.27
  hold for any two circles as stated: they keep "in equal circles" from Euclid's
  enunciations, and their proofs use it along his route (to III.26 by I.4, III.24 and
  the whole circle), but the statements do not need it. III.28 and III.29 do need equal
  circles, for there the measures are tied to straight lines in the circles: equal
  straight lines in unequal circles cut off unequal measures. (Status note, 17 October
  2026, from [brief 0005](0005-astra-review.md); the review records tag these
  `redundant-hypothesis` and `angle-measure`. On 18 October, stage 3 of
  [brief 0006](0006-statements.md) has III.26 and III.28 conclude that the circumferences
  are congruent as well, `Arc.Congruent`, so III.26 now needs its equal circles, and its
  record no longer carries `redundant-hypothesis`; III.27 still holds for any two
  circles.)
- III.24 concludes Euclid's equal segments: laid one on the other, they coincide
  (`Arc.Congruent`, below). Its companion `Prop24.equalCircles` proves equal circles and
  equal measures, and its measure clause likewise follows from its equal angles alone; the
  equal circles are its real content.
- The facts Euclid takes for granted about circumferences (that a circumference and the
  one remaining make up the circle; that the less is less than a semicircle) are proved
  from III.20–III.22, in `Elements/BookIII/Circumferences.lean`, and so a proposition that
  uses them cites those three.

**28 October 2026, III.27 and III.29 (#474).** The second item above is overtaken for these
two. Since [the decision of 28 October 2026](../decisions/2026-10-28-iii27-iii29-swap.md),
`Prop27` and `Prop29` state Euclid's congruence reading: their equal circumferences coincide
(`Arc.Congruent`), and congruent circumferences lie in equal circles already, so "in equal
circles" is redundant in both, for that reason and not the measure's. The statements the
item speaks of are now the companions `Prop27.of_measure`, which still holds for any two
circles, and `Prop29.of_measure`, which still needs its equal circles. Both records carry
`angle-measure` and `redundant-hypothesis`. `Prop27`'s proof first makes its circumferences
equal in measure, by III.24's companion `Prop24.equalMeasure`, and then argues as before.
The phrase table and the note on III.27's statement below have notes of the same date.

**Mixed angles.** "The angle of the semicircle is greater, and the remaining angle less,
than any acute rectilineal angle" (III.16); "the angle of the greater segment is greater
than a right angle" (III.31). These angles are "contained by a straight line and a
circumference", and our angles, magnitudes of two straight lines, are not them. Euclid
proves them by rectilineal facts: in III.16, that no straight line can be interposed
between the circumference and the tangent, which is the second clause of III.16's
statement (every straight line through `A` other than `AE` passes within the circle); in
III.31, that the angles `BAC`, `CAF` are right. The Lean states III.16's clause and the
right angle `BAC`; that `CAF` is right, the proof of III.31 shows on its way, where Euclid
finds `BAC` equal to `FAC` and so each right. The claims about mixed
angles are now proved in companions after those main statements, using `MixedAngle` and
comparisons of regions near the vertex. III.16's companions argue directly from the
rectilineal fact, where Euclid uses reductio; III.31's companions prove what he calls
manifest. No addition, ratio or motion of mixed angles is claimed. The representation
and Heath's account of the quarrel over the horn-like angle are explained in the mishnah.

**27 October 2026, correction.** III.16's companions now follow Euclid's reductio from the
rectilineal fact, and its route is `euclid`. The sentence above that they argue directly,
and the dated notes below that give the route as `modified`, describe the earlier proof;
[III.16's record](../../review/III/16.toml) gives the route now.

## Circles and their centres

**19 October 2026, step 6 complete.** These conventions replace the earlier convention
of supplying a centre merely to have one; the rule's approval of 18 October stands.
The account through the paragraph on III.1 below is the 19 October account; the
coordinator's correction of 22 October, after it, supersedes its centre convention for
III.2, III.4, III.8, III.14 and III.17.

A circle in Lean has a centre by `exists_centre`, the rule approved on 18 October 2026
in [brief 0008](0008-centre.md). `Postulate3` also makes each circle with its centre.
After step 6, existence-only centre inputs have gone; named centres remain wherever
another hypothesis or conclusion uses them geometrically. `Prop1.within` keeps its
given-centre interface for the confined use in III.1's construction. Simson
observed that the proof of III.1 must be by *reductio ad absurdum*, and Heath explains
why: "At the beginning of Book III. we have nothing more to base the proof upon than the
definition of a circle, and this cannot be made use of unless we assume some point to be
the centre" (vol. 2, p. 8). So:

- Where another hypothesis or conclusion uses the centre geometrically,
  the centre is a hypothesis in Heath's letter: `Centre E ABCD` in III.7, `Centre F ABC`
  in III.18.
- Where the enunciation itself measures from the centre, the centre is a hypothesis too:
  III.14 and III.15, "equally distant from the centre" and "nearer to the centre"
  (Definitions 4 and 5), with the feet of the perpendiculars from it. III.15's setting-out
  names it, "E the centre". III.14's takes it "[III. 1]": its proof finds a centre by
  III.1 and that it is `E` (`centre_unique`), so that the bracket is cited. III.4 and
  III.8 also cite III.1, applying their universal geometric conditions to its centre.
- Otherwise a centre is obtained inside the proof: by III.1 under Heath's "[III. 1]",
  and by `exists_centre` at an unbracketed step where the geometric data supply none.
  III.17 uses `Prop1.of_circle`, which chooses two points of the given circle and applies
  III.1. III.28 and III.29 still take their centres from `EqualCircles`.
- "Not through the centre" in III.4 and "through the centre" in III.8 are said of every
  centre (`∀ F, Centre F ABCD → ¬ Collinear A C F`); these geometric conditions stay,
  and the proof takes a centre by III.1 without an existence hypothesis.

III.1 itself finds the centre of a given circle: given two points `A`, `B` of the
circle, it constructs `D`, `C`, `E` and `F` as Euclid does and concludes `Centre F ABC`.
The statement is the problem's answer with its construction; its content is the reductio,
which shows that the point found is the centre; the proof takes a centre `G` from
`exists_centre` for the reductio.

**22 October 2026, #131.** A proof now takes a centre from `exists_centre` wherever a
call of III.1 would do no work, and Heath's "[III. 1]" stays on the page as his
reference, by the coordinator's
[decision of that day](../decisions/2026-10-22-iii1-calls-dropped.md), which corrects
brief 0008's rule "a bracket means III.1, none means the rule". The convention now
stands as follows, and no statement changes:

- III.2, III.4, III.8 and III.17 obtain their centres through `exists_centre`; each needs
  the centre alone, so a call of III.1 would do no work.
- III.14 uses the centre `E` supplied by its statement and takes no other centre.
- Heath's brackets remain his references on each page. III.28 and III.29 still take
  their centres from `EqualCircles`; unbracketed steps such as III.35 to III.37 still use
  `exists_centre`.
- III.4 and III.8 apply their universal geometric conditions to the centre obtained
  through `exists_centre`, with no existence hypothesis.

**28 October 2026, #547.** The convention above is overtaken. Under Heath's "[III. 1]",
III.2, III.4, III.8 and III.17 now take their centres by III.1's construction, through
`Prop1.of_circle`, which is now III.1's companion, by the owner's decision of 26 October
2026 recorded on [#547](https://github.com/jackChallis/stoicheia/issues/547)
([the entry of that day](../decisions/2026-10-26-centre-by-iii1.md) and
[the entry for III.2](../decisions/2026-10-28-iii2-centre.md)). III.2's route is now
`euclid`. So is III.8's: its last step goes by Euclid's two orders in every case, and a
point of contact, which ends both orders, is never the nearer (`Prop8.contact_last`).
III.26, III.28 and III.29 remain `modified`, and their records say why.

**28 October 2026, #547, later.** The congruence of the remainders in III.26 and III.28 now
comes by Euclid's subtraction, not by III.24 applied to the remaining segments, which the
entries for III.26 and III.28 above describe: the application of the equal segments, extended to
the whole circles (`Prop26.extend`), is restricted to what remains (`Prop26.remainder`).
III.26 stays `modified` for its obtuse angles at the circumferences, and III.29 for its
greater circumferences; III.28's route is `euclid`, its two diameters a case Heath calls
"scarcely worth giving" (vol. 2, p. 60), declared as a passage, so the note above is
overtaken for III.28. Each record says why, with Heath's page. III.1 takes each step of its construction under Euclid's sentence, and
its reductio supposes that the constructed F is not the centre
([the entry](../decisions/2026-10-28-iii1-under-heath.md)).

## Where the facts live

The rule is Books I and II's: a fact that needs no proposition goes in Book Zero; one that
cites a proposition goes beside the propositions, and its docstring ends with what it
cites.

**Book Zero, `Elements/Figure/OnCircles.lean`** (cites no proposition, declares no axiom):
`circumference_congr`, `standing_congr`, `standing_eq_circumference`, `Centre.every`,
`EqualCircles.radii`, `.symm`, `.refl`, `CirclesCut.symm`, `Touches.not_inside`,
`Touches.of_collinear`, `Touches.contact`. Until 24 October 2026 it also held
Triangle.of_onCircle (three points of a circle are not on one straight line),
exists_onCircle_oppositeSidesOf and exists_onCircle_sameSideOf (a straight line in a
circle has points of it on each side), which rested on System E's Circle 2 (which contains
III.2); no proposition used them. They were taken out when Circle 2 and Circle 3 were
proved after III.2 (#294): the propositions take the same facts from III.2's corollaries,
with no supplied centre (`Prop2.triangle`, `Prop2.oppositeSide`, `Prop2.sameSide`, and
`Prop2.within` for ends on or within the circle).
**`Elements/Figure/Chords.lean`**, from stage 3 of [brief 0006](0006-statements.md):
`Arc.congr_side` and `Arc.Congruent.congr_side` (only the side names a segment). The
brief's two other facts for it rest on III.2, and come after it: `Prop24.chord_cases` (a
point of the straight line through two points of a circle is on the circle exactly when it
is one of them, and within it exactly when between them), before III.24, which uses it;
and the meeting fact for an arc, `Prop25.meets`, beside III.25, whose companion uses it.

**27 October 2026, correction.** III.24 no longer uses `Prop24.chord_cases` in its main
proof. The lemma remains before it and is used by `Prop24.image`, after the theorem, for
`Prop24.equalMeasure` and `Arc.congruent_iff`.

**Book III's ground, before III.1, `Elements/BookIII/Squares.lean`**: `sq_pos` (the square
on a straight line is something) and `BookI.Prop46.sq` (equal squares are on equal
straight lines), for III.14 and III.37, which add I.3, I.4, I.28, I.34, I.46; and
`foot_between` (the perpendicular from the centre to a straight line in the circle falls
between its ends), for III.14, III.35 and III.36 before they cite III.3, which adds I.17
and I.19; and, from stage 3, `Arc.eq_of_aligned` (two segments on one base, on one side,
in equal circles and of one kind, are one), which adds I.7; and, from stage 4,
`Foot.exists` and `Foot.unique` (every straight line has one foot of the perpendicular
from a point), which add I.12 and I.17. The file imports Book II's
ground, so every proposition of Book III has `rect`, `sq` and `BookI.Prop47.sq`.

**26 October 2026, `foot_between` (#477).** `foot_between` has moved, with its name and type,
to a ground of its own after III.2, `Elements/BookIII/Feet.lean`, which III.14, III.15,
III.35 and III.36 import. Its last step is Circle 1, and Circle 1 is to be proved after
III.2, by the owner's decision of 25 October 2026
([the entry for this move](../decisions/2026-10-25-circle-1-bookzero.md)); III.1 and III.2
import `Squares.lean`, so a step that uses it must stand after III.2. The paragraph above is
unchanged; the rest of `Squares.lean` stands as it says.

**Placement, `Elements/BookIII/Placement.lean` and `Elements/BookIII/Placement/`**, from
stage 3, for III.24: `placement`, Euclid's application of one segment to another, from I.2,
I.3, I.4, I.7, I.8, I.20, I.22 and I.24's step, with the lemmas of the `Placement`
namespace, and I.20's degenerate case in `Elements/BookI/HelpersTriangles.lean`. Only
III.24 and `Elements/BookIII/Arcs.lean`, after III.29, may cite them. `Arcs.lean` holds the
bridge theorems, for drawn segments (`Arc.Drawn`): in equal circles, circumferences equal
in measure are those on equal straight lines and of one kind (`Arc.measure_eq_iff`), and
segments are congruent exactly when their circles are equal and their measures equal
(`Arc.congruent_iff`).

**Book III's ground, after III.22, `Elements/BookIII/Circumferences.lean`**, imported by
III.23–III.37:

| Lemma | What Euclid takes for granted | Adds |
|---|---|---|
| `Circumference.eq` | a circumference is twice the angle at any point of the other segment | III.21 |
| `Circumference.standing` | the circumference on which `BAC` stands is twice `BAC` | III.21 |
| `Circumference.centre` | a circumference beyond which the centre lies is its angle at the centre | III.20, III.21 |
| `Circumference.whole` | the two circumferences on a straight line make up the whole circle, four right angles | III.21, III.22 |
| `Circumference.semicircle` | a semicircle is two right angles | I.5, I.32 |
| `Circumference.lt_semicircle` | the circumference beyond the centre is less than a semicircle | I.32, III.20, III.21 |
| `Circumference.gt_semicircle` | the circumference on the centre's side is greater than a semicircle | I.32, III.20–III.22 |
| `Circumference.add` | a circumference cut at a point of it is the two circumferences it is cut into, for Book IV (stage 3) | I.32, III.21, III.22 |

`Circumference.semicircle` proves of circumferences, by Euclid's own argument, what III.31
proves of the angle in a semicircle: III.28 and III.29 need it first. It argues at the
point that measures the circumference, so it needs only I.5 and I.32, not III.21.

**26 October 2026, the angle at the centre (#129).** The table stands, and beside it now
stand the word `angleAtCentre`, in `Elements/Foundations/DefinitionsIII.lean`, the angle at
the centre standing on a circumference, which may be two right angles or more, and its
bridge theorems before III.20 in `Elements/BookIII/Prop20.lean`: `angleAtCentre.diameter`
(every diameter with its ends on opposite sides of the base gives the same angle),
`angleAtCentre.congr` (the same for every point naming the side), `angleAtCentre.within`
(the angle BEC when the centre E lies beyond the base), `angleAtCentre.semicircle` (two
right angles when E is on it), `angleAtCentre.reflex` (with the angle BEC, four right
angles when E is on the circumference's side), `angleAtCentre.reflex_gt` (then greater
than two right angles) and `angleAtCentre.size` (less, two right angles or greater, as E
lies). III.20's companion `Prop20.circumference` proves from III.20, with III.2 and
without III.21, that every circumference is its angle at the centre, whatever its size.
`Circumference.centre` keeps its statement, the case where the centre lies beyond the
circumference and its angle at the centre is the rectilineal angle BGC; it is proved from
`Circumference.eq` (III.21) and III.20's companion `Prop20.special`, the statement III.20
had before #129, so its row still adds III.20 and III.21
([decision entry](../decisions/2026-10-25-routes-iii-centre.md)).

**Porisms.** Two porisms are cited by later propositions, and are theorems of their
own, after their propositions: `Prop1.porism` (the centre lies on a straight line
bisecting a straight line in the circle at right angles; III.9, III.10) and
`Prop16.porism` (the straight line at right angles to a radius at its end touches the
circle; III.17, III.33, III.37 and Book IV). Since brief 0005's stage 1, each porism is an
entry of its own in the certificate, "III.1 Por." and "III.16 Por.", with its own axioms,
citations and status, and every policy check applies to it as to a proposition. Heath's
"[III. 1, Por.]" and "[III. 16, Por.]" are read as citations of those entries, by the
scripts and by `Certificate/Facts.lean` alike, and the graph draws a porism as its
proposition. A proposition counts as proved only when its porism is too, and its page
shows the porism's certificate in a column of its own. III.1 Por. follows Euclid's
reductio directly from its given centre. On AB, the centre is D by `Prop1.middle`; off
AB, it shares `Prop1.equal_adjacent` and `Prop1.perpendicular` with III.1: the first
applies I.8 to make the adjacent angles equal, Definition I.10 makes them right,
Postulate 4 identifies their measure with `∟`, and the second puts the centre on DC. It
neither calls III.1 nor uses `centre_unique` or `exists_centre`. III.16 Por. cites III.16
for the result from which its "from this it is manifest" follows.

## How the statements say Euclid's phrases

| Euclid | Lean |
|---|---|
| "the circle ABC" | a circle `ABC`, with `OnCircle` for the named points that the proof uses |
| "the straight line AB falls within the circle" (III.2) | every point between `A` and `B` is `InsideCircle` |
| "from E let EF be drawn perpendicular to AB" | I.12's form, as in II.12: `F` on `AB`, every angle `EFP` right |
| "DE touches the circle ABC at C" | `Touches D E ABC`, `OnCircle C ABC`, `Collinear D E C` |
| "the circumference BKC" | `circumference ABC B K C` |
| "on equal circumferences BC, EF" (III.27) | `standing ABC B A C = standing DEF E D F`, the circumferences on which the angles at `A`, `D` stand |
| "the circumference AD is equal to DB" (III.30) | `standing ADB A B D = standing ADB D A B` |
| "the greater circumference ACB" (III.28) | `circumference ABC A G B ≤ circumference ABC A C B` |
| "the rectangle contained by AE, EC" (III.35) | `rect A E E C`, Book II's |
| "the angle at C, the given rectilineal angle" (III.33) | `∠ C₁ C C₂`, with `Triangle C₁ C C₂`, as I.42 takes the angle at `D` |
| "the segment AEB is equal to the segment CFD" (III.24) | `Arc.Congruent ⟨AEB, A, B, E⟩ ⟨CFD, C, D, F⟩`: one map puts A on C and B on D, the segment on the segment and the circumference on the circumference, keeping every distance between their points |
| "the circumference BKC is equal to the circumference ELF" (III.26, III.28) | `circumference ABC B K C = circumference DEF E L F ∧ Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩`: equal in measure and congruent |
| "similar segments ACB, ADB" | `∠ A C B = ∠ A D B` |
| "the given segment ABC" (III.25), "the given circumference ADB" (III.30) | the circle, the straight line `AC` (or `AB`), and a point `P` on the side of the segment, for every such `P`; for III.25's construction, the ends `A`, `C`, the point `P` and the segment's points as a predicate `S`, with the meeting fact |

**28 October 2026, III.27 and III.29 (#474).** The row for "on equal circumferences BC, EF"
now gives the companion `Prop27.of_measure`. `Prop27` says it as
`Arc.Congruent ⟨ABC, B, C, Q⟩ ⟨DEF, E, F, R⟩`, with `Q` across `BC` from `A` and `R` across
`EF` from `D`; and III.29's equal circumferences are
`Arc.Congruent ⟨ABC, B, C, G⟩ ⟨DEF, E, F, H⟩` in `Prop29`, and equal in measure,
`circumference ABC B G C = circumference DEF E H F`, in `Prop29.of_measure`.

Hypotheses come from the setting-out and conclusions from "I say that", with these choices
worth naming. The first mate's report has a note on every statement.

- **III.3** speaks of "a straight line CD through the centre". The straight line through
  the centre `E` and the point `F` is `FE`, and so the statement is said of `E` and `F`;
  `C` and `D`, its ends on the circle, need no Lean name. Citers (III.4, III.14, III.35,
  III.36) have a centre and a point, never the ends.
- **III.5, III.6** exclude a circle paired with itself through the point within:
  `CirclesCut` supplies one in either direction, and `TouchesInternally` one of the inner
  circle within the outer. Contact without forbids a point within both.
- **III.7, III.8** say "greatest", "least", "the nearer is greater" and "only two equal"
  of every straight line from the point, with Euclid's meaning of "nearer": the less angle
  at the point with the ray through the centre, unsigned. Heath discusses the other
  readings and prefers Euclid's (vol. 2, pp. 15–16). `Prop7` and `Prop8` compare two
  straight lines on one side of the diameter, as Euclid's figures do; their companions,
  `Prop7.general` and `Prop8.general`, compare any two, on either side
  ([brief 0007](0007-stage-4b.md)), III.8's within each class. III.8 says which lines fall
  on the concave and which on the convex circumference by where the straight line from `D`
  meets the circle again.
- **III.9** leaves out Euclid's "within". His proof draws `ED` and `FD` through from the
  middle points `E`, `F` of `AB`, `BC`, which are within the circle, and never uses that
  `D` is; and III.25's companion `Prop25.complete` cites III.9 for a point not yet known
  to be within, the centre found beyond the segment.
- **III.10** concludes that the two circles are one, `ABC = DEF`, from three common
  points, as I.7 concludes `C = D`. Heath names four points; the proof uses three.
- **III.11, III.12** conclude where the centres and the point of contact lie:
  `Between F G A` within, `Between F A G` without. III.12 is printed in square brackets by
  Heath, as Heron's proof made into a proposition; it is stated and proved like the rest.
- **III.14** also asks that neither straight line pass through the centre, as Euclid's
  proof does when it takes "a straight line AB not through the centre" (III.3). Its
  companion, `Prop14.general`, takes diameters too, at no distance from the centre, as
  the enunciation does: it measures each straight line to its foot, `Foot`
  ([brief 0006](0006-statements.md), stage 4).
- **III.14, III.15** take the centre and the feet of the perpendiculars as hypotheses,
  since Definitions 4 and 5 measure from them; III.14's proof takes the centre by III.1
  all the same (above). The perpendiculars are given, so I.12 is not cited; that the feet
  fall within the straight lines is `foot_between`.

  This is the historical 19 October account. The 22 October correction in "Circles and
  their centres" supersedes its account of III.14.
- **III.15** says "the diameter is greatest" together with the more remote `FG` and
  `‖E H‖ < ‖E K‖`, as Euclid does: his proof that `AD` is greater than `BC` goes through
  `MN`, made on `EK` by cutting off `EL` equal to the less `EH` (I.3), so it uses the
  more remote straight line. Its companions take each clause for every straight line in
  the circle: `Prop15.le_diameter`, with no more remote straight line, and
  `Prop15.nearer`, the nearer of which may be a diameter
  ([brief 0006](0006-statements.md), stage 4). No later proposition cites III.15.
- **III.16** states what Euclid proves by straight lines: the straight line at right
  angles to the diameter at its end falls outside, and every other straight line through
  that end passes within. Its companions prove the mixed-angle comparisons, with their
  local reading explained in the mishnah.
- **III.20** takes the centre on the side of `BC` where `A` is, "the angles having the same
  circumference as base": then the angle at the centre is less than two right angles, as
  Euclid's angles are. Heath observes that Euclid "had no idea of III. 20 applying ... to
  the case where the angle at the circumference ... is obtuse" (vol. 2, p. 48). The
  statement covers both of Euclid's cases, drawn in his one figure, the centre within the
  angle `BAC` and outside the angle `BDC`, and the case he leaves out, the centre on one
  of the arms.

  **26 October 2026, the angle at the centre of any size (#129).** The bullet above is
  overtaken: III.20 now speaks of the angle at the centre standing on the circumference,
  of any size (`angleAtCentre`, in `Elements/Foundations/DefinitionsIII.lean`), which may
  be two right angles or more, our reading after Heath's notes, not Euclid's; the statement
  described above is its companion `Prop20.special`
  ([decision entry](../decisions/2026-10-25-routes-iii-centre.md)).
- **III.21** is said of any segment. Euclid's proof covers the segment greater than a
  semicircle; Heath gives Simson's for the rest (vol. 2, pp. 49–50), and III.22 and Book IV
  need every segment.

  **26 October 2026 (#129).** Our proof of III.21 now follows Euclid's argument in every
  segment, by III.20 of any size; Simson's proof is no longer used.
- **III.22** takes a quadrilateral in the circle as four points of it with the straight line
  `BD` (joining opposite corners) separating `A` from `C`; that `AC` separates `B` from `D`
  follows.
- **III.23** concludes that the circles are one, `ACB = ADB`: on one straight line and on
  one side, similar segments coincide. Its companion, `Prop23.point`, says it point by
  point, for III.24: on one side of AB, a point is on the circle exactly when AB subtends
  at it the angle in the segment, and within it exactly when the angle is greater.
- **III.24** concludes Euclid's equal segments, read through Common Notion 4 as
  segments that coincide (`Arc.Congruent`). Euclid proves it by applying one segment to
  the other, and our Lean allows superposition only in I.4 and I.8, so the application is
  a theorem, `placement` (`Elements/BookIII/Placement.lean`), proved from I.2, I.3, I.4,
  I.7, I.8, I.20, I.22 and I.24's step; III.23's companion then settles every point by the
  angles, in place of Euclid's reductio, and III.10 is not needed. Until stage 3 of
  [brief 0006](0006-statements.md), III.24 concluded only that the circles are equal and
  the circumferences equal in measure, proved by the angles at the centres (III.20,
  III.22) and the isosceles triangles on the equal bases (I.5, I.26, I.32), as in
  [the scratch proof](https://github.com/jackChallis/stoicheia/blob/81d72f5/docs/reports/crew/scratch-III/T24.lean);
  that statement and proof are now its companion `Prop24.equalCircles`, shown as the
  alternative, and `Prop24.equalMeasure` gives the equal measures of congruent segments,
  which III.26 takes from III.24.

  **27 October 2026, correction.** After the application III.24 now follows Euclid's
  reductio: the applied segment lies on a circle through C and D (`Prop24.moved`),
  III.23's companion keeps the image of E from falling within CFD or outside it, and
  III.10, which the proof now cites as Heath's bracket has it, makes the two circles one.
  The clause above on settling every point by the angles describes the earlier proof;
  [III.24's record](../../review/III/24.toml) gives the route now.
- **III.25** finds the centre of the circle of a given segment, with Euclid's construction
  and his three cases: the centre beyond the segment, at `D`, or within it, as the angle
  `ABD` is greater than, equal to, or less than `BAD`. Since stage 4 of
  [brief 0006](0006-statements.md), the construction is given the segment only, its
  points as a predicate with the meeting fact Euclid reads off it, and describes a circle
  through `A`, `B` and `C` with centre `E` (Postulate 3); the companion
  `Prop25.complete` shows, by III.9, that the circle is the segment's, and
  `Prop25.of_circle` keeps the statement handed the whole circle, without a supplied
  centre. `Prop25.kind` gives all three segment kinds and measure comparisons; the
  equality from `Prop25.complete` transports them to the given arc.
- **III.26** says both of Euclid's cases as he enunciates them, "whether they stand at the
  centres or at the circumferences": equal angles at the centres (the circumferences less
  than semicircles) give equal circumferences, and so do equal angles at the
  circumferences, of any size. IV.11 cites the second. Since stage 3 of
  [brief 0006](0006-statements.md), both conclude that the circumferences are congruent as
  well as equal in measure, and that needs the equal circles; the remainders' congruence
  comes from III.24 applied to the remaining segments, not by subtraction.
- **III.27** likewise: equal circumferences give equal angles at the circumferences, of
  any size (IV.11 needs obtuse ones), and equal angles at the centres where those stand on
  them. As stated it holds for any two circles (above). **28 October 2026 (#474):** this
  is now the companion `Prop27.of_measure`; `Prop27` takes the circumferences congruent,
  and holds for any two circles too, since congruent circumferences lie in equal circles
  already (the note of that date above).
- **III.28** asks of "the greater" only that it be no less (`≤`), so that two diameters,
  which Heath says the proposition covers "as the proof can easily be supplied" (vol. 2,
  p. 60), cut off semicircles. Since stage 3 of [brief 0006](0006-statements.md), it
  concludes, for the greater and for the less, that the circumferences are congruent as
  well as equal in measure: the greater by III.24, their angles the halves of the equal
  angles at the centres (III.20), and two diameters by the right angle in each semicircle
  (`Prop28.right`) and III.24.
- **III.29** is said of circumferences of any size; Euclid's proof covers those less than
  a semicircle, and Heath the semicircles.
- **III.31** keeps Euclid's figure: `BC` the diameter, `A` on the circle. "The angle in a
  greater segment" is said of every point `X` of the segment `ABC`, on `B`'s side of `AC`,
  and "that in a less segment" of every point `D` on the other side, so that a citer who
  wants only the right angle (III.32, III.33) need name neither. IV.5 cites [III. 31] for
  the angle in a greater segment at a point that is not the end of a diameter. Euclid
  proves it at `B`; at any other `X`, a point `D` of the less segment and the quadrilateral
  `AXCD` [III. 22] give it, a bracket III.31 already has.
- **III.32** concludes for every angle in each alternate segment, "the angle constructed
  in the segment BAD": the proof constructs Euclid's `A` and moves to any other point by
  III.21.
- **III.33** constructs a circle and a point of its segment admitting the given angle,
  without returning a centre clause. **III.34** takes its circle explicitly and cuts off
  the required segment; its proof obtains a centre internally.
- **III.36, III.37 (19 October 2026).** III.36's first branch carries the diameter
  calculation under Euclid's sentences through cancellation. `Prop36.through_centre`
  follows III.36 as a corollary proved from it, used by `Prop37.centre_on_secant`. III.37
  now selects the centre-on-AC case explicitly, then retains its general argument in the
  other branch, including III.17 and III.1. This makes an already covered case explicit;
  both statements retain full scope. The corollary and case helper require no companion
  registration. The statements of `Prop36.through_centre` and `Prop37.centre_on_secant`
  were challenged by an independent reader who wrote neither statement, and approved as
  written by the coordinator. On 19 October 2026 the layout was changed after a review
  finding under FORMALIZATION section 5, with all statements unchanged.
  **19 October 2026, after step 6.** III.37's general branch now takes its centre F from
  `exists_centre`, since Heath gives no reference for that step, and no longer by III.1;
  DE, the straight line drawn touching, still comes from III.17.

## Book I and II's rules, in Book III

- **Postulate 5.** Every proposition of Book III comes after I.29, so any may rest on it.
  `check_fidelity.py` sets `FIRST_EUCLIDEAN` for Book III as for Book II.
- **Superposition** stays with I.4 and I.8. III.24 is proved without it: `placement`,
  which lays one segment on another, rests on I.4, I.7 and I.8 as propositions, and only
  III.24 and `Elements/BookIII/Arcs.lean` may cite it, which `check_fidelity.py` checks.
  **19 October 2026, correction.** III.24 makes no direct call to the rule; `placement`
  uses it through I.4 and I.8. Its certificate includes superposition through those
  propositions, so the earlier phrase "without it" does not describe all its dependencies.
- **Citing earlier books.** A Book III proof cites `BookI.PropN` and `BookII.PropN`; a bare
  `Prop4` in a Book III file means III.4.
- **The scripts.** `heath.BOOKS` has Book III, 37 propositions, and `heath.parse_ref`
  reads "III.1 Por." as the porism of III.1; `render.py` writes `book/III/`, its sections
  of `CERTIFICATE.md` and `GRAPH.md`, and its titles and front page; every definition keeps
  its book, "Def. III.11", "Def. I.10". A bracket "[III. 1, Por.]" is read as citing III.1
  Por. A proposition Heath prints wholly in brackets (III.12) keeps its opening bracket in
  its heading, and its page shows it before the enunciation (`heath.bracketed`).
  `scaffold_book.py` has `BOOK_III`, the porisms, and imports Book III's circumference
  ground from III.23 on (`LATER_GROUNDWORK`). `Certificate/Facts.lean` lists Book III, and
  gives each porism an entry of its own.

## Exceptions

The review records in `review/III/` are the authority, proposition by proposition, and
each page shows its own in the line under the enunciation and the table under "In Lean".
This table is generated from them as they stand on 17 October 2026, with III.15 as it
stands on 18 October, III.24, III.26 and III.28 as stage 3 of
[brief 0006](0006-statements.md) leaves them, III.14, III.15 and III.25 as its stage 4
leaves them, and III.7, III.8 and III.17 as stage 4b of
[brief 0007](0007-stage-4b.md) leaves them (the centre given by hypothesis, `centre-given`,
is left out, being nearly everywhere):

19 October 2026: the table below preserves the earlier record snapshot. Circle 2,
`inside_of_between`, is now proved from Circle 3 in `Elements/Figure/Circles.lean`.
III.2's current axiom overlap is with Circle 3, `outside_of_between`, which gives it
at once; the published proof still follows Euclid without that axiom.

24 October 2026: Circle 3 is no longer an axiom. It is proved after III.2, from
`Prop2.within`, in `Elements/BookIII/Prop02.lean`, with Circle 2 beside it (#294), so both
of III.2's catalogued overlaps are with proved rules now, and its row is among the former
overlaps; the table keeps its earlier snapshot.

| Proposition | Statement | Argument | Overlap | Tags | Planned |
|---|---|---|---|---|---|
| [III.2](../../book/III/02.md) | whole | Euclid's | `inside_of_between` |  | kept, and catalogued |
| [III.5](../../book/III/05.md) | whole | one step changed | `circle_eq` |  | kept, and catalogued |
| [III.6](../../book/III/06.md) | whole | one step changed | `circle_eq`, `centre_inside` |  | kept, and catalogued |
| [III.7](../../book/III/07.md) | whole | Euclid's |  |  | done in stage 4b: compared on either side of AD (`Prop7.general`) |
| [III.8](../../book/III/08.md) | whole | one step changed |  |  | done in stage 4b: compared on either side of DA, within each class (`Prop8.general`) |
| [III.9](../../book/III/09.md) | whole | Euclid's |  | `hypothesis-dropped` |  |
| [III.10](../../book/III/10.md) | whole | Euclid's |  | `hypothesis-dropped` |  |
| [III.14](../../book/III/14.md) | whole | Euclid's |  |  | done in stage 4: diameters, at distance zero (`Prop14.general`) |
| [III.15](../../book/III/15.md) | whole | Euclid's |  |  | done in stage 4: both clauses for every straight line (`Prop15.le_diameter`, `Prop15.nearer`) |
| [III.16](../../book/III/16.md) | in part: the angle clauses stay in Euclid's words | Euclid's |  | `mixed-angles-omitted` | kept: a deliberate limitation |
| [III.17](../../book/III/17.md) | whole | Euclid's |  |  | done in stage 4b: from any point not within the circle (`Prop17.general`) |
| [III.21](../../book/III/21.md) | whole | one step changed |  |  |  |
| [III.23](../../book/III/23.md) | whole | Euclid's |  | `segment-with-circle` |  |
| [III.24](../../book/III/24.md) | whole | one step changed |  | `segment-with-circle`, `redundant-hypothesis` | done in stage 3: congruent segments by placement, the radius proof kept as an alternative |
| [III.25](../../book/III/25.md) | whole | Euclid's |  | `segment-with-circle` | done in stage 4: a construction that sees only the segment, with `Prop25.complete` |
| [III.26](../../book/III/26.md) | whole | one step changed |  | `angle-measure` | done in stage 3: equal circles made to do work (`Arc.Congruent`) |
| [III.27](../../book/III/27.md) | whole | one step changed |  | `angle-measure`, `redundant-hypothesis` |  |
| [III.28](../../book/III/28.md) | whole | one step changed |  | `angle-measure` | done in stage 3: concludes congruent circumferences too |
| [III.29](../../book/III/29.md) | whole | one step changed |  | `angle-measure` |  |
| [III.30](../../book/III/30.md) | whole | Euclid's |  | `segment-with-circle`, `angle-measure` |  |
| [III.31](../../book/III/31.md) | in part: the angles of the segments stay in Euclid's words | Euclid's |  | `mixed-angles-omitted` | kept: a deliberate limitation |
| [III.33](../../book/III/33.md) | whole | Euclid's |  | `segment-with-circle` |  |
| [III.34](../../book/III/34.md) | whole | Euclid's |  | `segment-with-circle` |  |

**19 October 2026, centre inputs.** The dated table's omission of `centre-given`
records the former convention. Step 6 has removed that tag from every Book III record.
Named centres remain where the geometry uses them; `Prop1.within` is the approved
construction exception. The tag's definition in `review/terms.toml` awaits step 7.

**19 October 2026, III.5, III.6 and III.10.** The dated table above is superseded for
these three rows by brief 0008, section 7, landing before step 6. III.5 and III.6 cover
the whole enunciations with Euclid's route: they draw through a point within and use the
order of the points, without `circle_eq`. Their overlaps remain: Diagram-segment 2 with
Generalities 4 for III.5, with Generalities 3 as well for III.6. Two further rows give
III.5 by Definition I.15 with Diagram-segment 4 and a magnitude law, or Diagram-segment 3's
second half and Generalities 4. III.6 takes `touching-whole-circles`. III.10 keeps its whole
statement, with `hypothesis-dropped`, but its route becomes `modified`: its last step uses
`circle_eq`, since its circles may merely meet. The records of III.5 and III.6 carry stamps
at e707d55 from GPT-6 Astra (Codex), and III.10's a stamp at 97f6403e from Claude Opus
5.5, each an independent reader. III.11–III.13, read again for the changed meaning and
dependencies, carry stamps too: III.13's at e707d55 from GPT-6 Astra (Codex), and III.11's
and III.12's at 0130b26c from Claude Opus 5.5.

**19 October 2026, III.16 and III.31.** Their rows in the dated table are also superseded:
with their mixed-angle companions both now cover the whole enunciation, and carry
`mixed-angles-local` instead of `mixed-angles-omitted`. III.16's route is `modified` for
the companions' direct argument; III.31's remains `euclid`.

**25 October 2026, the table and the records (#462).** The table above is the snapshot of
its date. The records in `review/III/` are the authority, as its opening line says, and
each page's "In Lean" line and "Argument" row, with the generated
[Book III index](../../book/III/index.md), show each record's route now. At main
bedbba23e these rows differ from their records, some as the notes above already say; a
step changed is a `different` passage of the record:

- III.2: `modified`, one step changed, the centre D, from `exists_centre` (#131); no
  `[overlap]`, Circles 2 and 3 being proved rules.
- III.5: `euclid`; its overlap, `Tacit.circle_eq`, agrees.
- III.6: `euclid`; its overlap is `Tacit.circle_eq` alone; tag `touching-whole-circles`.
- III.8: `modified`, two steps changed.
- III.10: `modified`, one step changed.
- III.16: statement `full`, with its companions; `modified`, two steps changed; tag
  `mixed-angles-local`.
- III.17: `modified`, one step changed, the centre E, from `exists_centre` (#131).
- III.24: three steps changed; tags `segment-with-circle`, `angle-measure` and
  `redundant-hypothesis`.
- III.25: tags `segment-with-circle` and `angle-measure`.
- III.26, III.28 and III.29: two steps changed each.
- III.31: statement `full`, with its companions; `euclid`; tag `mixed-angles-local`.
- With no row: III.1, its overlap `Tacit.exists_centre`; III.4, `modified`, one step
  changed, the centre F, from `exists_centre` (#131); and III.11, III.12 and III.13, tag
  `touching-whole-circles`.

**28 October 2026, the table and the records (#523).** The note of 25 October gives the
records' state at main bedbba23e; this list gives it at main 20d14b0a3, and the records in
`review/III/` remain the authority. These rows now differ from that note, or, where it is
silent, from the table; a step changed is still a `different` passage of the record:

- III.4: `euclid`, the centre F found by III.1's construction (#547).
- III.8: one step changed, its last step; the centre M is found by III.1's construction
  (#547).
- III.10: `euclid`, its last step by III.5, through `CirclesCut.of_meet` (#475).
- III.16: `euclid`, the angle clauses by Euclid's reductio from the second part (#547).
- III.17: `euclid`, the centre E found by III.1's construction (#547).
- III.18: tag `mixed-angles-local`, for its companions on the angle of contact (#130).
- III.20: tag `angle-measure`, for its companion `Prop20.circumference` (#129).
- III.21: `euclid`, Euclid's two steps for a segment of any size (#129).
- III.24: `euclid`, Euclid's application and his reductio (#547).
- III.26: one step changed, the congruence of the remainders (#129).

Book III's routes are still being worked on (#546, #547, #474), so this list too is of its
date.

The overlaps are in the [catalogue](../reports/overlaps.md). The planned work is brief
0005's ([0005-astra-review.md](0005-astra-review.md)); III.2's overlap remains catalogued,
and the mixed-angle comparisons have the scope described above.

## Later

- **Adding circumferences.** IV.11 adds circumferences ("let BCD be added to each") and
  IV.16 takes a fifth and a third of a circle. The measure adds as angles do, but the fact
  that a circumference cut at a point of it is the two circumferences it is cut into is not
  yet proved; Book IV's ground will want `Circumference.add`, from III.21 and the angles at
  a point of the remaining circumference. (18 October 2026: proved in stage 3 of
  [brief 0006](0006-statements.md), `Circumference.add` in
  `Elements/BookIII/Circumferences.lean`.)
- **VI.33**, "angles have the same ratio as the circumferences", becomes short with the
  measure. Book VI's design should revisit circumferences then. `circumference` and
  `standing` are angles in Lean: `Prop25.kind` compares a circumference with two right
  angles, while III.24's companions and III.26–III.30 compare circumferences with one
  another. A type of their own over `Angle` would forbid comparisons with angles
  without new rules; every law of magnitudes, now axioms about `Magnitude k`, would have to
  be proved again for it. The captain's call.
- **A circle's centre.** Brief 0008's step 6 has removed existence-only centre inputs.
  Named centres with geometric roles and the approved `Prop1.within` exception remain.
- A gap catalogue for Book III. (It now exists:
  [gaps-book-III.md](../reports/gaps-book-III.md), and Book III's index page links it.)
