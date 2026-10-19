# Book III: circles

*The design for Book III (16 October 2026, brought up to date on 17 October): how Lean
says Book III's words, where the facts about them live, and how its thirty-seven
propositions are stated. The code states what we formalized; where the code, this brief,
a review record and the pages disagree, the disagreement is recorded and every document
it touches is reconciled ([FORMALIZATION.md](../FORMALIZATION.md), section 1). The first
mate's working detail, one note per proposition, is in
[first-mate-III.md](../reports/crew/first-mate-III.md).*

## What Book III needs

Book I draws circles and reads off them; Book III is about them. It finds a circle's
centre, compares the straight lines in it and from a point to it, makes circles and
straight lines touch, measures the angles that stand on its circumferences, and in
III.26–III.30 compares the circumferences themselves:

> In equal circles equal angles stand on equal circumferences, whether they stand at the
> centres or at the circumferences. (III.26)

Three things in it do not fit what Books I and II built. Our circles have no centre
unless a hypothesis gives one. A circumference is a magnitude to Euclid, compared,
added and taken away, and we have only lengths, angles and areas. And twice (III.16,
III.31) he speaks of angles "contained by a straight line and a circumference", which
our angles, each made by two straight lines, are not.

## The words

The definitions are in `Elements/Foundations/DefinitionsIII.lean`. None is an
assumption.

| Euclid | Lean | Used in |
|---|---|---|
| Def. 1, equal circles | `EqualCircles α β`: a radius of the one is equal to a radius of the other | III.24, III.26–III.29 |
| Def. 2, a straight line touching a circle | `Touches A B α`: `AB` meets the circle, and, produced either way, does not cut it (`¬ LineMeetsCircle`) | III.16 Por., III.17–III.19, III.32, III.36, III.37 |
| Def. 3, circles touching | `TouchesInternally α β C` (they meet at `C`, are two circles, and no point of `β` is outside `α`), `TouchesExternally α β C` (they meet at `C`, and no point is within both), `CirclesTouch` (either within the other, or without) | III.6, III.11–III.13 |
| Defs. 4, 5, equally distant, at a greater distance | no word: `‖E F‖ = ‖E G‖`, `‖E H‖ < ‖E K‖` for the feet of the perpendiculars from the centre `E` | III.14, III.15 |
| Def. 6, a segment | no word: a circle, a straight line `AB` in it, and a point `E` of the circumference on one side, "the segment AEB" | III.23–III.25, III.33, III.34 |
| Def. 7, the angle of a segment | none: a mixed angle; no proof uses it | (III.16, III.31: the mishnah) |
| Def. 8, the angle in a segment | `∠ A E B`, `E` on the circumference of the segment | III.21 on |
| Def. 9, the angle standing on a circumference | `standing α B A C`, the circumference on which the angle `BAC` stands | III.27, III.30 |
| (Def. 6, 9) the circumference BKC | `circumference α B K C`: the part of `α` from `B` to `C` on `K`'s side of `BC` | III.24, III.26, III.28, III.29 |
| Def. 10, a sector | none: no proposition of Book III uses it | |
| Def. 11, similar segments | no word: `∠ A E B = ∠ C F D`, equal angles in them | III.23, III.24, III.26 |

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

**Circumferences.** Euclid compares circumferences only in one circle or in equal circles:
III.26–III.30, IV.11 and IV.16, and VI.33. A new kind of magnitude for them would need
new tacit rules, among them a rule of superposition for segments, and System E has
none, and we add no axiom for Book III. So a circumference is measured, by a
definition, as Definition 9 suggests: by the angle that stands on it at the
circumference, taken twice.

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
  `redundant-hypothesis` and `angle-measure`.)
- III.24's second conclusion, the equal measures, likewise follows from its equal
  angles alone; its first, equal circles, is the real content. It proves equal circles
  and equal measures, not that one segment can be laid on the other (below).
- The facts Euclid takes for granted about circumferences (that a circumference and the
  one remaining make up the circle; that the less is less than a semicircle) are proved
  from III.20–III.22, in `Elements/BookIII/Circumferences.lean`, and so a proposition that
  uses them cites those three.

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
angles, and Heath's account of the quarrel over the horn-like angle, go to the
mishnah. In the proofs, Euclid's sentences about them stand as comments with no Lean
beneath them, and each page says so.

## Circles and their centres

A circle in Lean has a centre only when a hypothesis gives one: `Postulate3` makes each
circle with its centre, and nothing says that a circle given otherwise has one. Simson
observed that the proof of III.1 must be by *reductio ad absurdum*, and Heath explains
why: "At the beginning of Book III. we have nothing more to base the proof upon than the
definition of a circle, and this cannot be made use of unless we assume some point to be
the centre" (vol. 2, p. 8). So:

- Where Euclid's setting-out names the centre, or speaks of a straight line through it,
  the centre is a hypothesis in Heath's letter: `Centre E ABCD` in III.7, `Centre F ABC`
  in III.18.
- Where the enunciation itself measures from the centre, the centre is a hypothesis too:
  III.14 and III.15, "equally distant from the centre" and "nearer to the centre"
  (Definitions 4 and 5), with the feet of the perpendiculars from it. III.15's setting-out
  names it, "E the centre". III.14's takes it "[III. 1]": its proof finds a centre by
  III.1 and that it is `E` (`centre_unique`), so that the bracket is cited, as in III.4
  and III.8.
- Otherwise the circle comes with `∃ O, Centre O α`, in Heath's letter for the centre
  where he has one (`∃ D, Centre D ABC` in III.2, where "let it be D"), and the proof takes
  the centre by III.1 under Euclid's "[III. 1]". III.1 needs two points of the circle;
  where the statement gives none (III.17), the proof first finds two on a straight line
  through the given centre (System E, Intersections 4 and 5), and identifies III.1's
  centre with it.
- "Not through the centre" in III.4 and "through the centre" in III.8 are said of every
  centre (`∀ F, Centre F ABCD → ¬ Collinear A C F`), with the circle's centre given
  besides: the proof then takes it by III.1, as Euclid does.

III.1 itself finds the centre of a circle that has one: given two points `A`, `B` of the
circle, it constructs `D`, `C`, `E` and `F` as Euclid does and concludes `Centre F ABC`.
The statement is the problem's answer with its construction; its content is the reductio,
which shows that the point found is the centre, the circle having some centre `G`.

## Where the facts live

The rule is Books I and II's: a fact that needs no proposition goes in Book Zero; one that
cites a proposition goes beside the propositions, and its docstring ends with what it
cites.

**Book Zero, `Elements/Figure/OnCircles.lean`** (cites no proposition, declares no axiom):
`Triangle.of_onCircle` (three points of a circle are not on one straight line),
`exists_onCircle_oppositeSidesOf`, `exists_onCircle_sameSideOf` (a straight line in a
circle has points of it on each side), `circumference_congr`, `standing_congr`,
`standing_eq_circumference`, `EqualCircles.radii`, `.symm`, `.refl`, `Touches.not_inside`,
`Touches.of_collinear`.

**Book III's ground, before III.1, `Elements/BookIII/Squares.lean`**: `sq_pos` (the square
on a straight line is something) and `BookI.Prop46.sq` (equal squares are on equal
straight lines), for III.14 and III.37, which add I.3, I.4, I.28, I.34, I.46; and
`foot_between` (the perpendicular from the centre to a straight line in the circle falls
between its ends), for III.14, III.35 and III.36 before they cite III.3, which adds I.17
and I.19. The file imports Book II's ground, so every proposition of Book III has `rect`,
`sq` and `BookI.Prop47.sq`.

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

`Circumference.semicircle` proves of circumferences, by Euclid's own argument, what III.31
proves of the angle in a semicircle: III.28 and III.29 need it first. It argues at the
point that measures the circumference, so it needs only I.5 and I.32, not III.21.

**Porisms.** Two corollaries are cited by later propositions, and are theorems of their
own, after their propositions: `Prop1.porism` (the centre lies on a straight line
bisecting a straight line in the circle at right angles; III.9, III.10) and
`Prop16.porism` (the straight line at right angles to a radius at its end touches the
circle; III.17, III.33, III.37 and Book IV). Since brief 0005's stage 1, each porism is an
entry of its own in the certificate, "III.1 Por." and "III.16 Por.", with its own axioms,
citations and status, and every policy check applies to it as to a proposition. Heath's
"[III. 1, Por.]" and "[III. 16, Por.]" are read as citations of those entries, by the
scripts and by `Certificate/Facts.lean` alike, and the graph draws a porism as its
proposition. A proposition counts as proved only when its porism is too, and its page
shows the porism's certificate in a column of its own. III.1 Por. rests on one rule III.1
does not, that a circle has one centre (`centre_unique`). Each porism's proof cites its
proposition, "from this it is manifest".

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
| "the segment AEB is equal to the segment CFD" (III.24) | `EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D` |
| "similar segments ACB, ADB" | `∠ A C B = ∠ A D B` |
| "the given segment ABC" (III.25), "the given circumference ADB" (III.30) | the circle, the straight line `AC` (or `AB`), and a point `P` on the side of the segment, for every such `P` |

Hypotheses come from the setting-out and conclusions from "I say that", with these choices
worth naming. The first mate's report has a note on every statement.

- **III.3** speaks of "a straight line CD through the centre". The straight line through
  the centre `E` and the point `F` is `FE`, and so the statement is said of `E` and `F`;
  `C` and `D`, its ends on the circle, need no Lean name. Citers (III.4, III.14, III.35,
  III.36) have a centre and a point, never the ends.
- **III.5, III.6** take two different circles (`ABC ≠ CDG`); a circle cuts itself, and has
  its own centre.
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
  `D` is; and III.25 cites III.9 for a point not yet known to be within, the centre found
  beyond the segment.
- **III.10** concludes that the two circles are one, `ABC = DEF`, from three common
  points, as I.7 concludes `C = D`. Heath names four points; the proof uses three.
- **III.11, III.12** conclude where the centres and the point of contact lie:
  `Between F G A` within, `Between F A G` without. III.12 is printed in square brackets by
  Heath, as Heron's proof made into a proposition; it is stated and proved like the rest.
- **III.14** also asks that neither straight line pass through the centre, as Euclid's
  proof does when it takes "a straight line AB not through the centre" (III.3). So its
  statement leaves out diameters, at no distance from the centre, though the
  enunciation covers them; the review record tags it `diameters-excluded`, and brief
  0005's stage 4 adds them.
- **III.14, III.15** take the centre and the feet of the perpendiculars as hypotheses,
  since Definitions 4 and 5 measure from them; III.14's proof takes the centre by III.1
  all the same (above). The perpendiculars are given, so I.12 is not cited; that the feet
  fall within the straight lines is `foot_between`.
- **III.15** says "the diameter is greatest" together with the more remote `FG` and
  `‖E H‖ < ‖E K‖`, as Euclid does: his proof that `AD` is greater than `BC` goes through
  `MN`, made on `EK` by cutting off `EL` equal to the less `EH` (I.3), so it uses the
  more remote straight line. No later proposition cites III.15.
- **III.16** states what Euclid proves by straight lines: the straight line at right
  angles to the diameter at its end falls outside, and every other straight line through
  that end passes within. The mixed angles go to the mishnah.
- **III.20** takes the centre on the side of `BC` where `A` is, "the angles having the same
  circumference as base": then the angle at the centre is less than two right angles, as
  Euclid's angles are. Heath observes that Euclid "had no idea of III. 20 applying ... to
  the case where the angle at the circumference ... is obtuse" (vol. 2, p. 48). The
  statement covers both of Euclid's cases, drawn in his one figure, the centre within the
  angle `BAC` and outside the angle `BDC`, and the case he leaves out, the centre on one
  of the arms.
- **III.21** is said of any segment. Euclid's proof covers the segment greater than a
  semicircle; Heath gives Simson's for the rest (vol. 2, pp. 49–50), and III.22 and Book IV
  need every segment.
- **III.22** takes a quadrilateral in the circle as four points of it with the straight line
  `BD` (joining opposite corners) separating `A` from `C`; that `AC` separates `B` from `D`
  follows.
- **III.23** concludes that the circles are one, `ACB = ADB`: on one straight line and on
  one side, similar segments coincide.
- **III.24** concludes that the circles are equal and the circumferences of the segments
  equal in measure. That is less than Euclid's equal segments: it does not say that one
  segment can be laid on the other, and the equal measures follow from the equal angles
  alone (above). Euclid proves it by applying one segment to the other, and our Lean
  allows superposition only in I.4 and I.8. III.24 is proved without applying one
  segment to another; [the scratch proof](https://github.com/jackChallis/stoicheia/blob/81d72f5/docs/reports/crew/scratch-III/T24.lean) does so, by the angles
  at the centres (III.20, III.22) and the isosceles triangles on the equal bases (I.5,
  I.26, I.32).
- **III.25** finds the centre of the circle of a given segment, with Euclid's construction
  and his three cases: the centre beyond the segment, at `D`, or within it, as the angle
  `ABD` is greater than, equal to, or less than `BAD`. A segment here is its circle, a
  straight line in it and a side, so III.25 is handed the whole circle, with a centre,
  and not the segment alone; the review record tags it `segment-with-circle`, and brief
  0005's stage 4 gives the construction the segment only.
- **III.26** says both of Euclid's cases as he enunciates them, "whether they stand at the
  centres or at the circumferences": equal angles at the centres (the circumferences less
  than semicircles) give equal circumferences, and so do equal angles at the
  circumferences, of any size. IV.11 cites the second. As stated it holds for any two
  circles (above).
- **III.27** likewise: equal circumferences give equal angles at the circumferences, of
  any size (IV.11 needs obtuse ones), and equal angles at the centres where those stand on
  them. As stated it, too, holds for any two circles.
- **III.28** asks of "the greater" only that it be no less (`≤`), so that two diameters,
  which Heath says the proposition covers "as the proof can easily be supplied" (vol. 2,
  p. 60), cut off semicircles.
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
- **III.33, III.34** construct the circle with its centre, so that what they make can be
  used.
- **III.36, III.37 (19 October 2026).** `Prop36.through_centre` carries III.36's diameter
  calculation through cancellation and is shared with `Prop37.centre_on_secant`. III.37
  now selects the centre-on-AC case explicitly, then retains its general argument in the
  other branch, including III.17 and III.1. This makes an already covered case explicit;
  both statements retain full scope. The helpers require no companion registration. The
  statements of `Prop36.through_centre` and `Prop37.centre_on_secant` were challenged by an
  independent reader who wrote neither statement, and approved as written by the
  coordinator.

## Book I and II's rules, in Book III

- **Postulate 5.** Every proposition of Book III comes after I.29, so any may rest on it.
  `check_fidelity.py` sets `FIRST_EUCLIDEAN` for Book III as for Book II.
- **Superposition** stays with I.4 and I.8. III.24 is proved without it.
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
stands on 18 October, and III.7, III.8 and III.17 as stage 4b of
[brief 0007](0007-stage-4b.md) leaves them (the centre given by hypothesis, `centre-given`,
is left out, being nearly everywhere):

| Proposition | Statement | Argument | Overlap | Tags | Planned |
|---|---|---|---|---|---|
| [III.2](../../book/III/02.md) | whole | Euclid's | `inside_of_between` |  | kept, and catalogued |
| [III.5](../../book/III/05.md) | whole | one step changed | `circle_eq` |  | kept, and catalogued |
| [III.6](../../book/III/06.md) | whole | one step changed | `circle_eq`, `centre_inside` |  | kept, and catalogued |
| [III.7](../../book/III/07.md) | whole | Euclid's |  |  | done in stage 4b: compared on either side of AD (`Prop7.general`) |
| [III.8](../../book/III/08.md) | whole | one step changed |  |  | done in stage 4b: compared on either side of DA, within each class (`Prop8.general`) |
| [III.9](../../book/III/09.md) | whole | Euclid's |  | `hypothesis-dropped` |  |
| [III.10](../../book/III/10.md) | whole | Euclid's |  | `hypothesis-dropped` |  |
| [III.14](../../book/III/14.md) | restricted: straight lines not through the centre | Euclid's |  | `diameters-excluded` | stage 4: diameters, at distance zero |
| [III.15](../../book/III/15.md) | restricted: the diameter's bound only beside a more remote straight line | Euclid's |  |  | stage 4: both clauses for every straight line |
| [III.16](../../book/III/16.md) | in part: the angle clauses stay in Euclid's words | Euclid's |  | `mixed-angles-omitted` | kept: a deliberate limitation |
| [III.17](../../book/III/17.md) | whole | Euclid's |  |  | done in stage 4b: from any point not within the circle (`Prop17.general`) |
| [III.21](../../book/III/21.md) | whole | one step changed |  |  |  |
| [III.23](../../book/III/23.md) | whole | Euclid's |  | `segment-with-circle` |  |
| [III.24](../../book/III/24.md) | in part: equal circles and measures; the segments stay in Euclid's words | different |  | `segment-with-circle`, `angle-measure`, `redundant-hypothesis` | stage 3: congruent segments by placement, the radius proof kept as an alternative |
| [III.25](../../book/III/25.md) | restricted: handed the whole circle and its centre | Euclid's |  | `segment-with-circle` | stage 4: a construction that sees only the segment |
| [III.26](../../book/III/26.md) | whole | one step changed |  | `angle-measure`, `redundant-hypothesis` | stage 3: equal circles made to do work (`Arc.Congruent`) |
| [III.27](../../book/III/27.md) | whole | one step changed |  | `angle-measure`, `redundant-hypothesis` |  |
| [III.28](../../book/III/28.md) | whole | Euclid's |  | `angle-measure` | stage 3: concludes congruent arcs too, through III.26 |
| [III.29](../../book/III/29.md) | whole | one step changed |  | `angle-measure` |  |
| [III.30](../../book/III/30.md) | whole | Euclid's |  | `segment-with-circle`, `angle-measure` |  |
| [III.31](../../book/III/31.md) | in part: the angles of the segments stay in Euclid's words | Euclid's |  | `mixed-angles-omitted` | kept: a deliberate limitation |
| [III.33](../../book/III/33.md) | whole | Euclid's |  | `segment-with-circle` |  |
| [III.34](../../book/III/34.md) | whole | Euclid's |  | `segment-with-circle` |  |

The overlaps are in the [catalogue](../reports/overlaps.md). The planned work is brief
0005's ([0005-astra-review.md](0005-astra-review.md)); III.16 and III.31's mixed angles,
and III.2's kind of overlap, are the deliberate limitations Book III keeps.

## Later

- **Adding circumferences.** IV.11 adds circumferences ("let BCD be added to each") and
  IV.16 takes a fifth and a third of a circle. The measure adds as angles do, but the fact
  that a circumference cut at a point of it is the two circumferences it is cut into is not
  yet proved; Book IV's ground will want `Circumference.add`, from III.21 and the angles at
  a point of the remaining circumference.
- **VI.33**, "angles have the same ratio as the circumferences", becomes short with the
  measure. Book VI's design should revisit circumferences then. `circumference` and
  `standing` are angles in Lean: no statement of Book III equates one with an angle or
  adds one to an angle (they are compared only with each other, in III.24 and
  III.26–III.30), but a statement could. A type of their own over `Angle` would forbid it
  without new rules; every law of magnitudes, now axioms about `Magnitude k`, would have to
  be proved again for it. The captain's call.
- **A circle's centre.** If Definition 15's other half becomes a rule, the
  `∃ O, Centre O α` hypotheses can go.
- A gap catalogue for Book III. (It now exists:
  [gaps-book-III.md](../reports/gaps-book-III.md), and Book III's index page links it.)
