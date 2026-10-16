# Book III: circles

*The design for Book III (16 October 2026): how Lean says Book III's words, where the
facts about them live, and how its thirty-seven propositions are stated. Where it
differs from the code, the code is right. The first mate's working detail, one note per
proposition, is in [first-mate-III.md](../reports/crew/first-mate-III.md).*

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
| Def. 3, circles touching | `TouchesInternally α β C` (they meet at `C`, are two circles, and no point of `β` is outside `α`), `TouchesExternally α β C` (they meet at `C`, and no point is within both), `CirclesTouch` (one of the three) | III.6, III.11–III.13 |
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
`Touches.not_inside` (System E, Intersections 3).

**Touching, for circles.** Heath reads Definition 3 as "the circles meet at a point but do
not cut at that point" (vol. 2, p. 3), and observes that Euclid assumes in III.11–III.13,
without stating it, that circles touching at one point do not meet anywhere else. Read
"do not cut one another" as "have only one point in common", and III.13 would be the
definition. So Lean reads it as Heath's minimum admission does, for the whole circle:
touching within, no point of the inner circle falls outside the outer; touching without,
no point lies within both. Two circles touching within at two points, or without at two
points, is then exactly what III.13 refutes, by III.11 and III.2. III.11's statement says
which circle is within (`TouchesInternally ABC ADE A`, `ADE` within `ABC`); III.13 asks
for either.

**Circumferences.** Euclid compares circumferences only in one circle or in equal circles:
III.26–III.30, IV.11 and IV.16, and VI.33. A new kind of magnitude for them would need
new tacit rules, among them a rule of superposition for segments, and System E has
none; the first mate cannot add an axiom. So a circumference is measured, by a
definition, as Definition 9 suggests: by the angle that stands on it at the
circumference, taken twice.

`circumference α B K C` is `∠ B A C + ∠ B A C` for a point `A` of `α` on the other side of
`BC` from `K`; Lean chooses one such angle (`Classical.epsilon`), as `rect` chooses one
rectangle. It is the angle the circumference subtends at the centre when it is less than
a semicircle (III.20); a semicircle is two right angles, and the whole circle four. In one
circle, or in equal circles, two circumferences are equal exactly when these angles are,
and that is all Euclid asks of them. The statements that compare circumferences keep his
"in equal circles", and the proofs use it as he does: in III.26 "the radii are equal",
and the bases, by I.4.

`standing α B A C`, the circumference on which the angle `BAC` stands, is the same measure
named from the other side: the part of `α` cut off by `AB`, `AC`, away from `A`. Book
Zero proves that the two names agree (`standing_eq_circumference`) and that either may be
named from any point of its side (`circumference_congr`, `standing_congr`).

What this costs, and what it does not:

- The angle measure cannot tell circumferences of unequal circles apart. Euclid never
  compares them, so no statement of his says otherwise.
- Some of Euclid's conclusions become short by the measure. Equal angles at the
  circumferences give equal measures at once, in any two circles. Euclid's route to
  III.26 goes by I.4, III.24 and the whole circle, and the sailors are to take it; a
  proof that went by the measure alone would leave "in equal circles" unused, and Lean's
  linter would say so.
- The facts Euclid takes for granted about circumferences (that a circumference and the
  one remaining make up the circle; that the less is less than a semicircle) are proved
  from III.20–III.22, in `Elements/BookIII/Circumferences.lean`, and so a proposition that
  uses them cites those three.

If the captain would rather have circumferences as magnitudes of their own, with tacit
rules for adding them and for applying one segment to another, the statements need not
change: they speak of `circumference` and `standing`, and only the definitions and the
ground would.

**Mixed angles.** "The angle of the semicircle is greater, and the remaining angle less,
than any acute rectilineal angle" (III.16); "the angle of the greater segment is greater
than a right angle" (III.31). These angles are "contained by a straight line and a
circumference", and our angles, magnitudes of two straight lines, are not them. Euclid
proves them by rectilineal facts: in III.16, that no straight line can be interposed
between the circumference and the tangent, which is the second clause of III.16's
statement (every straight line through `A` other than `AE` passes within the circle); in
III.31, that the angles `BAC`, `CAF` are right. The Lean states those facts; the claims
about mixed angles, and Heath's account of the quarrel over the horn-like angle, go to the
mishnah.

## Circles and their centres

A circle in Lean has a centre only when a hypothesis gives one: `Postulate3` makes each
circle with its centre, and nothing says that a circle given otherwise has one. Simson's
remark under III.1 is exactly the point: "At the beginning of Book III. we have nothing
more to base the proof upon than the definition of a circle, and this cannot be made use
of unless we assume some point to be the centre" (Heath, vol. 2, p. 8). So:

- Where Euclid's setting-out names the centre, or speaks of a straight line through it,
  the centre is a hypothesis in Heath's letter: `Centre E ABCD` in III.7, `Centre F ABC`
  in III.18.
- Otherwise the circle comes with `∃ O, Centre O α`, in Heath's letter for the centre
  where he has one (`∃ D, Centre D ABC` in III.2, where "let it be D"), and the proof takes
  the centre by III.1 under Euclid's "[III. 1]".
- "Not through the centre" in III.4 and "through the centre" in III.8 are said of every
  centre (`∀ F, Centre F ABCD → ¬ Collinear A C F`), with the circle's centre given
  besides: the proof then takes it by III.1, as Euclid does.

III.1 itself finds the centre of a circle that has one: given two points `A`, `B` of the
circle, it constructs `D`, `C`, `E` and `F` as Euclid does and concludes `Centre F ABC`.
The statement is the problem's answer with its construction; its content is the reductio,
which shows that the point found is the centre, the circle having some centre `G`.
If the captain adds Definition 15's other half (a circle has a centre) as a rule, every
`∃ O, Centre O α` can go.

## Where the facts live

The rule is Books I and II's: a fact that needs no proposition goes in Book Zero; one that
cites a proposition goes beside the propositions, and its docstring ends with what it
cites.

**Book Zero, `Elements/Figure/Chords.lean`** (cites no proposition, declares no axiom):
`Triangle.of_onCircle` (three points of a circle are not on one straight line),
`exists_onCircle_oppositeSidesOf`, `exists_onCircle_sameSideOf` (a straight line in a
circle has points of it on each side), `circumference_congr`, `standing_congr`,
`standing_eq_circumference`, `EqualCircles.radii`, `.symm`, `.refl`, `Touches.not_inside`,
`Touches.of_collinear`.

**Book III's ground, before III.1, `Elements/BookIII/Squares.lean`**: `sq_pos` (the square
on a straight line is something) and `BookI.Prop46.sq` (equal squares are on equal
straight lines), for III.14 and III.37. They add I.3, I.4, I.28, I.34, I.46. The file
imports Book II's ground, so every proposition of Book III has `rect`, `sq` and
`BookI.Prop47.sq`.

**Book III's ground, after III.22, `Elements/BookIII/Circumferences.lean`**, imported by
III.23–III.37:

| Lemma | What Euclid takes for granted | Adds |
|---|---|---|
| `Circumference.eq` | a circumference is twice the angle at any point of the other segment | III.21 |
| `Circumference.standing` | the circumference on which `BAC` stands is twice `BAC` | III.21 |
| `Circumference.centre` | a circumference beyond which the centre lies is its angle at the centre | III.20, III.21 |
| `Circumference.whole` | the two circumferences on a straight line make up the whole circle, four right angles | III.21, III.22 |
| `Circumference.semicircle` | a semicircle is two right angles | I.5, I.32 |
| `Circumference.lt_semicircle`, `.gt_semicircle` | the circumference beyond the centre is less than a semicircle, the one on the centre's side greater | I.32, III.20–III.22 |

`Circumference.semicircle` proves of circumferences, by Euclid's own argument, what III.31
proves of the angle in a semicircle: III.28 and III.29 need it first.

**Porisms.** Two corollaries are cited before their propositions are proved, so their
statements are fixed now, after their propositions: `Prop1.porism` (the centre lies on a
straight line bisecting a straight line in the circle at right angles; III.9, III.10) and
`Prop16.porism` (the straight line at right angles to a radius at its end touches the
circle; III.17, III.33, III.37 and Book IV). Heath's "[III. 1, Por.]" and
"[III. 16, Por.]" are read as citations of III.1 and III.16, and each porism's proof should
cite its proposition, so that the certificate agrees.

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
  at the point with the straight line through the centre, on one side of it. Heath
  discusses the other readings and prefers Euclid's (vol. 2, pp. 15–16). III.8 says which
  lines fall on the concave and which on the convex circumference by where the straight
  line from `D` meets the circle again.
- **III.10** concludes that the two circles are one, `ABC = DEF`, from three common
  points, as I.7 concludes `C = D`. Heath names four points; the proof uses three.
- **III.11, III.12** conclude where the centres and the point of contact lie:
  `Between F G A` within, `Between F A G` without. III.12 is printed in square brackets by
  Heath, as Heron's proof made into a proposition; it is stated and proved like the rest.
- **III.16** states what Euclid proves by straight lines: the straight line at right
  angles to the diameter at its end falls outside, and every other straight line through
  that end passes within. The mixed angles go to the mishnah.
- **III.20** takes the centre on the side of `BC` where `A` is, "the angles having the same
  circumference as base": then the angle at the centre is less than two right angles, as
  Euclid's angles are. Heath observes that Euclid "had no idea of III. 20 applying ... to
  the case where the angle at the circumference ... is obtuse" (vol. 2, p. 48). The
  statement covers both of Euclid's figures, the centre within the angle `BAC` and
  outside it, and the case he leaves out, the centre on one of its arms.
- **III.21** is said of any segment. Euclid's proof covers the segment greater than a
  semicircle; Heath gives Simson's for the rest (vol. 2, pp. 49–50), and III.22 and Book IV
  need every segment.
- **III.22** takes a quadrilateral in the circle as four points of it with the diameter
  `BD` separating `A` from `C`; that `AC` separates `B` from `D` follows.
- **III.23** concludes that the circles are one, `ACB = ADB`: on one straight line and on
  one side, similar segments coincide.
- **III.24** concludes that the circles are equal and the circumferences of the segments
  equal. Euclid proves it by applying one segment to the other; Lean has no superposition
  outside I.4 and I.8, and proves it by the angles at the centres (III.20, III.22) and the
  isosceles triangles on the equal bases (I.5, I.26, I.32). The scratch proof does so.
- **III.25** finds the centre of the circle of a given segment, with Euclid's construction
  and his three cases: the centre beyond the segment, at `D`, or within it, as the angle
  `ABD` is greater than, equal to, or less than `BAD`.
- **III.26** says both of Euclid's cases as he enunciates them, "whether they stand at the
  centres or at the circumferences": equal angles at the centres (the circumferences less
  than semicircles) give equal circumferences, and so do equal angles at the
  circumferences, of any size. IV.11 cites the second.
- **III.27** likewise: equal circumferences give equal angles at the circumferences, of
  any size (IV.11 needs obtuse ones), and equal angles at the centres where those stand on
  them.
- **III.28** asks of "the greater" only that it be no less (`≤`), so that two diameters,
  which Heath says the proposition covers "as the proof can easily be supplied" (vol. 2,
  p. 60), cut off semicircles.
- **III.29** is said of circumferences of any size; Euclid's proof covers those less than
  a semicircle, and Heath the semicircles.
- **III.31** keeps Euclid's figure: `BC` the diameter, `A` on the circle. "The angle in a
  greater segment" is said of the segment `ABC`, as he does, and "that in a less segment"
  of every point `D` of the circumference on the other side of `AC` from `B`, so that a
  citer who wants only the right angle (III.32, III.33) need name no `D`.
- **III.32** concludes for every angle in each alternate segment, "the angle constructed
  in the segment BAD": the proof constructs Euclid's `A` and moves to any other point by
  III.21.
- **III.33, III.34** construct the circle with its centre, so that what they make can be
  used.

## Book I and II's rules, in Book III

- **Postulate 5.** Every proposition of Book III comes after I.29, so any may rest on it.
  `check_fidelity.py` sets `FIRST_EUCLIDEAN` for Book III as for Book II.
- **Superposition** stays with I.4 and I.8. III.24 is proved without it.
- **Citing earlier books.** A Book III proof cites `BookI.PropN` and `BookII.PropN`; a bare
  `Prop4` in a Book III file means III.4.
- **The scripts.** `heath.BOOKS` has Book III, 37 propositions; `render.py` writes
  `book/III/`, its sections of `CERTIFICATE.md` and `GRAPH.md`, and its titles and front
  page; Book III's own definitions are written "Def. 11", another book's "Def. I.10". A
  bracket "[III. 1, Por.]" is read as citing III.1. `scaffold_book.py` has `BOOK_III`, the
  porisms, and imports Book III's circumference ground from III.23 on
  (`LATER_GROUNDWORK`). `Certificate/Facts.lean` lists Book III. Books I and II render
  byte for byte as tagged.

## Later

- **Adding circumferences.** IV.11 adds circumferences ("let BCD be added to each") and
  IV.16 takes a fifth and a third of a circle. The measure adds as angles do, but the fact
  that a circumference cut at a point of it is the two circumferences it is cut into is not
  yet proved; Book IV's ground will want `Circumference.add`, from III.21 and the angles at
  a point of the remaining circumference.
- **VI.33**, "angles have the same ratio as the circumferences", becomes short with the
  measure. Book VI's design should revisit circumferences then.
- **A circle's centre.** If Definition 15's other half becomes a rule, the
  `∃ O, Centre O α` hypotheses can go.
- **The general III.31.** "The angle in a greater segment is acute" is stated for Euclid's
  segment `ABC`; if a later book needs it for any segment, it follows by III.21, as a
  corollary after III.31.
- A gap catalogue for Book III.
