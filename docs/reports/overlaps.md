# Overlaps: where a rule already says what Euclid proves

19 October 2026: eight axioms have become theorems with their names and exact types
unchanged, and 31 more followed the same day. The lock now holds 48 axioms, including 42
tacit rules. Their [derivations and homes](../FORMALIZATION.md#rules-now-proved) explain
what each proof uses. The current catalogue below distinguishes the remaining axiom overlaps from
the former ones. The earlier catalogue and its measurements follow as history.

## Current axiom overlaps

| Proposition | Assumption | Kind | First enters | Audit lemma |
|---|---|---|---|---|
| I.2 | Superposition (`superposition`) | Supplies a step of the alternative proof | I.4 | `Audit.I_2` |
| I.3 | Superposition (`superposition`) | Supplies a step of the alternative proof | I.4 | `Audit.I_3` |
| I.13, a consequence used in I.47 | Metric 5 (`angle_le_two_right`) | Supplies a step: the upper bound on an angle | I.47 | None |
| I.23 | Superposition (`superposition`) | Supplies a step of the alternative proof | I.4 | `Audit.I_23` |
| III.2 | Circle 3 (`outside_of_between`) | Gives it at once: if the middle point were not inside, the second endpoint would be outside | Nowhere: no certificate entry rests on it | `Audit.III_2_outside`; `Audit.III_2` through the derived Circle 2 |
| III.5 | Diagram-segment 2 (`circle_eq`) | Gives it at once: circles about one centre through one point coincide | I.1, through proved rules including `centre_inside` | `Audit.III_5` |
| III.6 | Diagram-segment 2 (`circle_eq`) | Gives it at once for contact within; contact without is settled by Generalities 3, a former assumption now proved (below) | I.1, through proved rules including `centre_inside` | `Audit.III_6` |

"First enters" here includes the axioms of proved rules. I.1 reaches `circle_eq`
through `centre_inside` and `len_ne_zero`; III.5 is still the first proposition
whose own Lean names the axiom. III.5 and III.6 also reach it, and Postulate 3,
through the proved `centre_inside`. Their explicit calls to `circle_eq` distinguish
F from G and E from B; those calls are no longer their only paths to the axiom.

Fresh certificate facts at `1a2d37c1` show that no certificate entry rests on
Circle 3. I.12 finds X on AB between the centre C and the point D on the circle;
`InsideCircle.of_between_centre` puts X inside by comparing CX with the radius CD,
and Intersection 3 (`line_meets_circle_of_inside`), proved since 19 October 2026 in
`Elements/Figure/Incidence.lean`, supplies the two crossings E and G. The proved Intersection 2
(`line_meets_circle_of_opposite_sides`) has no user in `Elements/`, `Staging/` or
`Audit/`; its declaration in `Elements/Figure/Circles.lean` is the only occurrence
of its name there.

III.2 and its corollaries `Prop2.triangle`, `Prop2.oppositeSide` and
`Prop2.sameSide` also avoid Circle 3. Our III.2 follows Euclid through I.5, I.16
and I.19; its overlap with an available axiom is distinct from what its published
proof uses.

## Former axiom overlaps

| Former overlap | What now proves the rule |
|---|---|
| I.7 and Circle 4 (`not_same_side_of_circles_meet`) | I.7, Definition I.15 and `circle_eq`, after I.7 in `Elements/BookI/Prop07.lean`. `Audit.I_7` now reaches I.7 through its own corollary, so it is circular as an independent proof of I.7. |
| I.13's right-angle case and Diagram-angle 3 (`adjacent_eq_of_right`) | I.13 and Common Notion 3, after I.13 in `Elements/BookI/Prop13.lean`. The later proofs now use that theorem. |
| III.1's centre uniqueness and Generalities 2 (`centre_unique`) | The foundations, in `Elements/Figure/Circles.lean`: two supposed centres bisect the same straight line through the circle, and equal doubles have equal halves. III.1 Por. still calls the theorem, but its axiom closure is now the same as III.1's. |
| III.2 and Circle 2 (`inside_of_between`) | Circle 3, in `Elements/Figure/Circles.lean`. The remaining axiom overlap is the Circle 3 row above. |
| III.6's contact without and Generalities 3 (`centre_inside`) | A proof in `Elements/Figure/RuleBase.lean` (19 October 2026): a centre that were not inside its circle would have two unequal radii on one straight line. The radii are unequal because no radius is nothing (`RuleProofs.Circle.radius_ne_zero`, and `length_pos` over it), and that proof uses Postulate 3 and Diagram-segment 2 (`circle_eq`): a point at no distance from the centre would be on the circle. Lean reports, for `centre_inside`, Definition 15, Postulates 1 and 3 and 16 tacit rules, among them Circle 1, Diagram-segment 2, Intersections 4 and 5 and the rules of length and order. `Audit.III_6` now rests on that proof, and its pinned axioms are the same, so contact without rests on Diagram-segment 2 as contact within does; for both, the remaining axiom overlap is the Diagram-segment 2 row above. |

`Audit.outside_of_between`, which derives Circle 3 through Circle 2, now reaches the
Circle 3 axiom again. It does not retire that axiom. Circle 4 also uses
Diagram-segment 2, so the old alternative between those two assumptions in the
III.5 and III.6 discussion below now leaves Diagram-segment 2 as the retained axiom.
The duplicate-circle argument there remains an informal model argument, not a Lean
independence theorem.

The crossing proof `Audit.III_5_crossing` now rests on `circle_eq` too, through
the proved `len_lt_of_inside`. It still proves the statement with crossing as its
hypothesis, but no longer supplies the derivation without that axiom described
in the historical account below.

## Historical account, before 19 October 2026

The account below preserves the earlier readings, attributed findings and measured
counts. Its axiom statuses, first users and statements about current dependencies
are superseded by the dated catalogue above. In particular, the former seven-axiom
I.7 shortcut and the 17-proof right-angle census describe the earlier foundations.

Stoicheia takes the rules of System E (Jeremy Avigad, Edward Dean and John Mumma, 2009) as
its axioms, and a few of them already say what Euclid later proves, or give it in a few
lines. III.2 is the clearest case. System E's Circle 2 says that between two points on or
within a circle every point is within it, and III.2 is that rule for two points on the
circle. Astra pointed this out in the [outside review](outside-review-01.md), with a
one-line proof compiled in Lean, and asked for this catalogue. We are grateful. Two later
readings added to it, and we thank them too: a cold review by Claude saw that
superposition supplies the steps of I.2 and I.3, and Argon's second review corrected our
account of how each rule enters the proofs (the certificate counted a rule a proof reaches
through a lemma as one it calls itself, and now keeps the two apart), found defined words
that our screen left folded, and saw that III.30 belongs among the near misses.

A reconstruction that rests on such a rule does not establish the rule independently: it
shows that Euclid's reasoning goes through within System E, not that the proposition holds
without the rule. Our III.2 follows Euclid's argument, and it once rested so, through
III.1, on a rule at least as strong as its own conclusion; III.1 now takes that step by
Euclid's own argument for III.2, and no proposition rests on the rule. This catalogue
shows where System E gives early what Euclid later proves: which rule, where it first
enters the development, and how it reaches the proposition's own proof.

### The catalogue

Each row is one of three kinds:

- **States it**: the rule, read for the proposition's figure, is its statement, or says more.
- **Gives it at once**: the proposition follows from the rule in a short proof, from at
  most three rules, that cites no proposition. Any other rules in that proof only draw or
  name the figure.
- **Supplies a step**: inside some proof, the rule carries a step that is a proposition's
  content, or a case of it. The first column says which proposition, and in which proofs.
  For I.2, I.3, I.7 and I.23 the proof is the audit lemma: the rule carries the
  proposition's content, but the shortest proof we found from the rules alone takes ten,
  twenty-two, seven and eight of them, the rest drawing a figure the statement never
  mentions and telling its parts apart (and, for I.3, ordering three points by their
  lengths), which is more than "at once".

"First enters" names the first proposition, in Euclid's order, whose proof uses the rule
without taking it from a proposition it cites. It is read from
[facts.json](../../facts.json) as committed, which keeps the two ways apart
([Certificate/FIELDS.md](../../Certificate/FIELDS.md);
[issue #65](https://github.com/jackChallis/stoicheia/issues/65)): `own_axioms` lists the
rules a proof calls itself, those its own Lean or a helper written for its proposition
(`Prop47.within`, for I.47) names, and `inherited` the rules its own Lean does not name
but reaches through a lemma it calls, of Book Zero (`Elements/Figure/`) or a shared step,
each with the lemma that brings it in. A proposition it cites may rest on such a rule too.
Each first user in the table calls its rule itself. A later proof may rest on a rule it
never calls, as III.26 rests on Generalities 2 only through Book Zero's
`EqualCircles.radii`; III.28 and III.29 call that lemma too, and rest on the rule through
III.26 and III.27 as well, which they cite. The note under the table names the lemma the
rule comes through. Each proposition's page marks the same in its list of tacit rules:
"(used here)" for a rule its own Lean calls, and the lemmas for one it inherits.

Each audit lemma is in [Audit/Overlaps.lean](../../Audit/Overlaps.lean), its type the
proposition's own, proved from the rules alone, with the axioms Lean reports for it
pinned beneath. Under the table, each row has a short note: the proofs that call the rule
themselves, the lemmas and entries through which it reaches the others, and what the Lean
proof does. The notes are read from Lean's proof terms; a search of `Elements/` for the
rule's Lean name finds the same calls.

| Proposition | Rule(s) | Kind | First enters | Audit lemma |
|---|---|---|---|---|
| [I.2](#i2-and-i3) | Superposition (`superposition`): a triangle can be laid down on a given ray, on a given side, keeping its sides and angles | Supplies a step, in `Audit.I_2`: laid down at A along AB, a triangle on BC carries the length of BC to A, and drawing that triangle and a point off AB takes nine axioms more | I.4 | `Audit.I_2` |
| [I.3](#i2-and-i3) | Superposition (`superposition`) | Supplies a step, in `Audit.I_3`: laid down at A along the ray AB, a triangle on the less straight line carries its length onto the ray, and drawing the figure and placing the new point between A and B takes twenty-one axioms more | I.4 | `Audit.I_3` |
| [I.7](#i7) | Circle 4 (`not_same_side_of_circles_meet`): two circles cut one another on opposite sides of the straight line through their centres | Supplies a step, in `Audit.I_7`: I.7 is the rule with its two circles left undrawn, and drawing them and telling them apart takes six rules more | Nowhere: no proof uses it | `Audit.I_7` |
| [I.13, a case of it, in 17 proofs from II.1 on](#i13-in-17-proofs) | Diagram-angle 3 (`adjacent_eq_of_right`): the angle beside a right angle is right | Supplies a step: I.13 makes the two angles two right angles, so the second is right | II.1 | `Audit.adjacent_eq_of_right` runs the other way: the rule, proved from I.13 |
| [I.13, a consequence of it, in I.47](#i13-in-i47) | Metric 5 (`angle_le_two_right`): no angle exceeds two right angles | Supplies a step: for an angle between two straight lines, I.13 gives it | I.47, its only user | None |
| [I.23](#i23) | Superposition (`superposition`): a triangle can be laid down on a given ray, on a given side, keeping its sides and angles | Supplies a step, in `Audit.I_23`: laid down at A along AB, the triangle DCE carries its angle at C to A, and naming the ray and the side takes seven axioms more | I.4 | `Audit.I_23` |
| [III.1's corollary, in III.1 Por.](#iii1-por) | Generalities 2 (`centre_unique`): a circle has only one centre | Supplies a step: "a proposition which, if thought necessary, may be added to III. 1 as a corollary" (Heath, vol. 2, p. 8) | III.1's porism; of the propositions themselves, III.14 | None |
| [III.2](#iii2) | Circle 2 (`inside_of_between`): between two points on or within a circle, every point is within it | States it, and more: the ends may be within the circle as well as on it | Nowhere: no proposition rests on it | `Audit.III_2`, Astra's proof: Circle 2 alone |
| [III.2](#iii2) | Circle 3 (`outside_of_between`): a straight line that has left a circle does not come back; Circle 2 turned round | Gives it at once: were a point between two points of the circle not within it, the second point would be outside the circle, not on it | Nowhere: no proposition rests on it | `Audit.III_2_outside`: Circle 3 alone |
| [III.5](#iii5) | Diagram-segment 2 (`circle_eq`): a circle is fixed by its centre and radius | Gives it at once: two circles about one centre through one point are one circle | III.5 | `Audit.III_5`: Diagram-segment 2 alone |
| [III.6](#iii6) | Diagram-segment 2 (`circle_eq`), and Generalities 3 (`centre_inside`): a circle's centre is within it | Gives it at once: circles touching within are two circles through one point; circles touching without have no point within both, and a common centre would be one | Diagram-segment 2: III.5. Generalities 3: I.1 | `Audit.III_6`: the two rules alone |

The review records point here: a proposition's `[overlap]` names its rule
([review/SCHEMA.md](../../review/SCHEMA.md)).

#### Row by row

##### I.2 and I.3

Nothing brings the rule into our I.2 or I.3, which come before I.4 and do not rest on it.
The proofs are Euclid's: I.2 by the equilateral triangle of I.1 and two circles, I.3 by
I.2 and a circle. Our Postulate 3 is Euclid's collapsing compass, and leaves carrying a
distance to I.2; superposition, in the form we take it, carries one. What keeps I.2
Euclid's is the certificate's policy, which lets only I.4 and I.8 use the rule.
`Audit.I_2` uses superposition with Postulates 1 and 3, Generalities 1 and 3, Points 7,
Intersections 5, Circle 1 and Between 1 and 7, which draw a triangle on BC and a point off
AB, since neither statement gives one. `Audit.I_3` draws the same way, and adds Between 6,
Diagram-segment 1, Metric 1 and the laws of magnitude, which put the new point between A
and B.

##### I.7

Nothing brings the rule into our I.7, which does not rest on it. The proof is Euclid's
argument, by I.5, with D in each of its four places (`Prop7.cases`). `Audit.I_7` uses
Circle 4, with Postulates 1 and 3, Diagram-segment 3, Same side 3, Metric 3 and
Generalities 2 to draw the circles and tell them apart.

##### I.13 in 17 proofs

Sixteen of the 17 proofs call the rule themselves: II.1, II.3, II.4, II.5, II.9, II.11,
II.14, III.3, III.10, III.15, III.16, III.17 and III.25 in their own Lean; III.9 in its
helper `Prop9.apart`; and III.1 and its porism in III.1's helper `Prop1.perpendicular`,
which shows that at a point of a straight line only one straight line is at right angles
to it. III.19 reaches the rule only through `Prop1.perpendicular`, which III.16 uses as
well as calling the rule itself. Twenty-five more entries (24 propositions and III.16's
porism) rest on it through these 17. I.13 does not rest on it. The rule gives the right
angles Euclid reads off his figure, as for the rectangles of II.1, where his text says
nothing of them.

##### I.13 in I.47

The rule comes in through `Prop47.within`, I.47's helper. It shows that AD does not cross
BC beyond B, where the angle ABD would exceed two right angles; the same case cites I.13
twice.

##### I.23

I.8 calls the rule itself, and I.20 rests on it through I.5 and I.4. Our proof is Euclid's
construction: a triangle from three straight lines (I.22), and I.8 for its angle. The
certificate lets only I.4 and I.8 use superposition. That limits where the rule is used,
not what it can do: as a construction principle it is stronger than System E's restricted
inference rule, whose placed points never become constructed ones
([Superposition.lean](../../Elements/Foundations/Tacit/Superposition.lean)).
`Audit.I_23` uses superposition, with Postulate 1, Generalities 1, Metric 1, Metric 4,
Points 1 and Same side 3 to name the ray and the side: eight axioms in all, since System
E's Metric 1 is two of ours.

##### III.1 Por.

III.1's porism calls the rule itself: it makes the centre III.1 finds the given centre,
so that it lies on the cutting straight line. III.14, III.17 and III.36 call it
themselves for the same step, making the centre III.1 finds the centre their statements
speak of. III.26 reaches it only through Book Zero's `EqualCircles.radii`, that equal
circles have equal radii: a circle has only one centre, so the centres the definition of
equal circles names are the given ones. III.28 and III.29 call that lemma too, and rest on
the rule through III.26 and III.27 as well, which they cite.

##### III.2

Two rules contain III.2, and no proposition rests on either. Circle 2 says it outright, and more,
for its ends may be within the circle as well as on it. Circle 3, that a straight line
that has left a circle does not come back, is Circle 2 turned round: each proves the other
in a line (`Audit.inside_of_between`, `Audit.outside_of_between`), and Circle 3 gives
III.2 at once (`Audit.III_2_outside`). No proposition of Book I rests on either: I.5 and
I.9 take a point "at random" with Book Zero's `exists_between_nearer`, which keeps the
point near enough by the order of the points on the straight line and the adding of
lengths, not by a rule about circles.

Our III.2 is Euclid's reductio, by I.5, I.16 and I.19, with the centre from III.1, and it
rests on neither rule. Circle 2 used to reach it through III.1, which called the rule to
put D, the middle point of AB, within the circle, so that the straight line drawn through
D at right angles to AB meets the circle on both sides of it: "a fact which Euclid first
demonstrates in III. 2", as Isaac Todhunter observes (Heath, vol. 2, p. 7). III.1's
helper `Prop1.within` proves it by III.2's own argument, from the centre III.1's statement
gives: on AB that centre is D itself, and off it I.5, I.16 and I.19 make D nearer the
centre than the circumference. II.14, once the first proof to call the rule, needs E, between
B and F, the ends of the diameter of the semicircle BHF, within the circle, so that DE
produced meets it at H, a step Euclid takes without saying why
([gaps in Book II](gaps-book-II.md#ii14)). G, the centre, falls between B and E, so E lies
between the centre and F, and Book Zero's `InsideCircle.of_between_centre` puts it within,
by Definition I.15 and the rules that relate "within" to the radius, with no proposition.

The later proofs that called Circle 2 take the step in one of three ways. Where both ends
are on the circle, III.2's own case, they cite III.2: III.10, III.15, III.21, III.22,
III.23, III.25, III.30, and III.32 in its helper `Prop32.sameSide`. Where one end is the
centre and the other is on the circle, they use `InsideCircle.of_between_centre`: III.7,
III.8, III.12, III.15, III.17, III.20, III.34 and III.37. III.15 also has L between the
centre and the point K within the circle; `InsideCircle.of_between_centre_of_inside`
uses the given point F of the circle to put L within. Where an end is within the circle
and is not its centre, they cite III.2's corollary `Prop2.within`, III.2 for ends on or
within the circle, whose proof produces the straight line to meet the circle and finds
the point between the two points where it meets it: III.7, III.11, III.15 and III.23.
III.13 cites III.2, where Heath's reference is III.2.

Three more corollaries after III.2 take the place of Book Zero lemmas that rest on Circle 2:
`Prop2.triangle`, that three points of a circle are not on one straight line, first used
in III.8; and `Prop2.oppositeSide` and `Prop2.sameSide`, that a straight line in a circle
has points of the circle on either side of it, first used in the shared steps of
`Circumferences.lean`, which III.24 is the first to cite. Book Zero keeps its own three,
`Triangle.of_onCircle`, `exists_onCircle_oppositeSidesOf` and
`exists_onCircle_sameSideOf`, stated for a circle with no centre given: no proposition
uses them, and the staged work (`Staging/`) still does, and calls Circle 2 and Circle 3
itself in places. Since `Prop2.within` is Circle 2 for a circle with a centre,
proved from the other rules, Circle 2 and Circle 3 tell us nothing about such a circle
that the rest of our foundations do not.

##### III.5

III.5 calls the rule itself, for the step Euclid leaves tacit: were F and G one point, the
circles ABC and CDG, about one centre through one point, would be one circle. The Lean
takes Euclid's steps and ends as he does, by the order of the points: F and G lie on one
ray from E, and the nearer would make the less equal to the greater (Henry Savile's
argument, Book Zero's `OnRay.eq_of_len_eq`).

Any proof of our III.5 must use Diagram-segment 2 or Circle 4. Draw every circle twice
over, as two circles with one centre and one radius, through the same points. Of the 24
rules about circles, only these two say when two circles are one circle or two, and every
other rule we take still holds; but a circle and its copy are two circles, they cut one
another, and they have one centre, so III.5 fails for them. That is a model argument,
checked by hand rule by rule, not by Lean ([FORMALIZATION](../FORMALIZATION.md), section
9). It is a fact about our statement, which reads "two circles" as two different circles
(`ABC ≠ CDG`) and "cut" as meeting at two points (`CirclesMeet`). Read "cut" as a point of
one circle within the other, with a point in common, and Definition I.15 and
Diagram-segment 4, with a law of magnitude, give III.5 with neither rule
(`Audit.III_5_crossing`). In our statement, Euclid's own ending needs one of the two rules
as well, for the step he leaves tacit: that two different circles about one centre meet a
straight line from it at different points, so that EF and EG are "the less to the
greater". For a circle and its copy, F and G are one point, and EF is equal to EG without
contradiction.

##### III.6

III.6 calls both rules itself. Contact without ends at once, before anything is drawn: the
supposed common centre would be within both circles (Generalities 3, proved since 19
October 2026 in `Elements/Figure/RuleBase.lean`), and circles that touch without have no
such point. For contact within, the Lean is as III.5's, with
Diagram-segment 2 for the step Euclid leaves tacit, that E and B are two points.

Any proof of our III.6 for contact within must use one of the same two rules, for the
same reason: a circle and its copy, drawn twice over as under III.5, are two circles that
meet, and no point of either lies outside the other, so by our Definition III.3 they touch
within; and they have one centre. That too is our statement's reading, which asks of
circles touching within only that they are two, that they meet, and that no point of the
inner lies outside the outer; read with a point of the inner circle within the outer, the
same proof (`Audit.III_5_crossing`) gives III.6 for contact within with neither rule. In
our statement, Euclid's ending, FE equal to FB, "the less to the greater", needs the same
tacit step, that the two circles meet the straight line FEB at different points. For
contact without, Generalities 3 alone is enough: a common centre would be a point within
both circles, and circles that touch without have none.

### How the rows were found

**What the project already says.** The [gap catalogue for Book III](gaps-book-III.md) says
that Circle 2 "already contains III.2", in its introduction and under III.1, where it also
gives Generalities 2 as the corollary Heath would add to III.1. III.2's commentary has a
paragraph headed "A rule that contains III.2", and III.5's and III.6's name `circle_eq` as
the rule that supplies the step Euclid leaves tacit there. The axiom docstrings name one
more of Euclid's steps: Intersection 5 is "the step Euclid takes for granted in I.1". That
is a gap Euclid leaves and the rule fills, not a proposition he proves later, and it
belongs to the [gap catalogue for Book I](gaps-book-I.md).

**Small certificates.** Four certificates cite no proposition: I.1 and I.4, Euclid's own
beginnings, which rest on Postulate 3 with Intersection 5 and on superposition; and III.5
and III.6, which are rows of the catalogue. When the catalogue was made, III.5 and III.6
rested on six rules each, ending with Diagram-segment 2; now that they end by the order of
the points, as Euclid does, each rests on eighteen, as many as I.1, and on Common Notion 5,
so their certificates no longer stand out. Three others, I.23, I.25 and I.41, have the
fewest rules in `direct_axioms`, three to five, but each cites propositions and carries
Euclid's argument.

**A sweep of every rule.** We read each of the 81 tacit rules, with the postulates and
Definition 15, against the 99 statements and the three porisms, and later against the 19
companions that stages 2 and 4b brought in (I.40's, I.45's, II.1's and II.14's, and those
of III.7, III.8 and III.17), and found no more. Then a mechanical screen,
[Audit/screen.py](../../Audit/screen.py), had Lean's `grind` try every statement against
every axiom alone, every family of axioms (the file that declares them) together, every
pair of the 24 rules about circles, and every pair of families. Its first run, 40,698
attempts over the 99 propositions and the three porisms, closed III.2, III.5 and III.6, and
nothing else. But it left defined words folded, `Triangle`, `Collinear`, `circumference`
and `standing` among them, so that a statement written with them was searched only in part,
as Argon's second review pointed out; and it lost more than a quarter of its attempts
without a search, for `grind` refuses a rule in which it finds nothing to match, as it does
the twelve rules that only say a point, a straight line or a circle exists, and with it the
rest of the attempt, so that Postulates 4 and 5, for instance, were never tried with the
diagram rules.

The revised screen of `tooling/overlap-screen-unfold` (commit `760b974`) was run against
library revision `89c5da4`. The linked `Audit/screen.py` gains the behaviours described here
when that tooling lands. In the revised screen, every definition a statement or a rule
reaches is unfolded, but for the kinds of magnitude, with their sum, order and zero, in
which the rules are stated, and the magnitudes Lean chooses (`circumference`, `standing` and
the rectangle `rect`), which are given by what their definitions say; each try leaves out
the rules `grind` refuses, and each statement is also tried with no rule, so that one that
holds by its definitions alone is not counted as a rule's. Run so over all 121 statements,
the propositions, the porisms and the companions, the revised screen closed the same three,
each by a rule, and nothing else; no statement closed with no rule. Seven of its 90,629
tries ran out of time even with four times the usual allowance, all of them III.34 from
Postulate 4, alone or with Postulate 5 and at most one more family. III.34 asks for three
points on its circle, and the rules among those that put a point on a circle that has none
need a straight line, which III.34 does not give and none of those rules draws. No try
stopped on any other error. What the revised screen does not give `grind` is that every
point of a circle measures a circumference alike: that is III.21, a proposition, so the near
misses of the measure (below) are not found by it, and are not overlaps with a rule. Nor
does it give `grind` that a magnitude Lean chooses is one magnitude under two descriptions
that hold of the same points, as `standing_eq_circumference` and `standing_congr` show, so a
statement that needs that step is not searched either. Nor does `grind` reason by induction,
or open a figure's fields of itself, so what a figure given with its triangles holds by its
formation is not searched, which only the companions of I.45 and II.14 speak of. The revised
screen is not one of CI's checks: that run took about an hour and a half of processor time,
and nothing runs it of itself; it should be run again when a statement or a rule changes. It
cannot draw a figure, for `grind` works with the points and circles a goal already names.
I.7 needs two circles its statement never mentions, and I.23 a triangle laid down, so both
came from reading. I.2 and I.3 need a triangle drawn and then laid down. The catalogue first
listed them as near misses, since neither statement gives a triangle to move; but the same
holds of I.7's circles, and they are rows now, with `Audit.I_2` and `Audit.I_3`.

**How each rule enters.** Argon's second review pointed out that `direct_axioms` counts a
rule a proof reaches through a lemma as well as one its own Lean names, and found that
II.14 and III.15 called Circle 2 on two points of a circle. The account of "First enters"
above the table and the notes on I.13 in 17 proofs, III.1's porism and III.2 rest on that
reading, each point checked against Lean's proof terms. The certificate now keeps the two
apart, as `own_axioms` and `inherited`, and agrees with every one of those points.

### The rows checked

For each row we looked for a proof of the proposition's statement from at most three rules.

- **III.2**: found, from one rule, Circle 2; and from one rule, Circle 3, which is Circle 2
  turned round.
- **III.5**: found, from one rule, Diagram-segment 2.
- **III.6**: found, from two rules, and neither will do alone. In the ordinary plane with
  no point counted within any circle, Diagram-segment 2 still holds, while a circle then
  touches itself "without" and has the same centre as itself. Let a circle be drawn twice
  over, as two circles with one centre and one radius, and Generalities 3 still holds,
  while the two touch "within" and have one centre. Generalities 3 is a theorem now, so
  of the two only Diagram-segment 2 remains an assumption.
- **I.7**: not found from three. The shortest proof we found, `Audit.I_7`, uses seven:
  Circle 4 does the work, and the others draw two circles the statement never mentions and
  tell them apart. Circle 4 alone does not give I.7: where there are no circles and every
  length is nothing, it holds, having nothing to speak of, and I.7 fails for any two points
  on one side of AB. So the row says that Circle 4 supplies I.7's step, not that it gives
  I.7 at once.
- **I.23**: not found from three. `Audit.I_23` uses eight axioms (System E's Metric 1 is two
  of them): superposition does the work, and the others name the ray and the side.
  Superposition alone does not give I.23: where there are no straight lines it holds,
  having nothing to speak of, and no point lies on a ray from A through B. So the row says
  that superposition supplies I.23's step, as for I.7.
- **I.2 and I.3**: not found from three. `Audit.I_2` uses ten axioms and `Audit.I_3`
  twenty-two: superposition does the work, and the others draw a triangle to lay down and
  a point off AB, and, for I.3, place the new point between A and B. Superposition alone
  does not give I.2: where there are no straight lines it holds, having nothing to speak
  of, and no length from A need equal BC. Nor does it give I.3: in that world, let no
  point lie between two others, and let AB be the greater of two straight lines; then no
  point lies between A and B to cut off the less. So the rows say that superposition
  supplies their step, as for I.7 and I.23.
- **The steps.** For III.1, its porism and I.13 we found no proof from three rules: each
  needs a construction Euclid makes by earlier propositions, a bisection or a
  perpendicular (I.10, I.11). In the other direction, Diagram-angle 3 is a theorem of
  the remaining axioms: `Audit.adjacent_eq_of_right` proves it from I.13, and Lean's list
  of what that proof rests on does not include it. It stays an axiom, as System E has it.

### Near misses

- **III.10**, that a circle does not cut a circle at more points than two. Circle 4 with
  Same side 5 gives it when none of the three common points lies on the straight line
  through the centres: each pair would lie on opposite sides of that straight line, and a
  straight line has only two sides. When one of them does lie on it, the work is Euclid's.
  Circle 4 enters no proof.
- **I.4's last clause.** Metric 9 (`area_congruent`) makes the triangles equal once their
  sides and angles are. Euclid's reason there is that the triangles coincide (Common
  Notion 4), his own step in I.4, not a later proposition.
- **Representation and scope.** III.24's second clause follows from its angle hypothesis
  alone, and III.26 and III.27 hold without their equal circles, because of how a
  circumference is measured: a definition, not a rule. `Audit.III_24_measure`,
  `Audit.III_26_any` and `Audit.III_27_any` prove each so, with their axioms pinned, and
  give back the propositions' own statements; they are meant to stop compiling when arcs
  get a meaning of their own (brief 0005, stage 3). III.1 and III.25 take a centre from a
  hypothesis. These belong to the review records, under `[representation]` and
  `[statement]`.

- **III.30, by the same measure.** I.4 makes the angles DAB and ABD equal, and they stand
  on the halves DB and AD. Each half is measured by the angle standing on it, taken twice,
  so the halves are equal. Euclid goes instead from the equal straight lines AD and DB, by
  III.28, with his step that each half is less than a semicircle; his own III.26 would take
  him from the equal angles to equal halves without either. What the measure saves is
  III.26's work at the circumference, which it reduces to its definition and III.21.
  `Audit.III_30_measure` proves III.30 so, with its own statement and its axioms pinned; it
  cites III.21, through which every point of the circle measures a circumference alike, so
  it is a near miss of the measure, not of a rule. Our III.30 follows Euclid, by III.28, as
  [FORMALIZATION](../FORMALIZATION.md), section 5, asks. III.30's statement keeps the
  measure when arcs get a meaning of their own ([brief 0006](../briefs/0006-statements.md),
  stage 3), so this near miss stays.

### A separate piece of work

Each row of the first two kinds names an assumption that contains its proposition.
Deriving those propositions, or those rules, from weaker assumptions would be a separate
piece of work, with its dependencies audited. It would need a check that no proof rests,
by any path, on a rule containing its own conclusion; a ban on citing later propositions
by name cannot see that, as Astra observes. Two small steps are taken here. Diagram-angle
3 is a theorem of the other rules, which I.13 gives back. And III.2 rests on neither rule
that contains it: our proofs take its step by III.2, its corollaries or Definition I.15, and
for a circle with a centre `Prop2.within` proves Circle 2 from the other rules. Lean's
certificate shows that no entry rests on Circle 2 or Circle 3; no check yet keeps it so.

### Keeping it current

`lake build Audit` compiles the audit lemmas and checks their pinned axioms; the library is
not in the default build, and nothing imports it. If a statement or a rule changes so that
an audit lemma stops compiling, its row is out of date: the overlap may have gone, which is
good news, or moved. The first users come from facts.json, and change only when the proofs,
or the lemmas they call, do. A proof that calls Circle 2 or Circle 3, or one of Book Zero's
three lemmas that rest on Circle 2, brings the rule back into the certificate; III.2, its
corollaries and the two `InsideCircle` helpers take the step without it.
