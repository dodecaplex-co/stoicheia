# What Euclid takes for granted: Book III

A running catalogue of the steps in Book III that Euclid takes without saying why,
found by writing his proofs out in Lean. It carries on the catalogues for
[Book I](gaps-book-I.md) and [Book II](gaps-book-II.md); Book I's introduction names
those who noticed Euclid's gaps, or formalized the Elements, before us, and
[*Does the Proof Prove It That Way?*](https://arxiv.org/abs/2608.15432) (Pistis),
which catalogues 52 gaps in Books I–III, is the companion here too. Book III is about
the circle, and most of what it takes for granted is where a straight line meets a
circle and where the points fall: within the circle or outside it, between two others,
on one side of a straight line or the other. Many of these gaps were seen long ago, and
Heath's notes report J. G. Camerer, Augustus De Morgan, Isaac Todhunter and Robert
Simson on them, beside his own. Where we know who saw a gap first, we say so; nothing
here is meant to be new.

Each entry names the Lean lemma or tacit rule that fills the gap. A few of System E's
rules for circles do most of the work, and we name them once here. A circle's centre is
within it (`centre_inside`, Generalities 3), now proved in Book Zero's `RuleBase.lean`
from Circle 1, Definition I.15, Postulates 1 and 3, circle crossings, length addition and
the rule that one centre and one radius make one circle (`circle_eq`, Diagram-segment 2):
a centre outside would have unequal radii, which needs every radius to be something, and
Postulate 3 and Diagram-segment 2 show that it is (`RuleProofs.Circle.radius_ne_zero` and
`RuleProofs.Circle.length_pos`). That it has only one centre
(`centre_unique`, Generalities 2) is now proved in Book Zero's `Circles.lean`:
two supposed centres bisect the same straight line through the circle by Definition I.15,
and equal doubles have equal halves. A point within a circle, on a straight line that
meets the circle at two points, lies between them (`between_of_inside_chord`, Circle 1).
System E's Circle 2, that between two points on or within a circle every point is within
it (`inside_of_between`), and its Circle 3 (`outside_of_between`), each of which gives
III.2 at once, are proved after III.2, from it, since 24 October 2026; our III.1 and III.2
do without them, and no proof before III.2 may use them. A point
between the centre and a point on the circle is within it by Definition I.15
(`InsideCircle.of_between_centre`), as is a point between the centre and a point within
the circle when another point of the circle is given
(`InsideCircle.of_between_centre_of_inside`); a point
between two points of the circle is within it by III.2 (by III.2's own argument in III.1,
`Prop1.within`), and a point between two points on or within it by III.2's corollary
`Prop2.within`. A straight line from a point within a
circle to a point outside it meets the circle between them (`line_circle_between`,
Intersections 4), and a straight line through a point within meets the circle beyond
that point, on either side (`line_circle_beyond`, Intersections 5). And one centre with
one radius makes one circle (`circle_eq`, Diagram-segment 2). III.2's corollaries add that
three points of a circle make a triangle (`Prop2.triangle`) and that a straight line in a
circle has points of the circle on either side of it (`Prop2.oppositeSide`,
`Prop2.sameSide`); Book Zero's [`OnCircles.lean`](../../Elements/Figure/OnCircles.lean),
that no point of a straight line touching a circle is within it (`Touches.not_inside`).

Book III's proofs cite the earlier books as `BookI.PropN` and `BookII.PropN`. The steps
they share that cite Books I and II live in
[`Squares.lean`](../../Elements/BookIII/Squares.lean): equal squares are on equal
straight lines (`BookI.Prop46.sq`), and the perpendicular from the centre to a straight
line in the circle falls between its ends (`foot_between`). Those that cite III.20–III.22
live in [`Circumferences.lean`](../../Elements/BookIII/Circumferences.lean), and are what
Euclid takes for granted of circumferences, which we measure by twice the angle
standing on them: a circumference is twice the angle at any point of the other segment
(`Circumference.eq`, `Circumference.standing`), and is its angle at the centre when the
centre lies beyond it (`Circumference.centre`); the two circumferences on a straight
line make up the whole circle (`Circumference.whole`); and a circumference is a
semicircle, less or greater, as the centre lies on its straight line, beyond it or on
its side (`Circumference.semicircle`, `Circumference.lt_semicircle`,
`Circumference.gt_semicircle`). A lemma named after a proposition, such as
`Prop8.within`, lives in its file. Our foundations give every circle a centre
(`exists_centre`); proofs find a centre by III.1's construction where none is supplied
and Heath's reference is III.1 (`Prop1.of_circle`), III.2 aside, which takes it from the
rule; they take it from the rule where he gives no reference, and from geometric data
such as equal circles, as [Book III's introduction](../../book/III/index.md) tells.
These steps, with those below that Euclid takes with no bracket in Heath or without a
word, are why [CERTIFICATE.md](../../CERTIFICATE.md) shows the Lean citing more than
Heath's brackets give in most of the propositions of Book III; and two of Heath's
references to III.1, in III.2 and III.14, have no call beside them.

## III.1
- "Let it be bisected at the point D; from D let DC be drawn at right angles to AB": Heath gives no bracket for either step. They are I.10 and I.11 (`BookI.Prop10`, `BookI.Prop11`).
- "Let it be drawn through to E" asks that the straight line through D meet the circle on both sides of D. Todhunter observes that D is taken to be within the circle, which Euclid proves only in III.2, and Heath that the straight line must meet the circle twice, "an assumption which we are not entitled to make on the basis of what has gone before only" (vol. 2, p. 7). `Prop1.construction` obtains a centre through `exists_centre` solely inside the proof that D is within, and passes it to `Prop1.within`, which puts D within the circle by III.2's own argument (I.5, I.16, I.19), without Circle 3 or its consequence Circle 2 (`inside_of_between`), which would give III.2 at once (see III.2). That centre supplies none of the construction's outputs, and III.1's statement supplies none: the main reductio takes its own centre G from `exists_centre`. Intersections 5 (`line_circle_beyond`), used twice, finds C and E.
- G, the supposed centre, must be off AB as well as off CE, or there are no triangles DAG, DBG for I.8. A centre on AB would be its middle point D (`Prop1.middle`), which is on CE.
- "The angle FDB is equal to the angle GDB, the greater to the less": if AB passes through the centre, F falls on D and there is no angle FDB. Our proof sets the right angle CDB beside GDB, and `Prop1.perpendicular`, that at D only one straight line is at right angles to DB, says what "the greater to the less" stands for, on whichever side of CE G lies. With G across AB from C, it produces CD beyond D, and the angle there with DB is right by I.13, the two angles at D together making two right angles.
- "Therefore the point F is the centre": the reductio shows only that the centre is on CE. Heath: "It is however taken for granted rather than proved that the centre must be the middle point of CE" (vol. 2, p. 8). The centre is within the circle (`centre_inside`), so between C and E (Circle 1, `between_of_inside_chord`), and its equal radii make it the middle point, which is F (`Prop1.middle`).
- The Porism follows the main reductio directly from its given centre (`Prop1.porism`). If the centre is on AB, `Prop1.middle` shows that it is D, already on DC; otherwise `Prop1.equal_adjacent` supplies I.8's comparison and `Prop1.perpendicular` puts the centre on DC. It neither calls III.1 nor uses `centre_unique` or `exists_centre`. Heath separately says that the claim that a circle has one centre "may be added to III. 1 as a corollary" (vol. 2, p. 8); our foundations give that claim as System E's Generalities 2 (`centre_unique`), now proved from the foundations in Book Zero's `Circles.lean`.

## III.2
- "Let it fall outside, as AEB", and then "Similarly we can prove that neither will it fall on the circumference itself": the two suppositions Heath calls "the destruction of two hypotheses" (vol. 2, p. 9). One comparison serves both. The angles make DE less than DB (I.5, I.16, I.19); outside the circle DE would be greater than the radius DF, and on it equal to the radius.
- "Let DFE be drawn through": F, where DE crosses the circle, is read off the figure. A straight line from the centre, within the circle, to the supposed point E outside it meets the circle between them (`line_circle_between`, Intersections 4).
- Euclid's figure keeps the centre off AB, so that DAE and DEB are triangles for I.5 and I.16. When AB passes through D, `Prop2.through_centre` argues apart: DE is a part of DA or of DB, which are equal; and when E is D itself there is no straight line DE.
- III.2 follows at once from System E's Circle 3 (`outside_of_between`), and from its Circle 2 (`inside_of_between`). Neither is assumed: both are proved after III.2, from its corollary `Prop2.within`, and our III.2 uses neither. III.2 still takes its centre from the rule, where Heath's reference is III.1; III.1 puts its own D within the circle by III.2's argument (`Prop1.within`): the gap Todhunter points out under III.1.

## III.3
- "But the right angle AFE is equal to the right angle BFE": for the converse our statement gives only that AFE is right. Its neighbour BFE is right as well, by `adjacent_eq_of_right` (System E, Diagram-angle 3), now proved after I.13 by taking one right angle from two.
- "Each of the equal angles is right [I. Def. 10]": Definition I.10 calls each right; Postulate 4 makes it the one right angle `∟` that all right angles share, as in I.11.
- Euclid's "a straight line CD through the centre" is the straight line FE, through the centre E and the point F, so C and D need no Lean names. That F lies between A and B, as "bisect" means, the statement asks; III.14, III.35 and III.36 have it from `foot_between`.

## III.4
- "The angle FEA is equal to the angle FEB, the less to the greater" needs EA within the angle FEB, and Euclid's figure puts B on A's side of FE. Either B or D may be there: FE separates them, and III.3 makes both FEB and FED right. Whichever it is, `onRay_of_angle_eq` puts it on the straight line EA (the part equal to the whole, C.N. 5), and then BD would be AC.
- The enunciation needs two straight lines, for one taken twice bisects itself; the statement asks that B be off AC.

## III.5
- "let EFG be drawn through at random": we draw it through F, a point of ABC within CDG supplied by `CirclesCut`, and produce it beyond F to meet CDG at G (`line_circle_beyond`, Intersections 5). This chooses a line with the order Euclid's figure shows; one such line suffices.
- "therefore EF is also equal to EG, the less to the greater": Definition I.15 makes both lengths equal to EC, while F between E and G makes EF the less (`len_lt_of_between`). The proof does not use `circle_eq` to separate F and G; the construction gives their order.
- The proof uses only the common point C and the point of ABC within CDG. The second common point and the point of CDG within ABC describe mutual cutting. Heath's combined enunciation for III.5 and III.6 concerns mere meeting (vol. 2, p. 12); our crossing proof does not prove that wider claim on its own. The [overlap catalogue](overlaps.md#iii5) describes the bridge to the earlier reading, `CirclesCut.of_meet`, proved after III.8 from the existing axioms and III.7 and III.8; III.10's last step cites it.

## III.6
- J. G. Camerer questions whether E and B can coincide before III.13 has ruled out a second contact; Heath answers that one line from the supposed centre meeting the circles at different points is enough (vol. 2, p. 13). Our definition of contact within supplies a point of the inner circle within the outer. Drawing FEB through it and producing to the outer circle gives the two points and their order, either circle the inner, without `circle_eq`.
- Contact without, which Euclid leaves to the reader, ends before anything is drawn: a supposed common centre would be within both circles (`centre_inside`, Generalities 3), which contact without forbids. This is Definition I.15's clause placing the centre within the figure, and the case Heath regards as self-evident (vol. 2, p. 13).

## III.7
- "But the angle BEF is also greater than the angle CEF": "De Morgan points out that there is an unproved assumption in this demonstration" (vol. 2, p. 15). The straight lines are ordered by their angles at F, but I.24 needs the angles at the centre, and Euclid reads these off his figure. Heath proves it with the point where FB crosses EC and the perpendicular from E. Our proof takes the crossing too: `BookI.Prop24.within` puts FB within the angle EFC, `crossbar` finds the point M where it crosses EC, M is within the circle, between the centre E and C (`InsideCircle.of_between_centre`), and so comes before B (`Prop2.within`), and `angle_lt_of_between` makes CEF the less.
- A point of the circle on AD itself is A or D (Circle 1), the greatest or the least, which "the rest" leaves aside.
- "Let the angle FEH be constructed equal to the angle GEF [I. 23]": I.23 gives a ray, not a point of the circle. H is where that ray meets the circle (`line_circle_beyond`), so that "GE is equal to EH" is Definition I.15.
- "The nearer to the straight line through the centre being thus equal to the more remote": a second point on one side of AD as far from F as G is G itself, for were they two, one would be the nearer and the greater.
- Euclid compares the straight lines on one side of AD, as his figure has them. Across AD the comparison follows, Heath notes, from the equal straight line on the other side being equally inclined to the diameter (vol. 2, p. 17). The companion `Prop7.general` proves it so: Euclid's I.4 step, which makes FH equal to FG, makes the angles at F equal too (`Prop7.partner`).

## III.8
- Euclid speaks of the concave and the convex circumference, "terms which are not defined but taken as understood", as Heath remarks under III.7 (vol. 2, p. 16). We read the convex as where a straight line from D first meets the circle, and the concave as where it meets it again.
- "As De Morgan points out, there are here two assumptions similar to that tacitly made in the proof of III. 7, namely that K falls within the triangle DLM and E outside the triangle DFM" (vol. 2, p. 20). The first is I.21's figure, the second gives I.24 its greater angle at M. We prove both as in III.7 (`Prop8.within`, `Prop8.outside`): where DK crosses the radius ML, or DE the radius MF, the crossing is within the circle, and so between the two points where that straight line meets the circle (Circle 1).
- Our statement compares DA and DG with every point of the circle, and a point on DA itself makes no triangle for I.20. It is A or G (`Prop8.on_diameter`), and the part DG is less than the whole DA.
- "Let the angle DMB be constructed equal to the angle KMD": Heath gives no bracket for it: it is I.23. B is laid off on its arm at the distance of the radius (`OnRay.exists_len_eq`), and System E's Diagram-segment 3 (`on_circle_of_len_eq`) puts it on the circle. This rule is now proved from Postulate 3 and `circle_eq`, with the radius nonzero, in `Elements/Figure/RuleBase.lean`. Definition I.15 gives only the other half: that a point of the circle is a radius away.
- "Which was proved impossible" looks back to the convex circumference, but a third straight line DN might end on the concave one, or DK touch the circle. Our proof takes Euclid's step where the convex order reaches, the concave order for two points of the concave circumference, and the two orders together for a point on each, through the second point where the straight line making the greater angle with DA meets the circle, which is on the other circumference: cases his figure leaves aside. Only where neither order reaches, one of the two points a point of contact, does it compare the angles at M: by I.24, unequal angles there give unequal straight lines from D.
- Across DA, as in III.7, the companion `Prop8.general` compares through the partner on the other side, which Euclid's I.4 step at M makes equally inclined to DA; that it is in the same class, the convex or the concave circumference, is a step of its own (`Prop8.partner`), from the partners of the points of the circle beyond it or before it.

## III.9
- "Let AB, BC be joined and bisected at the points E, F": Heath gives no bracket for it: it is I.10.
- "The straight lines GK, HL have no other point common but the point D" takes them to be two straight lines. Were they one, the triangle BEF would have two right angles, against I.17 (`Prop9.apart`).
- "Camerer remarks that the genuine proof should also have contemplated the case in which one or other of the straight lines AB, BC passes through D" (Heath, vol. 2, p. 22); Heath answers that Euclid takes the most obscure case and leaves the others to the reader. D is none of A, B, C (`Prop9.ne_ends`), so at most one of AB, BC, CA passes through it (`Prop9.not_two`). Our proof bisects CA as well, by I.10, and argues on the two that miss D.
- Euclid's "within" is never used: ED and FD are drawn through from E and F, which are within wherever D is. Our statement leaves it out, as III.25 needs.

## III.10
- "Euclid's proof contains an unproved assumption, namely that the lines bisecting BG, BH at right angles *will* meet in a point P" (vol. 2, p. 24). The proof obtains a centre of each circle through `Tacit.exists_centre`; the porism to III.1 puts each centre on both straight lines (`Prop1.porism`), and they meet there.
- "Meet at no point except at P" takes AC and NO to be two straight lines. Were they one, the triangle BKL would have a right angle at K and another at L, against I.17 (`Prop10.meet_once`).
- The porism to III.1 asks for a right angle at the foot of each perpendicular. At K, C lies on the side of the point I.11 gives there, so the angle BKC is right as I.11 gives it; at L the porism is applied to O, which lies across L from the point I.11 gives, so the angle BLO is right by `adjacent_eq_of_right`. `Prop10.right_on_line` gives a right angle on either side of K or L, for the angles BKL and BLK in `Prop10.meet_once`.
- Heath gives no bracket for the bisections or the right angles: they are I.10 and I.11.
- Euclid names four common points and uses three; F never enters the argument. Heath observes that the proof covers circles that merely meet (vol. 2, p. 23). Our statement asks for three distinct common points, without centre inputs.
- "The two circles ABC, DEF which cut one another": Euclid's circles cut by his supposition; ours are given only common points, and the restated III.5 asks for crossing. That two different circles meeting at two points cut one another is proved after III.8 (`CirclesCut.of_meet`): their centres, taken from the rule, are two points by `circle_eq`, and the least straight line from either centre to the other circle, which III.7 or III.8 puts on the straight line through the centres, ends nearer that centre than the common points are, and so within the first circle. With B and G, III.5 then forbids the one centre P, as Heath's bracket says.

## III.11
- Heath finds Euclid's proof "beset with difficulties in consequence of what it tacitly assumes in the figure" (vol. 2, p. 25), and gives Camerer's note on them. Camerer observes first that the straight line joining the centres must be produced "*in the direction of the centre of the circle which touches the other internally*" (vol. 2, p. 25). Our statement concludes `Between F G A`: FG produced beyond G, the centre of the inner circle.
- G must be within ABC before FG produced beyond G can meet ABC at H. G lies between two points of the inner circle ADE, neither of them outside ABC (`Prop11.not_outside`), so III.2, for points on or within the circle (`Prop2.within`), puts it within.
- To make Euclid's proof "absolutely conclusive", Heath asks also that the point where FG produced meets the inner circle be "*not further* from G" than H (vol. 2, p. 26). Our proof finds it inside Euclid's argument: GD greater than GH puts D beyond H, outside ABC, which contact within forbids (`TouchesInternally`), and the strict inequality rules out D at H.
- That touching circles cross nowhere else, which Heath says Euclid "does practically assume in III. 11–13, without stating" (vol. 2, p. 3), our definitions of touching carry: they read Definition III.3 of the whole circles, Todhunter's reading as Heath reports it.
- With A on GF produced beyond F, a case that "would in any case have been left to the reader by Euclid" (vol. 2, p. 26), AG is AF and FG together (`between_of_inside_chord`), and so exceeds AF.
- Heath gives no bracket at all. "Since AG, GF are greater than FA" is I.20; and that F and G are two points, so that FG is a straight line, is III.6.

## III.12
- "Euclid's proof is valid provided only that, if FG, joining the assumed centres, meets the circle with centre F in C and the other circle in D, C is not within the circle ADE and D is not within the circle ABC" (vol. 2, p. 28). Our proof begins with the centres: each is outside the other circle (`Prop12.centre_outside`), for were it on that circle, a point near it towards the other centre would be within both. So FG leaves ABC at C and enters ADE at D (`line_circle_between`), and C is not within ADE, for a point of CF near C (`exists_between_nearer`) would be within both circles, which contact without forbids.
- Heath's parenthesis allows C and D to be one point (vol. 2, p. 28), so Euclid's "greater" is read as "not less".
- The case "that A does not lie on FG but on FG *produced* in either direction" is one Euclid "would in any case have left to the reader" (vol. 2, p. 29). One centre would then be within both circles.
- Heath's bracket gives [I. 20], and none is given for F and G being two points: it is III.6.

## III.13
- "Therefore the straight line joined from G to H will fall on B, D [III. 11]": Camerer remarks that "it is assumed that the supposed second point of contact lies on the line of centres *produced beyond the centre of the 'outer' circle*, whereas all that is proved in III. 11 is that the line of centres *produced beyond the centre of the 'inner' circle* passes through a point of contact" (Heath, vol. 2, p. 33). We read Definition III.3 of the whole circles, so circles touching within at D touch within at B as well, and III.11 puts B, like D, on GH. G, the centre of the outer circle, lies between B and D, two of its points on a straight line through it (`between_of_inside_chord`), and the order BGHD that carries Euclid's comparison follows, where Euclid reads it off his figure.
- Without, "the straight line joining the points will fall within each circle [III. 2]" needs a point of AC to be within. Our proof takes an unlettered point between A and C (`exists_point_between`), which III.2 puts within both circles, and contact without forbids it.

## III.14
- III.3 needs each perpendicular's foot between the ends of its straight line, and Euclid reads it off his figure: `foot_between`, by I.17 and I.19.
- "Let the centre of the circle ABDC be taken [III. 1], and let it be E": Definition III.4 measures from the centre, so our statement names E and the feet F, G. Our proof therefore takes no centre here, though Heath's reference is III.1, and I.12 has nothing left to draw.
- "And AB is equal to CD; therefore AF is also equal to CG": the halves of equal things are equal (`Magnitude.eq_of_add_self_eq`), the step J. L. Heiberg brackets in I.37.
- I.47, which Heath's bracket gives for "the squares on AF, EF are equal to the square on AE", is said of squares on straight lines (`BookI.Prop47.sq`), as in Book II. "Therefore EF is equal to EG", and in the converse "therefore AF is equal to CG", pass from equal squares to equal straight lines without a word: `BookI.Prop46.sq`, as in I.48.
- The enunciation speaks of any straight lines in the circle, and the proof takes them "not through the centre", as III.3 does. A diameter is at no distance from the centre, the foot of its perpendicular being the centre itself (`Foot`), and the companion `Prop14.general` takes it: a diameter is two radii together (`Prop14.diameter_sum`), and greater than a straight line not through the centre, by I.20.

## III.15
- "Euclid himself assumes that the angle subtended at the centre by MN is greater than the angle subtended by FG, or, in other words, that M, N both fall outside the triangle FEG" (vol. 2, p. 37). Heath gives the reason, that EM, EN are radii, greater than the distances to the points where MN cuts EF, EG. Our proof goes one step further back: MN and FG never meet, for at a common point the triangle it makes with L and K would have two right angles, against I.17. So F and G lie across MN from E, and each point where MN cuts EF or EG is within the circle, and so between L and the end of MN on its side (`Prop15.half`). The two halves together are "the angle MEN greater than the angle FEG".
- "Let EL be made equal to EH, through L let LM be drawn at right angles to EK and carried through to N": Heath gives no bracket for either: they are I.3 and I.11. K is within the circle by III.2, and L lies between the centre and K, so the given point F of the circle puts L within (`InsideCircle.of_between_centre_of_inside`); the straight line then meets the circle at M and N (`line_circle_beyond`), and it is at right angles to EK on both sides of L (`Prop15.perp`).
- The feet H and K fall within BC and FG (`foot_between`). Our statement names E and the perpendiculars EH, EK, as Definition III.5 measures from them, so there is nothing to draw by III.1 or I.12.
- "Therefore AD is greater than BC" comes by MN, which Euclid draws to compare BC with FG, so the proof says it only of a BC with a more remote straight line beside it. The companion `Prop15.le_diameter` needs no MN: BE and EC are two radii, together equal to AD, and greater than BC by I.20, unless BC passes through E and is a diameter too. The companion `Prop15.nearer` lets the nearer straight line be a diameter, its foot the centre (`Foot`); the more remote cannot pass through the centre.

## III.16
- "Let DG be drawn from the point D perpendicular to FA": Heath gives no bracket for it: it is I.12.
- Euclid's figure puts the foot G away from A. At A only one straight line is at right angles to AD, as in III.1 (`Prop1.perpendicular`), so were G at A, FA would be AE itself.
- If FA passes through the centre, D itself is the point of FA within the circle.
- Euclid's "let it fall within as CA" takes a point C on E's side of A, where the angle with AD is the right angle at A. AE is a whole straight line, and beyond A the angle is right too, being adjacent to a right angle (`adjacent_eq_of_right`).
- The angle of the semicircle and the horn-like angle are contained by a straight line and a circumference (Definition III.7). The main statement keeps the rectilineal fact Euclid proves them by: every other straight line through A has a point within the circle. The companions compare the mixed angles as regions near A, directly from that fact, where Euclid argues by reductio.
- Heiberg drops, as Theon's addition, the words "and that a straight line touches a circle at one point only" (Heath, vol. 2, p. 43); our `Touches` (Definition III.2) says it. Simson's remark that "there can be but one straight line which touches the circle at the same point" (vol. 2, p. 43) follows from our second clause.

## III.17
- "Let the centre E of the circle be taken; [III. 1]": the proof finds E by III.1's construction, on a straight line drawn through the circle at random (`Prop1.of_circle`), as Euclid does. Since A is outside, `line_circle_between` then finds Euclid's D between E and A.
- "From D let DF be drawn at right angles to EA": Heath gives no bracket for it: it is I.11. I.11's straight line need not end on the circle AFG; F is where it, produced beyond D, meets that circle, and the angle there is right too (`adjacent_eq_of_right`).
- B, where EF meets the circle BCD, is read off the figure. F is farther from E than D, so outside BCD, and EF meets the circle between E and F (`line_circle_between`).
- A point on the circumference Euclid leaves out, Heath explains, as "so directly indicated by III. 16, Por. as to be scarcely worth a separate statement" (vol. 2, p. 44). The companion `Prop17.general` takes it: the straight line at right angles to the radius EA at A (I.11) touches by III.16's porism, and the point of contact is A itself. From a point within, no straight line touches (`Prop17.inside`, by `Touches.not_inside`).

## III.18
- "Let FG be drawn from F perpendicular to DE": Heath gives no bracket for it: it is I.12.
- "But FC is equal to FB": B, where FG meets the circle, is read off the figure. G is outside the circle: not within, for no point of a straight line touching a circle is (`Touches.not_inside`), and not on it, or DE would meet the circle at C and at G and so cut it. Then FG meets the circle between F and G (`line_circle_between`).
- F is off DE, for the centre is within the circle (`centre_inside`) and no point of DE is.
- "Similarly we can prove that neither is any other straight line except FC" needs no Lean: the reductio puts the foot of I.12's perpendicular at C, so FC is at right angles to DE on both sides of C.

## III.19
- Our A is any point off DE with CA at right angles to it, and need not be on the circle, so it may lie across DE from the centre.
- "The angle FCE is equal to the angle ACE, the less to the greater": at C only one straight line is at right angles to DE, as in III.1 (`Prop1.perpendicular`), which produces AC beyond C when A lies across DE from F.
- The supposed centre F is off DE: `centre_inside` and `Touches.not_inside`. Euclid's E is a point of DE other than C, which our proof chooses, since our D and E may include C.

## III.20
- Euclid leaves out the case where AB or AC passes through the centre, which Christopher Clavius and others gave separately. Heath: "Euclid's proof gives so obviously the means of proving this that it is properly left out" (vol. 2, p. 49). Our proof writes it out, with one isosceles triangle.
- "Todhunter observes, what Clavius had also remarked, that there are two assumptions in the proof of III. 20, namely that, if A is double of B and C double of D, then the sum, or difference, of A and C is equal to double the sum, or difference, of B and D respectively, the assumptions being particular cases of V. 1 and V. 5" (vol. 2, p. 49). For the sum, our proof regroups the magnitudes (`add_comm`, `add_assoc`); for the difference, it takes equals from equals (`CommonNotion3`).
- "Therefore the whole angle BEC" needs AE produced to cross BC between B and C, and within the circle (III.2), so that BEF and FEC make up the angle at the centre (`crossbar`, `angleAtCentre.diameter`); and "the angle BEC which remains" needs B within the angle GEC (`angle_add_of_within`). Euclid reads both off his figure.
- Euclid "had no idea of III. 20 applying *in terms* ... to the case where the angle at the circumference, or the angle in the segment, is *obtuse*" (vol. 2, p. 48). Our statement reads the angle at the centre as the angle standing on the circumference, of any size (`angleAtCentre`), a reading of ours after Heath's notes. The proofs that BEF and FEC make it up wherever the centre lies, and that it is the angle BEC, two right angles, or four right angles less the angle BEC, as the centre lies on A's side of BC, on BC or beyond it, cite I.13 and III.2, which Heath's brackets do not give. The companion `Prop20.special` keeps the centre on A's side of BC, where the angle at the centre is the angle BEC, less than two right angles.

## III.21
- "Under the restriction that the 'angle at the centre' used in III. 20 must be less than two right angles, Euclid's proof of this proposition only applies to the case of a segment greater than a semicircle", Heath writes, and "The simplest proof, of many, seems to be that of Simson" (vol. 2, p. 49). Our III.20 reads the angle at the centre as of any size (`angleAtCentre`), a reading of ours after Heath's notes, so Euclid's two steps hold in every segment, and our proof needs no completion of Simson's (vol. 2, pp. 49–50).
- "Therefore the angle BAD is equal to the angle BED": halves of one angle are equal (`Magnitude.eq_of_add_self_eq`).

## III.22
- "The whole angle ADC is equal to the angles BAC, ACB" needs DB within the angle ADC, and so AC and BD to cut one another. Our statement puts A and C on opposite sides of BD; AC meets the straight line BD at a point within the circle (III.2), and so between B and D (Circle 1).
- Three points of a circle make a triangle (`Prop2.triangle`, from III.2), as I.32 needs of ABC.

## III.23
- Euclid draws the segment ACB within ADB. Simson observes that the remark Euclid makes in III.24, that the circles cannot meet again, "is an equally necessary preliminary to III. 23, in order that we may be justified in drawing the segments as being one inside the other" (vol. 2, p. 53). Our proof begins as Simson does: the circles meet at A and B, so not at C (III.10), and C is within the circle ADB or outside it. Heath gives no bracket for III.10.
- "Let ACD be drawn through": with C within ADB, AC drawn through meets ADB beyond C (`line_circle_beyond`). With C outside, the segments change places, through a point between A and B within both circles (III.2, and `line_circle_between`).
- Our D is any point of its segment, so III.21, which Euclid does not use here, moves its angle to where AC drawn through meets ADB.
- The companion, III.23 point by point (`Prop23.point`), goes through a point M between A and B, within the circle (III.2). For a point P outside the circle, PM meets it at Q; for one within, MP produced beyond P does. In both, the point between M and the third corner lies within the triangle on AB (`Prop23.insideTriangle_of_between`, by Pasch 2), as I.21 needs.

## III.24
- "If the segment AEB be applied to CFD": no rule moves a figure but in I.4 and I.8, so the application is a theorem (`placement`). Each point on E's side of AB, or on AB, goes to the point on F's side of CD, or on CD, as far from C as it was from A and from D as it was from B. That point exists, by I.22 off the base, I.20 giving its condition, and by I.3 on it, or beyond the ends by producing CD, I.2 placing the length first. It is the only one: by I.7 off the base, by the order of points on it, and never one on and one off, by I.20's degenerate case (`BookI.Prop20.collinear_iff`). Two points keep their distance: both on the base by their order; one on it and one off by I.8 and I.4, measured from the end whose ray holds the point of the base; both off it by I.8, I.24's step (`BookI.Prop24.within`) and I.4, measured from whichever end gives unequal angles (`Placement.base_choice`). The map is onto, the same construction running back from CD to AB.
- "And, AB coinciding with CD": a point of the straight line through two points of a circle is on the circle exactly when it is one of them, and within it exactly when it lies between them (`Prop24.chord_cases`, by III.2 and Circle 1), so the ends of AB go to the ends of CD and its points between to points between.
- "It will either fall within it, or outside it; or it will fall awry": Heath's semicolon shows that the [III. 10] in his bracket answers only the third, and "The first two hypotheses are disposed of by a *tacit* reference to the preceding proposition III. 23" (vol. 2, p. 54). Our proof makes that reference point by point, by III.23's companion: on one side of a straight line in a circle, a point is on the circle exactly when the straight line subtends at it the angle in the segment, and within it exactly when the angle is greater (`Prop23.point`). A point and its image see AB and CD under equal angles (I.8), so no point falls within, outside or awry, and III.10 is not needed.
- Heath's figure has segments less than semicircles; the statement covers the semicircle and the greater segment too.
- The alternative proof, `Prop24.equalCircles`, compares the circles by their radii. The angle in a segment is acute, right or obtuse as the centre lies on its side of the base, on the base or beyond it (`Prop24.angle_type`), so the equal angles at E and F place the centres alike. III.20, with III.22 first when the centres lie beyond the bases, makes the angles at the centres equal, and isosceles triangles on equal bases with equal angles at the vertex have equal sides (`Prop24.isosceles`, by I.5, I.32 and I.26). When the centres lie on the bases, the bases are diameters. The circumferences are equal in measure, each twice the equal angle in the other segment (`Circumference.eq`), and with the circumference on the other side of its base it makes up the whole circle (`Circumference.whole`).
- That equal segments have circumferences equal in measure, which III.26 takes from III.24, is III.24's companion `Prop24.equalMeasure`: a point of the one circumference off its base and its image see the bases under equal angles (I.8), and `Circumference.eq` and `Circumference.whole` do the rest.

## III.25
- "Let DB be drawn ... at right angles to AC" assumes that DB reaches the circumference. Our construction is given it, as the one fact it reads off the segment: a straight line drawn from within the base towards the segment meets it. For the arc of a circle it holds: a point between the ends of the base is within the circle (III.2), and the straight line through it meets the circle on each side (`line_circle_beyond`), one meeting point on the segment's side (`Prop25.meets`).
- "Let DB be drawn through to E": in the first case Euclid takes for granted that AE meets DB produced. The angle ABD is less than a right angle (I.17, ADB being right), so the angles BAE, ABD are less than two right angles, and Postulate 5 gives E (`Postulate5`), beyond D.
- In the third case "the centre will fall on DB within the segment ABC": the constructed straight line falls within the angle BAD (`BookI.Prop24.within`) and crosses BD between B and D (`crossbar`).
- Heath gives no bracket for the bisection, the right angle, the angle BAE or "the base AE is equal to the base CE": they are I.10, I.11, I.23 and I.4.
- Heath's bracket gives [III. 9] for E, which in the first case nothing yet shows to be within the circle; our III.9 does not ask it. The step stands apart from the construction, in the companion `Prop25.complete`: any circle through A, B and C, three distinct points of the given circle, is that circle; `Prop25.complete` obtains its centre internally for III.9.

## III.26
- "As in III. 21, if Euclid's proof is to cover all cases, it requires us to take cognisance of 'angles at the centre' which are equal to or greater than two right angles. Otherwise we must deal separately with the cases where the angle at the circumference is equal to or greater than a right angle" (vol. 2, p. 57). Our proof takes that cognisance: within it the angles at the centres are of any size (`angleAtCentre`), a reading of ours after Heath's notes, so Euclid's one argument covers every case. One division into cases stays, at I.4 (`Prop26.alike`): where the angles at the centres are two right angles, BC and EF are diameters; where they are greater, I.4 takes the angles BGC, EHF that remain of four right angles.
- Euclid's setting-out gives equal angles at the centres and at the circumferences together. Our statement takes his two cases one at a time, and III.20, which Euclid does not use here, gives the other pair: halving the angles at the centres, or doubling those at A and D.
- "But the whole circle ABC is also equal to the whole circle DEF; therefore the circumference BKC which remains": that a segment's circumference and the one remaining make up the whole circle is `Circumference.whole`; then Common Notion 3. Before it, Euclid passes from the equal segments BAC, EDF to their circumferences without a word; III.24's companion `Prop24.equalMeasure` gives the step.
- Our statement says that the remainders BKC, ELF are congruent too, and a congruence cannot be subtracted. III.24 gives it: the remaining segments stand on the equal straight lines BC, EF, and are similar, their angles making two right angles with the equal angles at A and D (III.22). Only the side names a segment, so they are the segments on K's and L's sides (`Arc.Congruent.congr_side`).

## III.27
- "Let the angle BGK be constructed equal to the angle EHF [I. 23]": I.23 gives the ray, not K on the circle. K is laid off on it at the distance GB (`OnRay.exists_len_eq`), and the proved Diagram-segment 3 puts it on the circle (`on_circle_of_len_eq`, from Postulate 3 and `circle_eq`, as in III.8).
- "Therefore BK is also equal to BC, the less to the greater" takes the part BK to be less than the whole BC. Our proof measures each circumference, the centre lying beyond it, by its angle at the centre (`Circumference.centre`), so that BK is less because the angle BGK is.
- "And the angle at A is half of the angle BGC ... [III. 20]" holds where the angles at the circumference are acute. Heath: "the remarks about the method of treating the different cases apply here also" (vol. 2, p. 59). Our statement asks for angles of any size, as IV.11 needs. Our proof reaches the obtuse ones by the circumferences that remain, on which acute angles stand, and III.22, as III.26 does for the remaining segments; the right ones are angles in semicircles, read off the measure of the circumference (`Prop24.angle_type`).
- Euclid argues one case of the inequality; the reductio is written once and used with the circles exchanged, as in I.26.

## III.28
- "Euclid's proof does not in terms cover the particular case in which the chord in one circle passes through its centre; but indeed this was scarcely worth giving, as the proof can easily be supplied" (vol. 2, p. 60). Heath supplies it by III.15; our proof by I.20, which shows that a straight line equal to a diameter of an equal circle is a diameter (`Prop28.diameter`). The four circumferences are then semicircles (`Circumference.semicircle`). The angle at the centre of each is two right angles (`angleAtCentre.semicircle`), but there are no triangle angles at the centres for III.26's clause on angles at the centres, so their congruence comes from the right angle in each semicircle (`Prop28.right`, from `Prop24.angle_type`, for III.31 comes later) and III.24. The same step rules out a diameter in one circle and a straight line that is not one in the other.
- "For let the centres K, L of the circles be taken": Euclid's figure puts each centre on the side of the greater circumference, as his triangles need. The circumference on the centre's side is greater than a semicircle and the other less (`Prop28.beyond`, from `Circumference.lt_semicircle` and `Circumference.gt_semicircle`), and `Prop28.sides` divides the cases.
- "Therefore the circumference ACB which remains": `Circumference.whole`, then Common Notion 3, for the measures. The congruence of the greater circumferences cannot be subtracted: at points X, Y of them the angles AXB, DYE are the halves of the equal angles AKB, DLE at the centres (III.20), so the greater segments are similar, and III.24 makes them congruent, named by C and F (`Arc.Congruent.congr_side`).
- C, G, F and H name only sides of AB and DE. Points of each circle on those sides (`Prop2.oppositeSide`, from III.2) give III.26 its setting-out.

## III.29
- Euclid's figure has BGC less than a semicircle. When the centre K is on BC, both straight lines are diameters, each two radii; Heath calls this case "even easier than the corresponding case of III. 28 itself" (vol. 2, p. 61). When BGC is greater than a semicircle, the angle BKC stands on BAC, the circumference that remains, and equal circumferences taken from equal circles leave equal circumferences (`Circumference.whole`, C.N. 3).
- Equal circumferences are both less than a semicircle, both semicircles, or both greater (`Prop29.size`), so L falls as K does.
- "Let the centres of the circles be taken" has no bracket for III.1, and needs none: our equal circles carry their centres (`EqualCircles`, Definition III.1).
- Heath adds that III.26–III.29 "are of course equally true if the *same* circle is taken instead of *two equal* circles" (vol. 2, p. 61). A circle is equal to itself (`EqualCircles.refl`), and III.30 uses III.28 so.

## III.30
- "Let AB be joined and bisected at C; from the point C let CD be drawn at right angles": Heath gives no bracket for either: they are I.10 and I.11.
- D, where CD meets the given circumference: C is within the circle (III.2), so the straight line meets the circle on the side of the given circumference (`line_circle_beyond`, with CD produced backwards first, Post. 2).
- "And each of the circumferences AD, DB is less than a semicircle": Euclid gives no reason, yet III.28 pairs the less with the less. The angles DAB, ABD are equal (I.4), and two of them are less than two right angles (I.17), so each is less than a right angle; a circumference is twice the angle standing on it (`Circumference.standing`), so AD and DB are less than semicircles, and the circumferences remaining are greater (`Circumference.whole`).
- III.28 is said of equal circles, and used here in one (`EqualCircles.refl`), as Heath allows under III.29.
- "Therefore the given circumference has been bisected at the point D": Euclid takes from the figure that the circumferences AD, DB make up ADB and share only D. The companion `Prop30.halves` proves it: they add to the given circumference (`Circumference.add`), and divide it point by point by III.2.

## III.31
- "Therefore each is right [I. Def. 10]": Postulate 4 makes each the one right angle `∟`, as in III.3.
- Euclid finds the angle in the greater segment less than a right angle at B, the end of the diameter, but IV.5 needs it at any point of the segment. Our statement says it at every point X: a point D of the less segment (`Prop2.oppositeSide`, from III.2) and III.22 for the quadrilateral AXCD give it.
- The angles of the segments are contained by a straight line and a circumference (Definition III.7). The main proof establishes the right angles BAC and FAC; the companions `Prop31.greater` and `Prop31.less` carry the mixed-angle comparisons, reading each angle as the region it opens near its vertex.

## III.32
- Euclid's figure has the circle, but for B, on one side of EF. Were two of its points on opposite sides, the straight line joining them would cross EF within the circle (III.2), and no point of a straight line touching a circle is within it (`Prop32.sameSide`).
- The figure also puts D on F's side of BA; otherwise the argument runs with E and F exchanged.
- When D is A, BD is itself the diameter and every angle in either segment is right (III.31). Heath remarks under III.33 that Euclid "has not, in III. 32, distinguished the case in which the cutting and touching straight lines are at right angles, i.e. in which the two alternate segments are semicircles" (vol. 2, p. 70).
- Heath gives no bracket for "let BA be drawn from B at right angles to EF" or for "the angles DBF, DBE are also equal to two right angles": they are I.11 and I.13. His A is the end of the diameter; any other angle in the segment BAD is equal to it by III.21, which he does not use.

## III.33
- "It is assumed in Euclid's proof of the first and third cases that AE and FG will meet; but of course there is no difficulty in satisfying ourselves of this" (vol. 2, p. 70). Our proof takes the meeting from Postulate 5 (`Postulate5`): the angle EAF is less than a right angle and the angle AFG is right. In the obtuse case, that EAF is less than a right angle needs DA produced beyond A.
- Heath gives no bracket for constructing the angle BAD, bisecting AB or drawing AE and FG at right angles: they are I.23, I.10 and I.11.
- "Therefore the circle described with centre G and distance GA will pass through B also": Definition I.15 says that the points of a circle are a radius away; that B, a radius away, is on the circle is the proved Diagram-segment 3 (`on_circle_of_len_eq`, from Postulate 3 and `circle_eq`, as in III.8).
- Which side of AB each point lies on is left to the three figures: G across AB from D when the angle is acute, on D's side when it is obtuse. In the second case E stays on D's side, as in Euclid's figure, so III.31 is used and not III.32, as Heath observes (vol. 2, p. 70).

## III.34
- "Let EF be drawn touching ABC at the point B": Heath gives no bracket for it. It is the porism to III.16, at right angles to the radius at B (I.11), and for that the proof takes a centre from `exists_centre`.
- "Let the angle FBC be constructed equal to the angle at D [I. 23]" leaves the side of EF to the figure. On the side away from the centre the arm never meets the circle, so the angle is laid on the centre's side.
- C is read off the figure. III.16 puts a point of the new straight line within the circle, so it meets the circle again (`line_circle_beyond`). C lies on the centre's side of EF, for otherwise the straight line from C to the centre would cross EF within the circle (`Touches.not_inside`).
- Euclid names A first, as a letter of the circle; our proof takes it last, any point of the alternate segment, which III.32 allows.

## III.35
- "Let the centre of ABCD be taken, and let it be F; from F let FG, FH be drawn perpendicular": Heath gives no bracket for either: `exists_centre` supplies F, and I.12 supplies the perpendiculars.
- III.3 needs G between A and C, and H between D and B: `foot_between`, by I.17 and I.19.
- Simson, following Johannes Campanus, adds the cases where one straight line passes through the centre and the other does not (Heath, vol. 2, p. 73). Our proof gives Euclid's argument once, for any straight line through E (`Prop35.cut`), and it covers them, and serves for DB as "For the same reason".
- When E is the foot G, AC is cut equally at E and II.5 has nothing to give; the square on EG is then nothing, and the argument holds all the same.
- I.47 is said of squares on straight lines (`BookI.Prop47.sq`), as in III.14.

## III.36
- "Let F be the centre", and in the second case "let the centre E be taken", have no bracket, nor has "from E let EF be drawn perpendicular to AC": `exists_centre` supplies the centre in each case, and I.12 supplies the perpendicular.
- III.3 needs F between A and C (`foot_between`).
- I.47 needs FBD a triangle, and EBD in the second case: the centre is within the circle (`centre_inside`), and no point of DB, which touches it, is within (`Touches.not_inside`), so the centre is off DB.
- I.47 is said of squares on straight lines here too (`BookI.Prop47.sq`).

## III.37
- "Let DE be drawn touching ABC; let the centre of the circle ABC be taken, and let it be F": Heath gives no bracket for either: III.17 supplies DE, and `exists_centre` supplies F.
- "Therefore DE is equal to DB": equal squares are on equal straight lines (`BookI.Prop46.sq`), as in III.14.
- I.8 needs DBF to be a triangle, which Euclid reads off his figure. Were B on DF, either D would be within the circle, or two sides of the triangle DEF would together equal the third, against I.20 (`Prop37.triangle`).
- De Morgan finds here "the same defect as in I. 48, i.e. an apparent avoidance of indirect demonstration by drawing the tangent DE on the opposite side of DF from DB" (Heath, vol. 2, pp. 76–77). III.17 does not say which straight line it draws. Our proof holds for either, even with E at B, for our I.8 does not ask on which side of DF the triangles lie.
- "And FB produced is a diameter": our porism to III.16 is said at the end of a radius, so FB need not be produced.
- "Similarly this can be proved to be the case even if the centre be on AC": Euclid leaves this case to the reader. `Prop37.centre_on_secant` proves it from `Prop36.through_centre`, III.36's diameter case, and the given equality, then by Euclid's comparison of two triangles through I.8.

## The postulates: what the Lean uses and what Heath's brackets give

Heath's brackets name no postulate in Book III. The certificate counts everything a proof rests
on, the propositions it cites included; these are the places where a proof's own steps
use one.

- **Postulate 1**: naming a straight line before a point can be on it or off it, as
  in Books I and II.
- **Postulate 2**: Euclid produces straight lines with no bracket, as BA "carried
  through to F" in III.31, and our proofs produce more: EA beyond A, so that only one
  straight line is at right angles at A (`Prop1.perpendicular`, used again in III.16 and
  III.19); a straight line produced backwards from a point within the
  circle, so that `line_circle_beyond` meets the circle on the side we want (III.7,
  III.30); a side of a triangle, since our I.32 asks for one produced (III.22,
  III.32, `Prop24.isosceles`, `Circumference.semicircle`); the radius AD beyond the
  centre D, to the diameter III.16 asks for, in its porism (`Prop16.porism`); DA beyond
  A in III.33; and FB beyond B in III.34, so that the touching line EF runs on through
  B to either side; and in III.10 the two perpendiculars beyond their feet, since the
  argument needs a second point of each and never where it meets the circle. Where
  Euclid draws a straight line through to the circle (III.1, III.20, III.23),
  Intersections 5 does the producing, as in I.2.
- **Postulate 3 and Definition I.15**: circles Euclid does not draw. The two of I.1
  find a point off a straight line (`exists_off_line`), in III.1, III.17, III.33 and
  III.34, and inside `BookI.Prop46.sq`, which brings them to III.14 and III.37. A
  circle lays a radius along a ray (`OnRay.exists_len_eq`) in III.8 and III.27, and
  keeps a point near another (`exists_between_nearer`) in III.12. And Euclid draws the
  circles of III.17 and III.33, but with no bracket for the circle. Heath's brackets give
  Definition I.15 in III.5 alone, and most proofs use it.
- **Postulate 4**: turning Definition I.10's right angles into the one magnitude `∟`,
  in III.1, III.3, III.9 and III.31, just where Heath's bracket gives [I. Def. 10].
- **Postulate 5**: the Lean uses it directly in III.25 and III.33, where Euclid takes
  for granted that two straight lines meet. Through what it cites, III.14 rests on it,
  by the squares of I.46 and I.47, and III.15 through III.14; so does every proposition
  from III.20 on: fourteen by I.32, III.35–III.37 by the squares again, and III.25 by
  the postulate alone. III.1–III.13 and III.16–III.19 do not.
