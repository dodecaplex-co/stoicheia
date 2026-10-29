# What Euclid takes for granted: Book I

A running catalogue of the steps in Book I that Euclid takes without saying why,
found by writing his proofs out in Lean. Many were noticed long ago, by Proclus,
by Henry Savile, by Sir Thomas L. Heath and others, and by everyone who has formalized Book I since:
Jeremy Avigad, Edward Dean and John Mumma (System E); Michael Beeson, Julien
Narboux and Freek Wiedijk; Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima
Anandkumar and Xujie Si (LeanEuclid); André Hernández-Espiet and Alex Kontorovich;
and Tadd Mao, Tianjun Zhong, Dhruva Arekar, Yuming Feng, One An, Jiani Huang, Xujie
Si and Ziyang Li, whose
[*Does the Proof Prove It That Way?*](https://arxiv.org/abs/2608.15432) (Pistis)
catalogues 52 gaps in Books I–III and is the natural companion to this one. Where
we know who saw a gap first, we say so; nothing here is meant to be new except
where marked.

Each entry names the Lean lemma or tacit rule that fills the gap. A lemma named
after a proposition, such as `Prop7.cases`, lives beside it. Most are particular to
one proposition's figure and live in its file. A few are steps that several proofs
share and that cite a proposition, which Book Zero may not do: `Prop5.base`, the
angles at the base of I.5 with the sides produced for us, lives in
`Elements/BookI/Helpers.lean`; the steps that cite I.28, I.30 or I.31, such as
`Prop30.meet`, live in `Elements/BookI/HelpersParallels.lean`; and corollaries that
later proofs draw from a proposition, such as `Prop29.alternate`, `Prop34.bisect`
and `Prop46.side_eq`, follow it in its own file. The other lemmas are general and
live in Book Zero (`Elements/Figure/`), where any proof may cite them.

## I.1
- The two circles cut one another. Heath: "It is a commonplace that Euclid has no right to assume, without premising some postulate, that the two circles *will* meet in a point C" (vol. 1, p. 242). Filled by the tacit rule `circles_meet` (System E, Intersection 5).
- C is not on AB, so ABC really is a triangle (`Prop1.figure`).
- The circles cut one another on both sides of AB, so the triangle may be put on either side. Euclid relies on this without saying so in I.9, where the triangle on DE must fall on the side away from A, and in I.11. I.1 is stated with a side to choose (System E, Intersections 8).

## I.2
- The circles about B and D are met by DB and DA produced (`line_circle_beyond`, System E, Intersections 5); Euclid's Postulate 2 steps are absorbed into this.
- A lies inside the circle GKL, because DA is only part of DG (C.N. 5).

## I.3
- The circle about A meets AB at a point E between A and B, because B lies outside it (`outside_of_len_gt`, `line_circle_between`). This needs the straight line AB itself, hence Postulate 1.

## I.4
- "B will also coincide with E, because AB is equal to DE" uses the converse of C.N. 4 for straight lines (Heath, vol. 1, p. 250). `OnRay.eq_of_len_eq` proves it by Savile's argument: if B fell short of E or beyond it, the less would equal the greater.
- "AC will also coincide with DF" needs that only one ray on that side of DE makes the given angle: the law of one ray for one angle, cited inside the placement (`Superposition.Derives.ray_of_angle`) and proved with its three straight lines named (`Superposition.onLine_of_angle_eq_named`).
- J. L. Heiberg's bracketed "two straight lines will enclose a space" is not needed: a finite straight line is fixed by its ends, and so is its length (`CommonNotion4`).
- The moved triangle keeps its area (System E, Metric 9, `area_congruent`).

## I.5
- F is taken "at random" on BD, but must be close enough to A that AE is the greater (`exists_between_nearer`, which draws a circle about A).
- F, taken between B and D, still lies beyond B as seen from A, so that B is between A and F (`between_cut`).
- G lies beyond C on AE (`OnRay.between_of_len_lt`).
- The angle FAG is common to both triangles, and BFC is AFC, because the points lie on the same rays (`angle_onRay_left`, System E, Diagram-angle 4).
- The angles ABG, ACF are made up of ABC, CBG and ACB, BCF (`angle_add_of_between`, Pasch 2 and Diagram-angle 2).
- Each of AFC, AGB, FBC, GCB is a genuine triangle (`Triangle.of_line`).

## I.6
- The triangle DBC is less than the triangle ABC because D lies between A and B; Heath notes the tacit assumption (vol. 1, p. 256). `Prop6.less`, from Diagram-area 1 and 2 and C.N. 5.
- DBC is a triangle, and the angle DBC is the angle ABC (`Prop6.figure`, `angle_onRay_left`).
- "One of them is greater" is the law that of two unequal magnitudes one is the greater (`lt_trichotomy`); the case where AC is the greater is the same argument with B and C exchanged.

## I.7
- Euclid draws one figure. There are four configurations: AD crosses CB, AC crosses DB, D within the triangle ABC, C within ABD (`Prop7.cases`, `Prop7.cross`). The "within" case is the one Proclus answers with the second part of I.5 (Heath, vol. 1, p. 260; `Prop7.within`).
- CB falls within the angle ACD and DA within the angle CDB (`Prop7.figure`, from Pasch 2 and Diagram-angle 2), the "relative positions" Heath mentions.
- The step Heath says it would be natural to insert, "the angle ACD is greater than the angle BCD [C.N. 5]", also needs ACB to be a genuine angle (Diagram-angle 1).
- D is on neither AC nor BC, which Heath says "does not require proof" (`Prop7.triangle`).

## I.8
- C comes down on F's side of E along EF, as far from E as F is, so on F (`OnRay.eq_of_len_eq`).
- A comes down on the same side of EF as D, which I.7 needs; Euclid never says so.
- "The same side of this line EF" becomes "the same side of the straight line EF" by the uniqueness of the line through two points (`SameSideOf.of_line`).

## I.9
- The equilateral triangle on DE goes on the side away from A (Heath, vol. 1, p. 264), and our I.1 lets the side be chosen.
- D, taken "at random" on AB, must be nearer A than C is, so that I.3 can be used (`exists_between_nearer`, as in I.5).
- F falls within the angle BAC: the question of Proclus' objector (Heath, vol. 1, p. 265). If F were on an arm, Proclus' own argument with the second part of I.5 rules it out; if outside the angle, I.7 does (`Prop9.crossing`, `Prop9.not_on_arm`); and from the point where AF crosses DE, `Prop9.side` reads off which side of AB and of AC F lies on.
- Euclid proves the angles DAF and EAF equal, but the angle to be bisected is BAC. DAF and EAF are BAF and FAC because D and E lie on the rays from A through B and C (`angle_onRay_left`, `angle_symm`), and BAC is made up of them because F lies within it (`angle_add_of_inside`, System E, Diagram-angle 2).

## I.10
- The bisector of the angle ACB meets AB, and between A and B: I.9's statement (F within the angle) and Book Zero's `crossbar`.

## I.11
- I.3 needs a greater line to cut from, and Postulate 2 gives no length; room is found with a circle (`produce_longer`, used again in I.16, I.20 and I.22).
- C lies between D and E, which makes the angles DCF and FCE adjacent (`between_cut`).
- "At right angles to AB" means at right angles to every point of AB, not only D and E (`OnRay.cases_of_between`).
- Turning Definition I.10's "right" into the one magnitude of all right angles takes Postulate 4, which no bracket names here.

## I.12
- The circle about C through D cuts AB twice. `OppositeSides.exists_between` finds X on AB between C and D; CX is less than the radius CD, so `InsideCircle.of_between_centre` puts X within the circle. The theorem `line_meets_circle_of_inside` (System E, Intersection 3) then gives the two distinct crossings E and G, proved in `Elements/Figure/Incidence.lean` by applying `line_circle_beyond` in both directions.
- "Perpendicular to the infinite straight line" again means a right angle with every point of AB (`OnRay.cases_of_between`, as in I.11).
- HGC and HEC, the triangles I.8 compares, are genuine triangles: H, G and E are on AB, and C is off it (`Triangle.of_line`).

## I.13
- Euclid's figure has BA leaning towards C; the other lean is his figure with C and D exchanged (`Prop13.cases`).
- A could, in principle, lie on the perpendicular BE; it can't, since then the two angles would be equal (`Prop13.cases`).
- BE must be drawn on A's side of CD; the figure decides it, and I.11's statement lets us choose.
- "The angle DBA is equal to the two angles DBE, EBA" needs BE within DBA, a triple-incidence argument (`Prop13.within`).
- "The same three angles": CBA, ABE, EBD and DBE, EBA, ABC are the same only because an angle is the same read from either arm (`angle_symm`, System E, Metric 4) and magnitudes add in any order (`add_comm`, `add_assoc`).

## I.14
- Euclid's figure has BE within the angle ABD; the other case, BD within ABE, needs handling too (`onRay_of_angle_eq`).
- E and D lie on the same side of AB, each being on the other side from C (`OppositeSidesOf.of_between`, `OppositeSidesOf.sameSideOf`): the one place the hypothesis "not lying on the same side" is used, as Proclus warned.
- "AB stands on the straight line CBE" needs A off CBE before I.13 applies: that straight line passes through B and C, and A, B, C are not on one straight line.
- "Therefore CB is in a straight line with BD": the supposition having failed, D lies on the ray from B through E, and every point of that ray lies beyond B from C (`OnRay.between`).

## I.15
- The two straight lines really cross, so that each "stands on" the other before I.13 applies (`Prop15.figure`).
- "Similarly it can be proved" hides a third use of I.13.
- Heath's bracketed Porism (four angles about a point make four right angles) is also proved, as `Prop15.porism`.

## I.16
- CF falls within the angle ECD, so that "the angle ECD is greater than the angle ECF" (C.N. 5). Heath notes this fails in Bernhard Riemann's closed, sphere-like geometry (vol. 1, p. 280); in our proof it comes from Pasch's rules and the two sides of a line (`Prop16.within`), and then `angle_add_of_within` and `Triangle.angle_pos`.
- BE produced must be long enough for I.3 to cut EF off it (`produce_longer`, as in I.11), which takes a circle (Post. 3) that Euclid does not draw.
- "Similarly" becomes one argument applied twice, the second time with AC produced, and I.15 finishes it.
- The angle ECD becomes the angle ACD, and BAE the triangle's angle BAC, without a word, since E lies on the ray from C through A and on the ray from A through C (`angle_onRay_left`, `angle_onRay_right`).

## I.17
- "Let the angle ACB be added to each" has no bracket, and no Common Notion adds the same thing to unequals. It is the tacit law of magnitudes `add_lt_add_right` (System E §3.5). Heath points to this step as the one the rejected axiom "*If equals be added to unequals*" was after (vol. 1, p. 223).
- I.13 needs AC to stand on BD with A off it: D is on BC produced, and A is off BC because ABC is a triangle (`Triangle.off_line`, `Triangle.of_line`). To say so, the straight line BC is named (Post. 1) before Postulate 2 produces it.
- "Similarly" becomes one argument applied three times, to the triangles ABC, BAC and CAB, the triangle named afresh each time (`Triangle.bac`, `Triangle.cab`).
- Euclid names one angle two ways (ACB, then BCA in the sum; ABC where I.16 gives CBA) and adds in either order. Our proof turns each angle round (`angle_symm`, System E, Metric 4) and reorders the sums (`add_comm`).

## I.18
- "The angle ADB is equal to the angle ABD, since the side AB is equal to AD" is I.5, given without a bracket. Our I.5 also speaks of the angles under the base, so the sides are produced for it (`Prop5.base`).
- The angle DCB that I.16 gives is the triangle's angle ACB, because D lies on the ray from C through A (`angle_onRay_left`).
- Before I.16 applies, BCD must be a triangle: B is off the straight line AC, on which C and D lie (`Triangle.of_line`); and its side CD is already produced, to A, because I.3 put D between A and C.
- "Much greater" needs BD to fall within the angle ABC, so that ABD is only a part of it: D lies between A and C (`angle_add_of_between`), the other part DBC is something (`Triangle.angle_pos`), and then C.N. 5 and `lt_trans`.

## I.19
- "AC is either equal to AB or less" is the division Proclus names (Heath, vol. 1, p. 285): of two magnitudes, one is the greater or they are equal (`lt_trichotomy`).
- The "less" case is I.18 for the triangle with B and C exchanged (`Triangle.acb`), with each angle turned round to match (`angle_symm`).
- The rest is laws of magnitudes: `Magnitude.ne_of_lt`, `lt_trans`, `lt_irrefl`.

## I.20
- "Let DA be made equal to CA" has no bracket, but it is I.3's work, and I.3 cuts off only from a greater straight line. BA is produced far enough first (`produce_longer`, as in I.11 and I.16), and `between_cut` then puts A between B and D.
- "The angle BCD is greater than the angle ADC [C.N. 5]" needs CA within the angle BCD, which holds because A lies between B and D (`angle_add_of_between`, `Triangle.angle_pos`).
- The angle ADC becomes the angle BDC without a word, since A lies on the ray from D through B (`angle_onRay_left`); and DB is BA and AD together (System E, Diagram-segment 1).

## I.21
- "Let BD be drawn through to E": that BD, produced, reaches AC at all is the crossbar theorem, since D lies within the angle ABC (`crossbar`).
- That it reaches AC beyond D, so that D lies between B and E: B and D are on one side of AC (System E, Pasch 3), and E is on the ray from B through D (`Prop21.through`).
- Before I.20 and I.16 apply, ABE and CED must be triangles. C is off BE because D, on A's side of BC, is off BC (`Triangle.of_line`, `Triangle.off_line`).
- "Let EC be added to each" and "let DB be added to each" have no bracket, and no Common Notion adds the same thing to unequals: as in I.17, it is the tacit law of magnitudes `add_lt_add_right`.
- "BA, AC are greater than BE, EC" needs AE and EC to make up AC, since E lies between A and C, and in the same way ED and DB make up EB (System E, Diagram-segment 1).
- The angle CED is the angle CEB, and BAE is BAC, because each pair of points lies on one ray (`angle_onRay_right`).

## I.22
- The circles meet. Heath: "It was early observed that Euclid assumes, without giving any reason, that the circles drawn as described will meet" when the condition holds (vol. 1, p. 293). Proclus argued it but missed the case of one circle within the other, and Robert Simson thought no beginner so dull as not to see it. `Prop22.meet` follows Heath's own argument (vol. 1, p. 294): the circle about G has a point outside the circle about F and a point inside it, so they cut one another (System E's Intersection rule 4, `circles_meet_of_on_inside_outside`, in the corrected form Logan Murphy and his colleagues gave it in LeanEuclid). Intersection 4 is now proved from Intersection 5 and `line_circle_between` in `Elements/Figure/Incidence.lean`, finding the crossing from the centre of the first circle. Intersection 4 takes that centre from our rule that every circle has a centre (`exists_centre`), but `Prop22.meet` has it already, G, and gives it to the lemma that carries the proof (`circles_meet_of_centre`); so since 26 October 2026 I.22 rests neither on Circle 1, which the proof used before, nor on our rule. Our proof also covers the case Heath passes over, where the inside point is the centre F itself.
- DE is "of infinite length in the direction of E", but I.3 cuts off only from a greater finite straight line, so each cut needs room first (`Prop22.room`: I.2, then `produce_longer`). That is why I.2 is among the propositions I.22 cites.
- None of A, B, C is nothing, which I.3 needs (`Prop22.ne_zero`).
- DF, FG and GH are cut off one after another, so that D, F, G, H lie in that order along DE, as in Euclid's figure (`between_cut`). Heath's argument that the circles meet needs it, since FH must be FG and GH together.
- K is taken where the circles cut one another on a chosen side of DE (System E, Intersections 8), so that I.23 can place the triangle where it wants it.

## I.23
- I.22's condition is not repeated here. The three straight lines are the sides of the triangle DCE, so I.20 supplies it, as the bracket in I.22's enunciation suggests.
- Heath: "the construction of the triangle assumed in this proposition is not exactly the construction given in I. 22" (vol. 1, p. 295). Our I.22 is stated with its corner at a given point, a side along a given ray and its third corner on a given side, which is what I.23 asks of it.
- AFG is a triangle, as I.8 needs: G is on AB and is not A, and F is off AB (`OnRay.onLine`, `SameSideOf.triangle`, `Triangle.off_line`, `Triangle.of_line`).
- D and E are taken "at random", and the choice does not matter because an angle depends only on its rays (`angle_eq_of_onRay`).
- DCE must be a triangle for I.20 and I.8, so D and E are not on one straight line with C. Definition I.8 already asks this of a plane angle, whose lines "do not lie in a straight line"; a flat angle could not be copied this way, having no triangle to carry. The statement takes the given angle as the triangle DCE.
- Which ray from A, and which side of AB, the new angle takes are left to the figure. The statement settles both, as I.24, I.31 and I.42 need.

## I.24
- Euclid gives one case, F below EG. Simson added a sentence to make it the only one, and Heath leaves it out (vol. 1, p. 297). Our proof inserts Simson's words: the statement reads the same with B and C, and E and F, exchanged, so DE may be taken not greater than DF. F lies within the angle EDG (`Prop24.within`), and then below EG (`Prop24.below`), by the lemma Heath gives (vol. 1, p. 298) from I.16, I.18 and I.19, with I.5 when DE equals DG; Heath's proof gives no reference for any of them. Proclus' two other cases (Heath, vol. 1, p. 297) are told in the mishnah.
- "Let DG be made equal to either of the two straight lines AC, DF" has no bracket; a circle about D lays it off (`OnRay.exists_len_eq`).
- G is on the same side of DE as F. I.23 lets us ask for that side, and `SameSideOf.of_onRay` keeps the point laid off along the arm there.
- "The angle DFG is greater than the angle EGF", and "much greater", are each the whole greater than the part, because DF meets EG at a point H between D and F and between E and G (`angle_lt_of_between`).

## I.25
- "For, if not, it is either equal to it or less" is the division of I.19 (`lt_trichotomy`), and the last step, "therefore the angle BAC is greater than the angle EDF", is a *reductio ad absurdum* (`Classical.byContradiction`).
- "For then the base BC would also have been less than the base EF" is I.24 with the triangles exchanged, DEF first, so the equal sides are read the other way round: DE equal to AB, and DF to AC.
- Each "but it is not" is a law of magnitudes: BC, being greater than EF, is not equal to it (`Magnitude.ne_of_lt`), nor less (`lt_trans`, `lt_irrefl`).

## I.26
- "Let BG be made equal to DE", and in the second part "let BH be made equal to EF", have no bracket, but each is I.3's work (`Prop3`), as in I.20; and I.3 puts G between B and A, and H between B and C.
- GBC, ABH and AHC are genuine triangles, as I.4 and I.16 need (`Triangle.of_line`). The angles GBC and ABH are the angle ABC, their arms being the same rays (`OnRay.of_between`, `angle_onRay_left`, `angle_onRay_right`); and "the less to the greater" needs the angle BCG to be a part of BCA, since G lies between B and A (`angle_lt_of_between`).
- "If AB is unequal to DE, one of them is greater", and Euclid lets it be AB. The other case is the same argument with the triangles exchanged, written once and used twice, and so is the second part's (`lt_trichotomy`).
- The equal sides must be corresponding sides, both adjoining the equal angles or both subtending equal angles; Heath explains that a figure of Proclus shows just this (vol. 1, p. 306). The statement names them so: BC and EF, or AB and DE.

## I.27
- Euclid's two directions, "in the direction of B, D or towards A, C", are the two sides of EF; the Greek speaks of parts, Heath notes (vol. 1, p. 308). A point where AB and CD meet is off EF, for AB meets EF at E alone, and were the point E, CD would be EF itself, with D on it (System E, Generalities 1). So it lies on D's side or on A's, since a straight line has just two sides (`same_side_or`, System E, Same side 5), now proved in `Elements/Figure/Incidence.lean` from Intersection 1, Pasch 3 and 4 and the three collinear orders.
- "The exterior angle AEF" of the triangle GEF needs E between A and G, and "the interior and opposite angle EFG" needs EFG to be the given angle EFD. Euclid reads both off his figure. B lies on G's side of EF, so G lies on the ray from E through B (`OnRay.of_sameSideOf`), beyond E from A (`OnRay.between`); and G lies on the ray from F through D, so EFG is EFD (`angle_onRay_right`).
- "Similarly" is the same argument with the figure read from the other end, D, C, B, A for A, B, C, D, written once and used twice, as in I.16.

## I.28
- "And they are alternate": I.27 needs A and D on opposite sides of GH. The statement puts B and D on one side of EF, which is the straight line GH (`SameSideOf.inner`), and G lies between A and B, so A is across GH from D (`SameSideOf.oppositeSidesOf_of_between`).
- The same hypothesis keeps B off GH, so that AB and EH really cut one another at G, as I.15 needs, and H off AB, so that GH stands on AB, as I.13 needs.

## I.29
- Postulate 5, as Euclid calls on it here, leaves out its conditions. Heath: "A good deal is left to be understood, namely that the straight lines begin from points at which they meet a transversal" (vol. 1, p. 312). `Postulate5` asks for all of it: the straight lines through B and G, through G and H, and through H and D, with B and D on one side of GH (`SameSideOf.inner`).
- Euclid lets the angle AGH be the greater and leaves out the case where GHD is. That is his argument from H's end, on the side of A and C, with I.13 at H, written once and used twice.
- "Let the angle BGH be added to each" has no bracket: as in I.17, it is the tacit law of magnitudes `add_lt_add_right`.
- I.13 and I.15 need H off AB and B off EH. Both follow from B's being off GH, which comes from the statement's same-side hypothesis and not from the parallels.

## I.30
- Heath's figure puts EF between AB and CD, so that GK crosses it at H (`OppositeSides.exists_between`). The enunciation also covers EF lying outside both, where a straight line from one to the other need not cross it. For that case we prove from I.29 that two straight lines through one point, each parallel to a third, are one straight line (`Prop30.unique`), which supplies only the meeting of GH, drawn from AB to EF, with CD; Euclid's own chase does the rest, with CD or AB in the middle. Uniqueness is Playfair's axiom, of which I.30 is the logical equivalent, as Heath reports Augustus De Morgan pointing out (vol. 1, p. 314).
- The given points need not stand where Heath's do, so `Prop30.point_on_side` takes an end of each straight line on whichever side of GK his figure wants, producing it if it must.
- Each citation of I.29 needs Euclid's whole figure: the falling straight line meets each parallel between two of its points, and itself goes on beyond both. Book Zero produces the straight lines to make it (`AreParallel.figure_alternate`, `AreParallel.figure_interior`), and later proofs reach it through `Prop29.alternate`, `Prop29.interior` and `Prop29.exterior`.
- "And they are alternate. Therefore AB is parallel to CD" is I.27, though Heath gives no bracket for it.

## I.31
- The given point A is off the given straight line BC; the statement asks it (`¬ Collinear B C A`).
- D, "taken at random on BC", is taken between B and C, as in Euclid's figure (`exists_point_between`, System E, Points 3, now proved in `Elements/Figure/Incidence.lean` from smaller concentric circles, Definition I.15 and circle crossings), so that B and C lie on either side of AD (`OppositeSidesOf.of_between`).
- The angle DAE must be built on the side of AD away from C, or EAD and ADC would not be alternate angles, as I.27 needs. Our I.23 lets the side be named, and B's is named (`SameSideOf.trans_opposite`).
- Proclus remarks that the construction implies that only one straight line through A is parallel to BC, and draws this from I.30: two such straight lines would be parallel, though they meet at A (Heath, vol. 1, p. 316). Our statement asks for a parallel, not the only one. The uniqueness is `Prop30.meet`, that a straight line meeting one of two parallels meets the other, and later proofs cite it wherever Euclid names a point on a parallel he has drawn: I.37–I.40, I.42, I.44, I.46 and I.47.

## I.32
- Euclid's figure puts E within the angle ACD. I.31 gives a straight line through C with a point on either side of C, and `Prop32.choose_end` takes the one on A's side of BC. Then E lies across AC from B, for otherwise the parallel would cross AB (`AreParallel.oppositeSidesOf`); so E and D are on one side of AC, and `angle_add_of_within` makes ACD the angles ACE, ECD together.

## I.33
- "(At the extremities which are) in the same directions (respectively)": the bracketed words are Heath's, inserted for clearness (vol. 1, p. 323). Our statement says it with `SameSideOf`: B and D lie on one side of AC. Book Zero's `AreParallel.oppositeSidesOf` then puts A and D on opposite sides of BC, so that ABC, BCD are alternate angles, as I.29 needs (`Prop29.alternate`).
- I.27 asks for BC to meet each of AC and BD between two of its points, so AC and DB are produced beyond C and B (Post. 2, `produce`), to ends Heath leaves without letters. What I.27 then says of the produced straight lines it says of AC and BD (`AreParallel.of_parallel`).

## I.34
- Euclid never defines a parallelogram. Proclus observes that I.33 gives "the construction or origin of the parallelogram" without expressing the fact, so that Euclid can speak here of "parallelogrammic areas" with no more explanation (Heath, vol. 1, p. 323). Our `Parallelogram` is a four-sided figure whose opposite sides are parallel, its corners taken in order round it.
- I.29 needs A and D on opposite sides of BC: the far corners of a parallelogram lie on one side of each side (`Parallelogram.sameSideOf`), and Book Zero's `AreParallel.oppositeSidesOf` does the rest.
- "The whole angle ABD is equal to the whole angle ACD [C.N. 2]" needs BC within both angles, which the parallelogram, named from each corner in turn, gives (`angle_add_of_within`).

## I.35
- Heath: "Euclid speaks of the triangle DGE without any explanation that, in the case which he takes (where AD, EF have no point in common), BE, CD must meet at a point G between the two parallels" (vol. 1, p. 327). `Prop35.figure` proves it from Book Zero's `AreParallel.cross_or`, and puts E between D and F, as "the whole DF" needs.
- Euclid gives one arrangement. Proclus, "observing that Euclid has given only the most difficult of the three possible cases, adds the other two with separate proofs" (Heath, vol. 1, p. 328): E between A and D (`Prop35.between`), and E at D (`Prop35.same`). Our proof also takes E at A, where F is D (`OnRay.eq_of_len_eq`), and each case the other way along AF, by exchanging the parallelograms (`AreParallel.sameSideOf_or`).
- Heath points out "the further *tacit* assumption that it is indifferent to *what part* or from *what part* of the same or equal areas the same or equal areas are added or subtracted", a postulate De Morgan thought particularly important (vol. 1, p. 328). In our foundations an area is a magnitude, so where it is added or taken away does not matter; what must be said is what a figure is made of. A straight line from a corner cuts a triangle into two that make it up (`area_cut`, System E, Diagram-area 2), and a four-sided figure is the two triangles a diameter cuts it into (`quadArea`): the trapezium ABGD by its diameter BD.
- A parallelogram has one area, whichever diameter cuts it: Book Zero shows that two diameters which cross give the same measure (`quadArea_rotate_of_cross`, `Parallelogram.quadArea_rotate`).

## I.36
- "Let BE, CH be joined": I.33 joins equal and parallel straight lines at the ends which are in the same directions, so C and H must lie on one side of BE. `AreParallel.sameSideOf_or` says they do, or else that E and C lie on one side of HB; the second is Euclid's case again, with EFGH read as HGFE.
- The second citation of I.35, on the base EH, may fall in any of its arrangements, since BC and FG may overlap or share an end. So I.36 needs the cases Proclus adds under I.35 as well as Euclid's. Heath reports Heron distinguishing "the different cases of I. 35, 36" (vol. 1, p. 22).

## I.37
- E and F are where BE and CF, the parallels I.31 draws, meet AD produced. That they meet at all is `Prop30.meet` (see I.31): AD meets CA at A, so it meets BE, the parallel to CA.
- "[But the halves of equal things are equal to one another.]" Heiberg brackets the words, but the step is needed all the same, and it is no inference from Common Notion 3. Paul Tannery observes that it needs a *reductio ad absurdum* through Common Notion 2, and Heath that even then "a little argument would be necessary" (vol. 1, p. 224). Book Zero gives it as `Magnitude.eq_of_add_self_eq`.
- "The diameter AB bisects it": `quadArea` measures EBCA by its diameter EC, so the figure is named from B (`Parallelogram.rotate`, `Parallelogram.quadArea_rotate`) before `Prop34.bisect` makes it twice ABC.

## I.38
- As in I.37: G and H, where BG and FH meet AD produced, come from `Prop30.meet`; the bracketed halves are `Magnitude.eq_of_add_self_eq`; and GBCA is named from B, so that its diameter is AB (`Parallelogram.quadArea_rotate`).
- I.42 cites this proposition for two triangles with one vertex, ABE and AEC, where Euclid's AD is no straight line at all. Our statement takes "in the same parallels" as two whole straight lines, so the vertices may be one point, and the "AD" that Euclid produces is the parallel through them.

## I.39
- E, where the parallel through A meets BD, comes from `Prop30.meet`: BD meets BC at B, so it meets the parallel to BC.
- "The greater to the less" needs to know where E falls. The parallel puts E on A's side of BC, and so on D's, on the ray from B through D (`OnRay.of_sameSideOf`). Euclid's figure has E between B and D; Proclus points out that the proof is as easy when it falls beyond D (Heath, vol. 1, p. 337). Either way one triangle is a part of the other (`area_lt_of_cut`, C.N. 5).
- Supposing AD not parallel to BC makes E differ from D. Both orders on the ray from B through D make one triangle strictly less than the other (`between_cases`, `area_lt_of_cut`), contradicting their equality. This excludes a proposed parallel through A meeting BD away from D and carries the closing "Similarly".

## I.40
- As in I.39: F, where the parallel through A meets CD, comes from `Prop30.meet`; the same-side hypothesis puts F on the ray from C through D (`OnRay.of_sameSideOf`); and the case Proclus adds under I.39, F beyond D, is taken with Euclid's (`area_lt_of_cut`).
- `Prop40.general` follows the same reductio for equal bases anywhere on one straight line, including coincident vertices.

## I.41
- E may lie anywhere on the straight line AD, at A or at D among them. One argument serves, since our I.37 takes "in the same parallels" as two whole straight lines and lets its two triangles share their vertex.
- E is off BC, for parallels do not meet (`Parallel.not_onLine`), so EBC is a triangle.

## I.42
- "Let BC be bisected at E" is I.10, though Heath gives no bracket.
- Euclid's F lies where the arm of the angle CEF meets AG, and G where CG, drawn parallel to EF, meets AG; both come from `Prop30.meet`. F must lie on the arm I.23 made, not behind E, or the angle CEF would not be equal to D: F is on A's side of BC, and so on the arm (`OnRay.of_sameSideOf`).
- "Therefore the triangle ABC is double of the triangle AEC" needs ABC to be ABE and AEC together (`area_cut`). The parallelogram FECG is double of AEC too, and Euclid concludes that the two are equal, by the axiom on doubles that Heath notes is tacitly assumed here (vol. 1, p. 224). Each is AEC added to itself, so Common Notion 1 does it (`CommonNotion1`).

## I.43
- "The complement BK which remains" takes for granted that the triangle ABC is made up of the triangle AEK, the complement BK and the triangle KGC. `Prop43.cut` proves it from the three betweennesses alone. BK separates E from G, so the diameters of the complement cross (`OppositeSides.exists_between`), at a point between B and K with no letter in the figure (`Between.of_inside`); either diameter then measures it (`quadArea_rotate_of_cross`), and `area_cut` gives the three pieces. Nothing in the proof uses that the complements are parallelograms.

## I.44
- "Let it be placed so that BE is in a straight line with AB": Euclid moves the parallelogram I.42 has made. Our Lean moves a figure only by superposition, which is kept for I.4 and I.8, so `Prop44.place` builds an equal one where Euclid puts it: I.2 copies its sides and I.23 its angle, I.31 and `Prop30.meet` complete it, and I.4 and I.34 make it equal. Which side of AB it stands on is left to the figure; the statement names it with a point P, and G goes on the other side, so that M falls on P's.
- H, L and M, where straight lines meet the parallels, come from `Prop30.meet`, and "parallel to either", said twice, is I.30 (`Prop30.parallel`); Heath's bracket names only I.31.
- Our proof must state the orders Euclid reads off his figure, H, G, F; H, B, K; F, E, K; K, M, L; L, A, H; and G, B, M, before I.43 and I.15 apply. Parallels keep order (`Between.of_sameSide`).
- "Therefore the angles BHG, GFE are less than two right angles" has no bracket: HB falls within the angle AHF (`angle_add_of_within`), and the part is less than the whole (C.N. 5).

## I.45
- Euclid divides the rectilineal figure ABCD by DB into the triangles ABD and DBC, and takes "the whole rectilineal figure ABCD" to be the two together. Any rectilineal area, Heath says, "can of course be resolved into triangles" (vol. 1, p. 347). Taken for granted is that the figure can be divided into triangles, and that every division gives the same whole: AC would give ABC and ACD. For a four-sided figure whose diameters cross, Book Zero proves the latter (`quadArea_rotate_of_cross`); for any figure and any division, David Hilbert proved it, for his measure of area ([*The Foundations of Geometry*](https://www.gutenberg.org/ebooks/17384), ch. IV, "The Theory of Plane Areas", section 20), and his own note to the chapter credits Gérard and F. Schur (1892 and 1898) with like theories and refers to an article by O. Stolz (1894). Book Zero proves division existence separately and proves division independence after Hilbert's theory of content, for a figure given by its outline alone, finitely many closed lines of straight sides: the figure has a division into triangles that do not overlap, no point inside two of them (`Figures.division_exists`), and any two divisions covering the same points have the same sum (`Figures.Apart.area_eq_of_same_region`), so the figure has one area (`Figures.Outline.area`), and `Prop45.outline` makes the parallelogram equal to it. The older companions take a figure given with a checked division into triangles: any division into triangles that lie apart, for a figure with any boundaries; for a figure with one boundary, triangles glued edge to edge in a suitable order; or Euclid's and Oliver Byrne's, by the straight lines from one corner, whose figure is the one bounded by the closed line through the corners in order (`Prop45.fan_boundary`). They make the parallelogram equal to those triangles, which is the figure's area, whatever the division.
- "KH, HM not lying on the same side" needs GM applied on the side of GH away from K, which Euclid leaves to the figure. Our I.44 is asked for that side, through a point across GH from K with no letter in Heath; the same choice puts F and L on either side of GH, as the second use of I.14 needs.
- Before I.30, our proof shows that KF and ML are different straight lines: were they one, it would be KM, and D, which is on KM, would lie on ML, a parallel to GD (`line_unique`, `Parallel.not_onLine`); before I.33, that F and L lie on one side of KM, each being on G's side (`same_side_trans`), so that KM and FL join them in the same directions.
- "The whole parallelogram KFLM" is FH and GM together, which needs K, H, M and F, G, L in order, as the two uses of I.14 give (`quadArea_add_of_parallelograms`).

## I.46
- "Let AD be made equal to AB" has no bracket. A circle about A lays it off along AC (`OnRay.exists_len_eq`, Post. 3), so I.3 is not needed, and C may fall on either side of D.
- E, where DE and BE meet, comes from `Prop30.meet`: DE meets AD at D, so it meets BE, the parallel to AD.
- Which side of AB the square stands on is left to the figure. The statement names it with a point off AB, since I.48 describes its squares outward from a triangle, as I.47 asks; `SameSideOf.of_onRay` and `Parallelogram.sameSideOf` keep D and E there.

## I.47
- "Let the angle ABC be added to each" needs C within the angle DBA, and A within the angle FBC. Euclid reads both off his figure. The angles at B and C are less than right angles (I.17), and the squares are described outward, so `Prop47.within` puts each point where the figure does, by I.13, and `angle_add_of_within` adds the angles.
- "Through A let AL be drawn parallel to either BD or CE" is I.31, though no bracket names it, and "either" is I.30 (`Prop30.parallel`). AL meets DE at L, and BC at a point Heath leaves without a letter (`Prop30.meet`).
- "The whole square BDEC" is the parallelograms BL and CL together only if the foot of AL lies between B and C, and L between D and E. A lies between BD and CE, so AL, parallel to both, crosses BC and DE between them (`Between.of_inside`), and `quadArea_add_of_parallelograms` puts the pieces together.
- Euclid's squares are described by I.46, so they are parallelograms, as I.41 needs. The main theorem takes its squares as given in the statement (Def. I.22), and `Prop28.square` (I.28) shows them parallelograms. The companion `Prop47.general` constructs outward squares by I.46, applies `Prop47`, and transfers the equality to either side by `Prop46.square_eq`.

## I.48
- "Let AD be drawn from the point A at right angles to the straight line AC" is I.11, though no bracket names it, and "let AD be made equal to BA" is a circle about A (`OnRay.exists_len_eq`, Post. 3).
- Euclid speaks of the squares on DA, AC and DC without describing them. Our proof describes them by I.46, outward from the triangle DAC, as I.47 asks.
- "Since DA is equal to AB, the square on DA is also equal to the square on AB", and later "so that the side DC is also equal to BC": squares on equal straight lines are equal, and equal squares stand on equal straight lines. Euclid assumes both; Heath reports Proclus proving them under I.46 (vol. 1, pp. 348–349). They are `Prop46.square_eq` and `Prop46.side_eq`.

## The postulates: what the Lean uses and what Heath's brackets give

[CERTIFICATE.md](../../CERTIFICATE.md) sets Heath's references, read from his
brackets, beside what the Lean uses, for every proposition; where the two differ
over a postulate, the reason is one of these.

- **Postulate 1**: our proofs name a straight line before they can say a point is
  on it or off it, or lay a figure along it. This is a difference in bookkeeping, not
  in geometry: Euclid's "the straight line AB" names the same line implicitly.
- **Postulate 2**: a straight line produced where Heath gives no bracket (I.14,
  I.31, and BE laid along AB in I.44); the given straight lines of I.30, produced
  so that each has an end on either side of GK, as in Heath's figure
  (`Prop30.point_on_side`); the sides of I.5 produced, because our I.5 is stated
  with them (`Prop5.base`); a straight line produced far enough for I.3
  to cut from (`produce_longer`); a straight line produced behind a point, so that
  a circle about it is cut on the side we want (`OnRay.exists_len_eq`); and
  straight lines produced so that a straight line falling on two others meets each
  of them between two of its points, as I.27, I.28 and I.29 ask
  (`AreParallel.figure_alternate`, `AreParallel.figure_interior`,
  `Prop28.interior`, and AC and DB in I.33). In I.2 the rule that a straight line
  through the inside of a circle meets it (System E, Intersections 5) does the
  producing, so that proof uses no Postulate 2, though Heath's bracket gives it.
  In I.5 the statement hands us the produced sides, but Postulate 2 still underlies
  proved rules: in its own Lean the order rule `between_of_between_right`, beneath
  `OnRay.between_of_len_lt`, and Metric 8, `area_swap`. I.4 reaches it through the proof of a law its derivation cites,
  one ray for one angle (`Superposition.Cited.holds_rayOfAngle`), by way of the proved
  Triple incidence 2, and I.6 through `area_swap` as well as I.4.
- **Postulate 3 and Definition I.15**: circles Euclid does not draw, which keep a
  chance point near enough (`exists_between_nearer`, I.5 and I.9), give a straight
  line room to be cut from (`produce_longer`), or lay a length along a ray
  (`OnRay.exists_len_eq`, I.24, I.44, I.46 and I.48); and circles he does draw, but
  without a bracket for the circle (I.22) or for its radii (I.2, I.12, I.22).
  Proved order and length rules also carry these assumptions: I.4 reaches them through
  the proofs of four laws its derivation cites (`Superposition.Cited.holds_neOfLen`,
  `Superposition.Cited.holds_rayUnique`, `Superposition.Cited.holds_rayOfAngle` and
  `Superposition.Cited.holds_rayOfAngleSide`, by way of
  `ne_of_len_eq`, `OnRay.eq_of_len_eq`, `Superposition.onLine_of_angle_eq_named` and
  Pasch 3), although its own construction draws no circle.
- **Postulate 4**: turning Definition I.10's right angles into the one magnitude `∟`
  that all right angles share.
- **Postulate 5**: no difference. The Lean uses it directly just where Euclid
  calls on it, in I.29 and I.44, and elsewhere only through the propositions cited:
  every proposition after I.29 but I.31 rests on it that way.

The certificate counts everything a proof rests on, the propositions it cites
included, so a postulate can be on a proposition's certificate when its own proof
never uses it.
