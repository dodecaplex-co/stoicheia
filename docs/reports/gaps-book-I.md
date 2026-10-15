# What Euclid takes for granted: Book I

A running catalogue of the steps in Book I that Euclid takes without saying why,
found by writing his proofs out in Lean. Many were noticed long ago, by Proclus,
by Savile, by Heath and others, and by everyone who has formalized Book I since:
Jeremy Avigad, Edward Dean and John Mumma (System E); Michael Beeson, Julien
Narboux and Freek Wiedijk; Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima
Anandkumar and Xujie Si (LeanEuclid); André Hernández-Espiet and Alex Kontorovich;
and Tadd Mao, Tianjun Zhong, Dhruva Arekar, Yuming Feng, One An, Jiani Huang, Xujie
Si and Ziyang Li, whose
[*Does the Proof Prove It That Way?*](https://arxiv.org/abs/2608.15432) (Pistis)
catalogues 52 gaps in Books I–III and is the natural companion to this one. Where
we know who saw a gap first, we say so; nothing here is meant to be new except
where marked.

Each entry names the Lean lemma or tacit rule that fills the gap. Lemmas named
`PropN.something` are particular to one proposition's figure and live in its file;
the others are general and live in Book Zero (`Elements/Figure/`), where any proof
may cite them. The one exception is `Prop5.base`, the angles at the base of I.5
with the sides produced for us: several proofs share it, and since it cites I.5 it
lives beside the propositions, in `Elements/BookI/Helpers.lean`.

## I.1
- The two circles cut one another. Heath: "It is a commonplace that Euclid has no
  right to assume, without premising some postulate, that the two circles will meet
  in a point C." Filled by the tacit rule `circles_meet` (System E, Intersection 5).
- C is not on AB, so ABC really is a triangle (`Prop1.figure`).
- The circles cut one another on both sides of AB, so the triangle may be put on
  either side. Euclid relies on this without saying so in I.9, where the triangle
  on DE must fall on the side away from A, and in I.11. I.1 is stated with a side
  to choose (System E, Intersections 8).

## I.2
- The circles about B and D are met by DB and DA produced (`line_circle_beyond`,
  System E Intersections 5); Euclid's Postulate 2 steps are absorbed into this.
- A lies inside the circle GKL, because DA is only part of DG (C.N. 5).

## I.3
- The circle about A meets AB at a point E between A and B, because B lies outside it
  (`outside_of_len_gt`, `line_circle_between`). This needs the straight line AB itself,
  hence Postulate 1.

## I.4
- "B will also coincide with E, because AB is equal to DE" uses the converse of
  C.N. 4 for straight lines (Heath, vol. 1, p. 250). `OnRay.eq_of_len_eq` proves it by
  Savile's argument: if B fell short of E or beyond it, the less would equal the greater.
- "AC will also coincide with DF" needs that only one ray on that side of DE makes the
  given angle (`onRay_of_angle_eq`).
- Heiberg's bracketed "two straight lines will enclose a space" is not needed: a
  finite straight line is fixed by its ends.
- The moved triangle keeps its area (System E, Metric 9, `area_congruent`).

## I.5
- F is taken "at random" on BD, but must be close enough to A that AE is the greater
  (`exists_between_nearer`, which draws a circle about A).
- F, taken between B and D, still lies beyond B as seen from A, so that B is between A
  and F (`between_cut`).
- G lies beyond C on AE (`OnRay.between_of_len_lt`).
- The angle FAG is common to both triangles, and BFC is AFC, because the points lie
  on the same rays (`angle_onRay_left`, System E Diagram-angle 4).
- The angles ABG, ACF are made up of ABC, CBG and ACB, BCF (`angle_add_of_between`,
  Pasch 2 and Diagram-angle 2).
- Each of AFC, AGB, FBC, GCB is a genuine triangle (`Triangle.of_line`).

## I.6
- The triangle DBC is less than the triangle ABC because D lies between A and B; Heath
  notes the tacit assumption (vol. 1, p. 256). `Prop6.less`, from Diagram-area 1 and 2
  and C.N. 5.
- DBC is a triangle, and the angle DBC is the angle ABC (`Prop6.figure`, `angle_onRay_left`).
- "One of them is greater" is the law that of two unequal magnitudes one is the greater
  (`lt_trichotomy`); the case where AC is the greater is the same argument with B and C
  exchanged.

## I.7
- Euclid draws one figure. There are four configurations: AD crosses CB, AC crosses DB,
  D within the triangle ABC, C within ABD (`Prop7.cases`, `Prop7.cross`). The
  "within" case is the one Proclus answers with the second part of I.5 (Heath,
  vol. 1, p. 260; `Prop7.within`).
- CB falls within the angle ACD and DA within the angle CDB (`Prop7.figure`, from Pasch 2
  and Diagram-angle 2), the "relative positions" Heath mentions.
- The step Heath says it would be natural to insert, "the angle ACD is greater than the
  angle BCD [C.N. 5]", also needs ACB to be a genuine angle (Diagram-angle 1).
- D is on neither AC nor BC, which Heath says "does not require proof" (`Prop7.triangle`).

## I.8
- C comes down on F's side of E along EF, as far from E as F is, so on F
  (`OnRay.eq_of_len_eq`).
- A comes down on the same side of EF as D, which I.7 needs; Euclid never says so.
- "The same side of this line EF" becomes "the same side of the straight line EF" by the
  uniqueness of the line through two points (`SameSideOf.of_line`).

## I.9
- The equilateral triangle on DE goes on the side away from A (Heath, vol. 1, p. 264); I.1 now takes the side as an argument.
- D, taken "at random" on AB, must be nearer A than C is, so that I.3 can be used (`exists_between_nearer`, as in I.5).
- F falls within the angle BAC: the question of Proclus' objector (Heath, vol. 1, p. 265). If F were on an arm, Proclus' own argument with the second part of I.5 rules it out; if outside the angle, I.7 does (`Prop9.crossing`, `Prop9.not_on_arm`).

## I.10
- The bisector of the angle ACB meets AB, and between A and B: I.9's statement (F within the angle) and Book Zero's `crossbar`.

## I.11
- I.3 needs a greater line to cut from, and Postulate 2 gives no length; room is found with a circle (`produce_longer`, used again in I.16, I.20 and I.22).
- C lies between D and E, which makes the angles DCF and FCE adjacent.
- "At right angles to AB" means at right angles to every point of AB, not only D and E (`OnRay.cases_of_between`).
- Turning Definition 10's "right" into the one magnitude of all right angles takes Postulate 4, which Euclid doesn't cite here.

## I.12
- The circle about C through D cuts AB twice (System E Intersection 2).
- "Perpendicular to the infinite straight line" again means a right angle with every point of AB (`OnRay.cases_of_between`, as in I.11).

## I.13
- Euclid's figure has BA leaning towards C; the other lean is his figure with C and D exchanged (`Prop13.cases`).
- A could, in principle, lie on the perpendicular BE; it can't, since then the two angles would be equal.
- BE must be drawn on A's side of CD; the figure decides it, and I.11's statement lets us choose.
- "The angle DBA is equal to the two angles DBE, EBA" needs BE within DBA, a triple-incidence argument (`Prop13.within`).

## I.14
- Euclid's figure has BE within the angle ABD; the other case, BD within ABE, needs handling too (`onRay_of_angle_eq`).
- E and D lie on the same side of AB, each being on the other side from C (`OppositeSidesOf.of_between`, `OppositeSidesOf.sameSideOf`): the one place the hypothesis "not lying on the same side" is used, as Proclus warned.

## I.15
- The two straight lines really cross, so that each "stands on" the other before I.13 applies (`Prop15.figure`).
- "Similarly it can be proved" hides a third use of I.13.
- Heath's bracketed Porism (four angles about a point make four right angles) is also proved, as `Prop15.porism`.

## I.16
- CF falls within the angle ECD, so that "the angle ECD is greater than the angle ECF" (C.N. 5). Heath notes this fails in Riemann's closed, sphere-like geometry (vol. 1, p. 280); in Lean it comes from Pasch's rules and the two sides of a line (`Prop16.within`), and then `angle_add_of_within` and `Triangle.angle_pos`.
- BE produced must be long enough for I.3 to cut EF off it (`produce_longer`, as in I.11), which takes a circle (Post. 3) that Euclid does not draw.
- "Similarly" becomes one argument applied twice, the second time with AC produced, and I.15 finishes it.

## I.17
- "Let the angle ACB be added to each" has no bracket, and no Common Notion adds the same thing to unequals. It is the tacit law of magnitudes `add_lt_add_right` (System E §3.5). Heath points to this step as the one the rejected axiom "If equals be added to unequals" was after (vol. 1, p. 223).
- I.13 needs AC to stand on BD with A off it: D is on BC produced, and A is off BC because ABC is a triangle (`Triangle.off_line`, `Triangle.of_line`). To say so, the straight line BC is named (Post. 1) before Postulate 2 produces it.
- "Similarly" becomes one argument applied three times, to the triangles ABC, BAC and CAB.

## I.18
- "The angle ADB is equal to the angle ABD, since the side AB is equal to AD" is I.5, given without a bracket. Our I.5 also speaks of the angles under the base, so the sides are produced for it (`Prop5.base`).
- The angle DCB that I.16 gives is the triangle's angle ACB, because D lies on the ray from C through A (`angle_onRay_left`).
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
- The angle CED is the angle CEB, and BAE is BAC, because each pair of points lies on one ray (`angle_onRay_right`).

## I.22
- The circles meet. Heath: "It was early observed that Euclid assumes, without giving any reason, that the circles drawn as described will meet" when the condition holds (vol. 1, p. 293). Proclus argued it but missed the case of one circle within the other, and Simson thought no beginner so dull as not to see it. `Prop22.meet` follows Heath's own argument (vol. 1, p. 294): the circle about G has a point outside the circle about F and a point inside it, so they cut one another (System E's Intersection rule 4, `circles_meet_of_on_inside_outside`, in LeanEuclid's corrected form). Lean also needs the case Heath passes over, where the inside point is the centre F itself.
- DE is "of infinite length in the direction of E", but I.3 cuts off only from a greater finite straight line, so each cut needs room first (`Prop22.room`: I.2, then `produce_longer`). That is why I.2 is among the propositions I.22 cites.
- None of A, B, C is nothing, which I.3 needs (`Prop22.ne_zero`).
- K is taken where the circles cut one another on a chosen side of DE (System E, Intersections 8), so that I.23 can place the triangle where it wants it.

## I.23
- I.22's condition is not repeated here. The three straight lines are the sides of the triangle DCE, so I.20 supplies it, as the bracket in I.22's enunciation suggests.
- Heath: "the construction of the triangle assumed in this proposition is not exactly the construction given in I. 22" (vol. 1, p. 295). Our I.22 is stated with its corner at a given point, a side along a given ray and its third corner on a given side, which is what I.23 asks of it.
- AFG is a triangle, as I.8 needs: F is on AB and is not A, and G is off AB (`OnRay.onLine`, `SameSideOf.triangle`, `Triangle.off_line`, `Triangle.of_line`).
- D and E are taken "at random", and the choice does not matter because an angle depends only on its rays (`angle_eq_of_onRay`).
- Which ray from A, and which side of AB, the new angle takes are left to the figure. The statement settles both, as I.24, I.31 and I.42 need.

## I.24
- Euclid gives one case, F below EG. Simson added a sentence to make it the only one, and Heath leaves it out (vol. 1, p. 297). Lean takes all three: F lies within the angle EDG (`Prop24.within`), DF drawn on crosses EG at a point X (`crossbar`), and `Prop24.cases` puts F on EG, within the triangle DEG, or beyond EG. The first two are Proclus' cases (Heath, vol. 1, p. 297): the whole greater than the part (`len_lt_of_between`), and I.21, which Euclid never cites here.
- "Let DG be made equal to either of the two straight lines AC, DF" has no bracket; a circle about D lays it off (`OnRay.exists_len_eq`).
- G is on the same side of DE as F. I.23 lets us ask for that side, and `SameSideOf.of_onRay` keeps the point laid off along the arm there.
- "The angle DFG is greater than the angle EGF", and "much greater", are each the whole greater than the part, because X lies between D and F and between E and G (`angle_lt_of_between`).
- In Proclus' second case, taking the equal DF and DG away from the two sums is a law of magnitudes Euclid never states (`Magnitude.lt_of_add_lt_add_left`).

## The postulates: what the Lean uses and what Euclid cites

Each proof's own steps (`direct_axioms` in `facts.json`, which leaves out whatever
comes in through a cited proposition) set beside Heath's brackets, for I.1–I.24:

| | Used in the proof, with no bracket there | Bracketed, but not used in the proof |
|---|---|---|
| Postulate 1 | I.3, I.4, I.6–I.11, I.13–I.15, I.17–I.24 | |
| Postulate 2 | I.7, I.9, I.11, I.14, I.18–I.20, I.22, I.24 | I.2, I.5 |
| Postulate 3 | I.5, I.9, I.11, I.16, I.20, I.22, I.24 | |
| Postulate 4 | I.11–I.13 | |
| Definition 15 | I.2, I.11, I.12, I.16, I.20, I.22, I.24 | |

- **Postulate 1**: Lean must name a straight line before it can say a point is on
  it or off it, or lay a figure along it. This is a difference in bookkeeping, not
  in geometry: Euclid's "the straight line AB" names the same line implicitly.
- **Postulate 2**: a straight line produced where Euclid gives no bracket (I.14);
  the sides of I.5 produced, because our I.5 is stated with them (`Prop5.base`);
  and a straight line produced far enough for I.3 to cut from (`produce_longer`,
  `OnRay.exists_len_eq`). In I.2 the rule that a straight line through the inside of
  a circle meets it (System E, Intersections 5) does the producing, and in I.5 the
  statement hands us the produced sides, so Lean has no use for Euclid's bracket.
- **Postulate 3 and Definition 15**: circles Euclid does not draw, which keep a
  chance point near enough (`exists_between_nearer`, I.5 and I.9) or give a straight
  line room to be cut from (`produce_longer`, `OnRay.exists_len_eq`); and circles he
  does draw, but without a bracket for the circle (I.22) or for its radii (I.2,
  I.12, I.22).
- **Postulate 4**: turning Definition 10's right angles into the one magnitude `∟`
  that all right angles share.

The certificate counts everything a proof rests on, the propositions it cites
included, so a postulate can be on a proposition's certificate when its own proof
never uses it. [CERTIFICATE.md](../../CERTIFICATE.md) has the full list for each.
