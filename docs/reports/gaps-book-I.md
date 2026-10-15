# What Euclid takes for granted: Book I

A running catalogue of the steps in Book I that Euclid takes without saying why,
found by writing his proofs out in Lean. Many were noticed long ago, by Proclus,
by Savile, by Heath and others, and by everyone who has formalized Book I since:
Avigad, Dean and Mumma (System E), Beeson, Narboux and Wiedijk, the LeanEuclid
team, Hernández-Espiet and Kontorovich, and the Pistis team, whose catalogue of
52 gaps in Books I–III is the natural companion to this one. Where we know who
saw a gap first, we say so; nothing here is meant to be new except where marked.

Each entry names the Lean lemma or tacit rule that fills the gap. Lemmas named
`PropN.something` are particular to one proposition's figure and live in its file;
the others are general and live in Book Zero (`Elements/Figure/`), where any proof
may cite them.

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
  (`Prop5.chance_point`, which draws a circle about A).
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
- D, taken "at random" on AB, must be nearer A than C is, so that I.3 can be used (`Prop9.chance_point`).
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
- BE produced must be long enough for I.3 to cut EF off it (`produce_longer`, as in I.11), so Postulate 3 appears on the certificate.
- "Similarly" becomes one argument applied twice, the second time with AC produced, and I.15 finishes it.

## Postulates the Lean needs that Euclid doesn't cite

Postulate 1 appears in I.3, I.4, I.6 and I.8 because Lean must name a straight line
before it can say a point is on it or a figure is laid along it. This is a
difference in bookkeeping, not in geometry: Euclid's "the straight line AB" names the
same line implicitly.
