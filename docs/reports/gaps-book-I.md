# What Euclid takes for granted: Book I

A running catalogue of the steps in Book I that Euclid takes without saying why,
found by writing his proofs out in Lean. Many were noticed long ago, by Proclus,
by Savile, by Heath and others, and by everyone who has formalized Book I since:
Avigad, Dean and Mumma (System E), Beeson, Narboux and Wiedijk, the LeanEuclid
team, Hernández-Espiet and Kontorovich, and the Pistis team, whose catalogue of
52 gaps in Books I–III is the natural companion to this one. Where we know who
saw a gap first, we say so; nothing here is meant to be new except where marked.

Each entry names the Lean lemma or tacit rule that fills the gap.

## I.1
- The two circles cut one another. Heath: "It is a commonplace that Euclid has no
  right to assume, without premising some postulate, that the two circles will meet
  in a point C." Filled by the tacit rule `circles_meet` (System E, Intersection 5).
- C is not on AB, so ABC really is a triangle (`Prop1.figure`).

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
  C.N. 4 for straight lines (Heath, vol. 1, p. 250). `Prop4.coincide` proves it by
  Savile's argument: if B fell short of E or beyond it, the less would equal the greater.
- "AC will also coincide with DF" needs that only one ray on that side of DE makes the
  given angle (`Prop4.on_ray`).
- Heiberg's bracketed "two straight lines will enclose a space" is not needed: a
  finite straight line is fixed by its ends.
- The moved triangle keeps its area (System E, Metric 9, `area_congruent`).

## I.5
- F is taken "at random" on BD, but must be close enough to A that AE is the greater
  (`Prop5.chance_point`, which draws a circle about A).
- G lies beyond C on AE (`Prop5.beyond`).
- The angle FAG is common to both triangles, and BFC is AFC, because the points lie
  on the same rays (`Prop5.angle_along`, System E Diagram-angle 4).
- The angles ABG, ACF are made up of ABC, CBG and ACB, BCF (`Prop5.angle_add`,
  Pasch 2 and Diagram-angle 2).
- Each of AFC, AGB, FBC, GCB is a genuine triangle (`Prop5.triangle`).

## I.6
- The triangle DBC is less than the triangle ABC because D lies between A and B; Heath
  notes the tacit assumption (vol. 1, p. 256). `Prop6.less`, from Diagram-area 1 and 2
  and C.N. 5.
- DBC is a triangle, and the angle DBC is the angle ABC (`Prop6.figure`, `Prop6.angle`).
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
- C comes down on F's side of E along EF (`Prop8.coincide`).
- A comes down on the same side of EF as D, which I.7 needs; Euclid never says so.
- "The same side of this line EF" becomes "the same side of the straight line EF" by the
  uniqueness of the line through two points (`Prop8.sameSide`).

## Postulates the Lean needs that Euclid doesn't cite

Postulate 1 appears in I.3, I.4, I.6 and I.8 because Lean must name a straight line
before it can say a point is on it or a figure is laid along it. This is a
difference in bookkeeping, not in geometry: Euclid's "the straight line AB" names the
same line implicitly.
