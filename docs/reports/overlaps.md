# Overlaps: where a rule already says what Euclid proves

Stoicheia takes the rules of System E (Jeremy Avigad, Edward Dean and John Mumma, 2009) as
its axioms, and a few of them already say what Euclid later proves, or give it in a few
lines. III.2 is the clearest case. System E's Circle 2 says that between two points on or
within a circle every point is within it, and III.2 is that rule for two points on the
circle. Astra pointed this out in the [outside review](outside-review-01.md), with a
one-line proof compiled in Lean, and asked for this catalogue. We are grateful.

A reconstruction within these foundations does not establish such a rule independently.
Our III.2 follows Euclid's argument, and the proof is sound; but it rests, through III.1
and through I.5, on a rule at least as strong as its own conclusion. So it shows that
Euclid's reasoning goes through within System E, not that III.2 holds without the rule.
This catalogue shows where System E front-loads what Euclid later proves: which rule,
where it first enters the development, and how it reaches the proposition's own proof.

## The catalogue

Each row is one of three kinds:

- **States it**: the rule, read for the proposition's figure, is its statement, or says more.
- **Gives it at once**: the proposition follows from the rule in a short proof that cites
  no proposition. Any other rules in that proof only draw or name the figure.
- **Supplies a step**: inside some proof, the rule carries a step that is a proposition's
  content, or a case of it. The first column says which proposition, and in which proofs.

"First enters" names the first proposition, in Euclid's order, whose own proof uses the
rule, from `direct_axioms` in [facts.json](../../facts.json) at commit d040117. "Brought
in by" names the entries and helpers through which the rule reaches the proof, read from
Lean's proof terms. Each audit lemma is in [Audit/Overlaps.lean](../../Audit/Overlaps.lean),
its type the proposition's own, proved from the rules alone, with the axioms Lean reports
for it pinned beneath.

| Proposition | Rule(s) | Kind | First enters | Brought in by | What the Lean proof does | Audit lemma |
|---|---|---|---|---|---|---|
| I.7 | Circle 4 (`not_same_side_of_circles_meet`): two circles cut one another on opposite sides of the straight line through their centres | Gives it at once: I.7 is the rule with its two circles left undrawn | Nowhere: no proof uses it | Nothing: our I.7 does not rest on it | Euclid's argument, by I.5, with D in each of its four places (`Prop7.cases`) | `Audit.I_7`: Circle 4, with Postulates 1 and 3, Diagram-segment 3, Same side 3, Metric 3 and Generalities 2 to draw the circles and tell them apart |
| I.13, a case of it, in 16 proofs from II.1 on | Diagram-angle 3 (`adjacent_eq_of_right`): the angle beside a right angle is right | Supplies a step: I.13 makes the two angles two right angles, so the second is right | II.1 | Called directly by II.1, II.3, II.4, II.5, II.9, II.11, II.14, III.1, III.3, III.9, III.10, III.15, III.16, III.17, III.19 and III.25; 13 more rest on it through these. I.13 does not rest on it | Gives the right angles Euclid reads off his figure, as for the rectangles of II.1, where his text says nothing of them | `Audit.adjacent_eq_of_right` runs the other way: the rule, proved from I.13 |
| I.13, a consequence of it, in I.47 | Metric 5 (`angle_le_two_right`): no angle exceeds two right angles | Supplies a step: for an angle between two straight lines, I.13 gives it | I.47, its only user | `Prop47.within`, I.47's helper | Shows AD does not cross BC beyond B, where the angle ABD would exceed two right angles; the same case cites I.13 twice | None |
| I.23 | Superposition (`superposition`): a triangle can be laid down on a given ray, on a given side, keeping its sides and angles | Gives it at once: laid down at A along AB, the triangle DCE carries its angle at C to A | I.4 | I.8, which uses it, and I.20, through I.5 and I.4 | Euclid's construction: a triangle from three straight lines (I.22), and I.8 for its angle. The certificate lets only I.4 and I.8 use superposition, as System E asks | `Audit.I_23`: superposition, with Postulate 1, Generalities 1, Metric 1, Metric 4, Points 1 and Same side 3 to name the ray and the side |
| III.1's corollary, in III.1 Por. | Generalities 2 (`centre_unique`): a circle has only one centre | Supplies a step: "a proposition which, if thought necessary, may be added to III. 1 as a corollary" (Heath, vol. 2, p. 8) | III.1 Por.; among the 99, III.14 | III.1 Por. calls it itself; so do III.14, III.17, III.26, III.28, III.29 and III.36 | Makes the centre III.1 finds the given centre, so that it lies on the cutting straight line | None |
| III.2 | Circle 2 (`inside_of_between`): between two points on or within a circle, every point is within it | States it, and more: the ends may be within the circle as well as on it | I.5 and I.9, through Book Zero's `exists_between_nearer`, which takes a point "at random" near enough | III.1, which calls it itself; I.5, as `Prop5.base`; and I.16 and I.19, through I.5 and I.9 | Euclid's reductio, by I.5, I.16 and I.19, with the centre from III.1. It never calls the rule itself. Later proofs call the rule on two points of a circle where III.2 would serve (III.10, III.21 to III.23, III.25, III.30, III.32), as do two Book Zero lemmas first used in III.8 and later; III.13 cites III.2, as Euclid does | `Audit.III_2`, Astra's proof: Circle 2 alone |
| III.2, in III.1 | Circle 2 (`inside_of_between`) | Supplies a step: the middle point D of the chord AB is within the circle, "a fact which Euclid first demonstrates in III. 2", as Isaac Todhunter observes (Heath, vol. 2, p. 7) | I.5 and I.9, as above | III.1 calls it itself; I.8, I.10 and I.11, which III.1 cites, rest on it through I.5 and I.9 | Puts D within the circle, so that the straight line through D meets the circle on both sides of it (Intersections 5) | None |
| III.5 | Diagram-segment 2 (`circle_eq`): a circle is fixed by its centre and radius | Gives it at once: two circles about one centre through one point are one circle | III.5 | III.5 calls it itself, at its last step | Euclid's steps, ending with the rule: the supposed common centre makes the two circles one | `Audit.III_5`: Diagram-segment 2 alone |
| III.6 | Diagram-segment 2 (`circle_eq`), and Generalities 3 (`centre_inside`): a circle's centre is within it | Gives it at once: circles touching within are two circles through one point; circles touching without have no point within both, and a common centre would be one | Diagram-segment 2: III.5. Generalities 3: I.1 | III.6 calls both itself | As III.5, with Generalities 3 for contact without | `Audit.III_6`: the two rules alone |

The review records point here: a proposition's `[overlap]` names its rule
([review/SCHEMA.md](../../review/SCHEMA.md)).

## How the rows were found

**What the project already says.** The [gap catalogue for Book III](gaps-book-III.md)
says that Circle 2 "is III.2", in its introduction, and "is III.2 itself", under III.1,
where it also gives Generalities 2 as the corollary Heath would add to III.1. III.2's
commentary has a paragraph headed "A rule that is III.2", and III.6's names `circle_eq`
as III.5's last step. The axiom docstrings name one more of Euclid's steps: Intersection 5
is "the step Euclid takes for granted in I.1". That is a gap Euclid leaves and the rule
fills, not a proposition he proves later, and it belongs to the
[gap catalogue for Book I](gaps-book-I.md).

**Small certificates.** Four certificates cite no proposition. I.1 and I.4 are Euclid's
own beginnings, with Postulate 3 and Intersection 5, and with superposition. III.5 and
III.6 rest on six rules each, and both are rows. The certificates with fewer rules of
their own than these, I.25, I.41 and I.23 with three to five, cite propositions and carry
Euclid's arguments.

**A sweep of every rule.** We read each of the 81 tacit rules, with the postulates and
Definition 15, against the 99 statements and the three porisms. Then a mechanical screen,
[Audit/screen.py](../../Audit/screen.py), had Lean's `grind` try every statement against
every axiom alone, every family of axioms (the file that declares them) together, every
pair of the 24 rules about circles, and every pair of families: 40,698 attempts over the
99 propositions and the three porisms. It closed III.2, III.5 and III.6, and nothing
else. The screen cannot draw a figure, for `grind` works with the points and circles a
goal already names. I.7 needs two circles its statement never mentions, and I.23 a
triangle laid down, so both came from reading.

## The rows checked

For each row we looked for a proof of the proposition's statement from at most three rules.

- **III.2**: found, from one rule, Circle 2.
- **III.5**: found, from one rule, Diagram-segment 2.
- **III.6**: found, from two rules, and neither will do alone. In the ordinary plane with
  no point counted within any circle, Diagram-segment 2 still holds, while a circle then
  touches itself "without" and has the same centre as itself. Let a circle be drawn twice
  over, as two circles with one centre and one radius, and Generalities 3 still holds,
  while the two touch "within" and have one centre.
- **I.7**: not found from three. The shortest proof we found, `Audit.I_7`, uses seven:
  Circle 4 does the work, and the others draw two circles the statement never mentions and
  tell them apart. Circle 4 alone does not give I.7: where there are no circles and every
  length is nothing, it holds, having nothing to speak of, and I.7 fails for any two points
  on one side of AB.
- **I.23**: not found from three. `Audit.I_23` uses eight: superposition does the work, and
  the others name the ray and the side. Superposition alone does not give I.23: where there
  are no straight lines it holds, having nothing to speak of, and no point lies on a ray
  from A through B.
- **The steps.** For III.1, its porism and I.13 we found no proof from three rules: each
  needs a construction Euclid makes by earlier propositions, a bisection or a
  perpendicular (I.10, I.11). In the other direction, Diagram-angle 3 is a theorem of
  the remaining axioms: `Audit.adjacent_eq_of_right` proves it from I.13, and Lean's list
  of what that proof rests on does not include it.

## Near misses

- **III.10**, that a circle does not cut a circle at more points than two. Circle 4 with
  Same side 5 gives it when none of the three common points lies on the straight line
  through the centres: each pair would lie on opposite sides of that straight line, and a
  straight line has only two sides. When one of them does lie on it, the work is Euclid's.
  Circle 4 enters no proof.
- **I.4's last clause.** Metric 9 (`area_congruent`) makes the triangles equal once their
  sides and angles are. Euclid's reason there is that the triangles coincide (Common
  Notion 4), his own step in I.4, not a later proposition.
- **I.2 and I.3.** A rule that moves triangles could carry a length as well, but it needs a
  triangle to move, and neither statement gives one, so the proof is longer than "at once".
  The certificate keeps superposition to I.4 and I.8 in any case.
- **Representation and scope.** III.24's second clause follows from its angle hypothesis
  alone, and III.26 and III.27 hold without their equal circles, because of how a
  circumference is measured: a definition, not a rule. III.1 and III.25 take a centre from a hypothesis. These
  belong to the review records, under `[representation]` and `[statement]`.

## A separate workstream

Each row of the first two kinds names an assumption that contains its proposition.
Deriving those propositions, or those rules, from weaker assumptions would be a separate,
dependency-audited workstream. It would need a check that no proof rests, by any path, on
a rule containing its own conclusion; a ban on citing later propositions by name cannot
see that, as Astra observes. Diagram-angle 3, which I.13 gives back, is the one small step
taken here.

## Keeping it current

`lake build Audit` compiles the audit lemmas and checks their pinned axioms; the library is
not in the default build, and nothing imports it. If a statement or a rule changes so that
an audit lemma stops compiling, its row is out of date: the overlap may have gone, which is
good news, or moved. The first users come from facts.json, and change only when the proofs
do.
