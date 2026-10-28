# Overlaps: where a rule already says what Euclid proves

19 October 2026: eight axioms have become theorems with their names and exact types
unchanged, taking the lock from 87 axioms to 79. Their
[derivations and homes](../FORMALIZATION.md#rules-now-proved) explain what each proof
uses. The lock has also gained one rule of our own, by the owner's decision of 18 October
2026: every circle has a centre (`exists_centre`, [brief 0008](../briefs/0008-centre.md)).
The same brief restates III.5 and III.6: circles that cut one another cross, each with a
point within the other, and a circle touching another within has a point within it. The
current catalogue below distinguishes the remaining axiom overlaps from the former ones,
and gives III.5 and III.6 as restated. The earlier catalogue and its measurements follow as
history.

20 October 2026: the restricted rule of superposition also retires the construction
shortcuts for I.2, I.3 and I.23. The current table reflects both changes.

21 October 2026: 31 more axioms, proved on 19 October by the owner's decision of that
day ("Please do both. 79 is rather large with so many books in front of us."), have become
theorems, again with their names and exact types unchanged, among them
Generalities 3 and 4 (`centre_inside`, `inside_not_on`) and the rules of Diagram-segments 3
and 4 that give III.5's other short proofs (`on_circle_of_len_eq`, `len_lt_of_inside`). The
lock now holds <!-- count:axioms -->48<!-- /count --> axioms, including <!-- count:tacit-rules -->42<!-- /count --> tacit rules, `exists_centre`
among them. The current table reflects this change too.

24 October 2026: Circle 3 (`outside_of_between`), the last assumption that gave III.2 at
once, has become a theorem with its name and exact type unchanged, proved after III.2 from
its corollary `Prop2.within`, as Circle 2 now is too (#294). III.2's row has left the
current table for the former overlaps.

26 October 2026: Book Zero's lemma that a radius is not nothing, from which every positive
length comes, now takes that fact from our radius rule (`radius_ne_zero`, added by the
owner's decision of 25 October 2026), and Metric 1 and Diagram-segment 3's second half are
proved from the rule, so no proved rule of Book Zero rests on Diagram-segment 2 (#473).
III.5 and III.6 now rest on neither Diagram-segment 2 nor Circle 1. Diagram-segment 2 still
gives each at once, so their rows stay; their notes below say what changed.

26 October 2026, later: Book Zero no longer uses Circle 1 (`between_of_inside_chord`),
which was then still an assumption (#477). Generalities 2 and 4 and Intersection 4 are
proved again, from the circle's centre and our radius rule, and a new lemma,
`between_of_centre_chord`, gives Circle 1 where the point within is the centre; III.1, its
porism and III.2 use it, and rest on Circle 1 no longer. Of the 149 entries, 144 had rested
on Circle 1 and 37 then did, the first III.7: 23 propositions, no porism and 14 companions.
Through their own proofs and the proved rules beneath them, without the entries they cite,
59 had rested on it and 23 then did. Intersection 4 takes the first circle's centre from
`exists_centre`, but I.22, which used it, has that centre already and now gives it to the
lemma that carries the proof (`circles_meet_of_centre`), so I.22 rests on neither Circle 1
nor our rule, and no entry came to rest on `exists_centre` that had not: 53 did, as before,
the first III.1: 28 propositions, no porism and 25 companions. Through their own proofs and
the proved rules beneath them 46 did, where 31 had, since Generalities 4 now takes its
centre from the rule. No row leaves or joins the table; the notes on Generalities 2, 3 and
4 below say what moved.

26 October 2026, last: Circle 1 has become a theorem with its name and exact type
unchanged, proved after III.2 from its corollary `Prop2.within`, with Between 6 and
Generalities 4, beside Circle 2 and Circle 3 (#477). It never had a row here, and no row
leaves or joins the table. No entry rests on it now. Through their own proofs and the
proved rules beneath them 19 entries use it, the first III.7: 15 propositions, no porism and
4 companions; each cites III.2, which III.14, III.35 and III.36 cite for the first time.
Counting the entries they cite, 37 use it: 24 propositions, no porism and 13 companions;
III.10 reaches it through `CirclesCut.of_meet` and III.7 and III.8.
Where the point within is the centre, `Prop14.general`, `Prop15.le_diameter`,
`Prop15.nearer` and `Prop36.through_centre` take the step from Book Zero's
`between_of_centre_chord` instead, so that III.14's and III.15's companions and III.37 cite
nothing new. III.2 takes its centre from `exists_centre`, so III.14 and its companion III.14
general now rest on that rule: 55 entries do, 29 propositions, no porism and 26 companions;
through their own proofs and the proved rules beneath them 48 do, 28 propositions and 20
companions, III.11 and III.14 joining, for Generalities 4, beneath the new proof, takes its
centre from the rule.

28 October 2026 (#515): I.47 rests on Metric 5 (`angle_le_two_right`) no longer.
`Prop47.within` rules out AD crossing BC beyond B by I.13's bound for an angle of a
triangle, `BookI.Prop13.angle_lt_two_right`, proved after I.13 from I.13 and Common Notion
5; OutlineBound's own copy of that bound, in `Elements/BookI/OutlineBound.lean` and the
rule's only other user, has given way to the same theorem. No entry rests on Metric 5 now;
24 did, from I.47 on: 13 propositions, no porism and 11 companions. I.47's row has left the
current table for the former overlaps. The rule is still in the lock, used by no proof,
until its deletion is decided.

## Current axiom overlaps

| Proposition | Assumption | Kind | First enters | Audit lemma |
|---|---|---|---|---|
| [III.1](#iii1) | `exists_centre`, our rule: every circle has a centre | Supplies a step, in two places: inside the construction, a centre for the proof that D is within the circle, by III.2's argument; and, in the reductio, the supposed centre G | III.1 | None |
| [III.5](#iii5) | Diagram-segment 2 (`circle_eq`), with Generalities 4 (`inside_not_on`), a former assumption now proved (below) | Gives it at once: circles about one centre through one point coincide, and the point of one within the other would be within that circle and on it | III.10, through `CirclesCut.of_meet` | `Audit.III_5` |
| [III.6](#iii6) | Diagram-segment 2 (`circle_eq`), with Generalities 3 (`centre_inside`) and 4 (`inside_not_on`), former assumptions now proved (below) | Gives it at once: for contact within the circles would coincide, and the point of the inner within the outer would be within that circle and on it; for contact without a common centre would be within both | III.10, through `CirclesCut.of_meet` | `Audit.III_6` |

"First enters" here includes the axioms of proved rules. Until 26 October 2026 I.1
reached `circle_eq` through `centre_inside` and `len_ne_zero`; since then no proved rule
of Book Zero rests on it (#473). III.10 is the first entry to rest on it, through
`CirclesCut.of_meet`, and since 26 October 2026 no proposition's own Lean names the axiom:
the first entry whose own Lean names it is III.25's companion `BookIII.Prop25.complete`.
III.5 and III.6 do not rest on it: Book Zero's `ne_of_centre_of_on` and `len_lt_of_between`,
and for III.6 `centre_inside` as well, rest instead on our radius rule (`radius_ne_zero`),
which gives neither proposition, for it says only that a radius is something. Generalities
3 and 4 are proved rules, so they enter no certificate as assumptions.

Circle 2 and Circle 3 are no longer assumptions. Since 24 October 2026 both
are proved after III.2, in `Elements/BookIII/Prop02.lean`, from its corollary
`Prop2.within`, and with them Points 9 (`exists_point_outside_circle`) and
Intersection 2 (`line_meets_circle_of_opposite_sides`), whose proofs now take from
III.2 the step they took from Circle 3. The certificate's walk passes through proved
rules, so an entry that used any of the four would cite III.2, which no entry
before III.2 may; [facts.json](../../facts.json) records III.2 as what each of
them cites. I.12 finds X on AB between the centre C and the point D on the circle;
`InsideCircle.of_between_centre` puts X inside by comparing CX with the radius
CD, and Intersection 3 (`line_meets_circle_of_inside`), proved since 19 October
2026 in `Elements/Figure/Incidence.lean`, supplies the two crossings E and G.
Intersection 2 has no user in `Elements/`, `Staging/` or `Audit/`; its declaration in
`Elements/BookIII/Prop02.lean` is the only occurrence of its name there.

Circle 1 (`between_of_inside_chord`) is no longer an assumption either. Since 26 October
2026 it is proved after III.2 in the same file, from `Prop2.within`: the point within is
neither point of the circle, and were either of those between the other two it would be
within the circle, not on it. [facts.json](../../facts.json) records III.2 as what it
cites, so an entry before III.2 that used it would cite III.2, and the check on later
citations refuses that.

Our III.2 follows Euclid through I.5, I.16 and I.19, and neither it nor its corollaries
`Prop2.triangle`, `Prop2.oppositeSide` and `Prop2.sameSide` uses Circle 1, Circle 2 or
Circle 3, which are proved after them.

### III.5

Our III.5 follows Euclid's argument, by Definition I.15 and the order on EFG. Cutting
(`CirclesCut`) gives F on ABC and within CDG; producing EF beyond F meets CDG at G, so
EF is the less. The proof cites neither Diagram-segment 2 nor Circle 4, nor the
Diagram-segment 3 (second half) or 4 rules that give the other two short proofs. From the
second axiom retirement until 26 October 2026 it rested on Diagram-segment 2 all the same,
through the proved rules beneath Book Zero's `ne_of_centre_of_on` and `len_lt_of_between`;
those rules now rest on our radius rule instead, and III.5 does not rest on Diagram-segment
2 (above). The row says what the rules contain, separately from what our proof uses.

The row makes the circles one and contradicts F being both within and on that circle. Two
other short proofs were rows of their own until the second axiom retirement proved their
rules (below, among the former overlaps): one compares the distance to a point within with
the radius, which Definition I.15 makes equal to it; the other uses Definition I.15 to make
EF equal to EC, then Diagram-segment 3's second half to put F on CDG, though F is within it.
Each audit lemma has the restated III.5's type. III.10 called Diagram-segment 2 itself
until 26 October 2026, to identify circles with a common centre and point; it now ends by
III.5 and reaches the rule through `CirclesCut.of_meet`, which tells the two centres apart
by it, and III.23 reaches it through III.10. The first entry whose own Lean calls it is
III.25's companion `BookIII.Prop25.complete`. The first propositions to call Generalities 4 and
Diagram-segment 4 themselves are III.7 and III.17, and Diagram-segment 3's second half is
first called by II.14; all three are theorems now, and enter no certificate as
assumptions. The magnitude law `lt_irrefl` first enters at I.1 through
`Magnitude.add_self_ne`.

The earlier reading asked that the circles be different and meet at two points
(`CirclesMeet`), without the points within. For that reading any proof must use
Diagram-segment 2 or Circle 4, and Circle 4, now proved after I.7, has Diagram-segment 2
beneath it: draw each ordinary circle twice, as two objects with the same centre, radius
and points. Every other axiom still holds, but the two copies meet and share their
centre. This is a model argument checked by hand, not by Lean. It does not apply to the
restated III.5, since neither copy has a point within the other.

The bridge `CirclesCut.of_meet`, proved in `Elements/BookIII/Cutting.lean` after III.8
since 26 October 2026, shows that two different circles meeting at two points do cross.
It takes their centres from `exists_centre` and uses III.7 and III.8, with `circle_eq`.
Consequently the earlier statement of III.5 follows from the restated one with no centre
given (`Audit.III_5_today`). The bridge is separate from III.5's proof and cites later
propositions; III.10's last step cites it with III.5. Heath's combined enunciation for III.5
and III.6 concerns two different circles merely meeting (vol. 2, p. 12); Diagram-segment 2
gives that assertion at once. It is not a proposition of ours, so it has no separate row.

### III.6

For contact within, our III.6 draws FEB through a point of the inner circle within the
outer. The order of E and B, with Definition I.15, gives Euclid's contradiction, either
circle the inner. It cites neither Diagram-segment 2 nor Circle 4, and since 26 October
2026 it does not rest on Diagram-segment 2 through proved rules either (above). The
catalogue's short proof instead makes the circles one by Diagram-segment 2 and uses
Generalities 4 to contradict the point within.

Contact without ends at once in both proofs: a supposed common centre would be within
both circles (Generalities 3), which contact without forbids. Generalities 3 expresses
Definition I.15's own clause that the centre lies within the figure. It ends the case
Euclid leaves to the reader, which Heath regards as self-evident (vol. 2, p. 13).
Diagram-segment 2, the row's main rule, is not cited by our III.6. The alternative routes
through Diagram-segment 3 or 4 need four rules once contact without is included, so they
do not meet the catalogue's limit of three. Without Generalities 3 the row's other two
rules do not suffice: in the ordinary plane with no point counted within any circle they
hold, while a circle touches itself without and has the same centre as itself. This tests
the short route, not the necessity of Diagram-segment 2 for III.6; our proof does not cite
that rule.

The twin-circle argument under III.5 also applies to the earlier contact within: two
copies are different objects meeting with no point of either outside the other. The new
clause requiring a point within excludes them. The bridge `Audit.within_point`, by III.10,
recovers that point from the earlier conditions, with no centre given. It recovers the
earlier statements of III.6 and III.11 with no extra hypothesis: III.6 supposes a common
centre, and III.11 keeps the named centres that its conclusion orders.
`Audit.III_13_today` asks for no centres, and so gives the earlier III.13, which was
given them. This keeps the whole-circle reading of touching; it does not itself establish
agreement with Heath's preferred local reading at the contact, which III.13's companions
prove, for any two circles (`Prop13.circlesTouch_iff`, 25 October 2026, #126).

## Former axiom overlaps

| Former overlap | Why it is retired |
|---|---|
| I.7 and Circle 4 (`not_same_side_of_circles_meet`) | I.7, Definition I.15 and `circle_eq`, after I.7 in `Elements/BookI/Prop07.lean`. `Audit.I_7` now reaches I.7 through its own corollary, so it is circular as an independent proof of I.7. |
| I.13's right-angle case and Diagram-angle 3 (`adjacent_eq_of_right`) | I.13 and Common Notion 3, after I.13 in `Elements/BookI/Prop13.lean`. The later proofs now use that theorem: [14 proofs, each calling it itself](#i13s-rule-in-14-proofs), by the recount of 22 October 2026, after II.5 and II.14 came to prove their right angles in place. III.1, III.1 Por. and III.2 no longer reach it: III.1's helper takes the step by I.13 in its own Lean. |
| III.1's centre uniqueness and Generalities 2 (`centre_unique`) | The foundations, in `Elements/Figure/Circles.lean`: the straight line through two supposed centres, produced beyond each to the circle, would make the radius from one of them less than itself. Until 26 October 2026 the proof had both centres bisect one straight line through the circle, by Circle 1, and equal doubles have equal halves; it now uses neither Circle 1 nor any proposition (#477). III.1 Por. no longer calls it: since 19 October 2026 the porism takes the argument of Euclid's reductio from its given centre and reaches neither III.1 nor the theorem. It rested on 38 tacit rules to III.1's 39, and since 26 October 2026, when both left Circle 1, on 37 to III.1's 38 ([facts.json](../../facts.json)). III.36 is the only proposition whose own Lean calls the theorem, since III.14 no longer does (22 October 2026); [eight proofs](#iii1s-corollary) rest on it without passing through another entry, and 26 entries in all, by a walk of Lean's proof terms on 28 October 2026. |
| III.2 and Circle 2 (`inside_of_between`) | III.2 itself: Circle 2 is its corollary `Prop2.within`, after III.2 in `Elements/BookIII/Prop02.lean` (24 October 2026); from 19 October it was proved from Circle 3 in `Elements/Figure/Circles.lean`. `Audit.III_2` now reaches III.2 through its own corollary, so it is circular as an independent proof of III.2. |
| III.2 and Circle 3 (`outside_of_between`) | III.2, by `Prop2.within`, after III.2 in `Elements/BookIII/Prop02.lean` (24 October 2026): were the point beyond within the circle or on it, the point between would be within it. `Audit.III_2_outside` now reaches III.2 through its own corollary, so it is circular as an independent proof of III.2. |
| III.6's contact without and Generalities 3 (`centre_inside`) | A proof in `Elements/Figure/RuleBase.lean` (19 October 2026): a centre that were not inside its circle would have two unequal radii on one straight line. The radii are unequal because no radius is nothing (`RuleProofs.Circle.radius_ne_zero`, and `RuleProofs.Circle.length_pos` over it). Until 26 October 2026 that lemma was proved from Postulate 3, Circle 1 and Diagram-segment 2 (`circle_eq`): a point at no distance from the centre would be on the circle; it now takes the fact from our radius rule (`radius_ne_zero`), and `RuleProofs.Circle.length_pos` adds Postulate 3. Lean reports, for `centre_inside`, Definition I.15, Postulates 1 and 3 and 15 tacit rules, among them the radius rule, Intersections 4 and 5 and the rules of length and order, and neither Circle 1 nor Diagram-segment 2. `Audit.III_6` rests on that proof, and its pinned axioms are those of that proof with Diagram-segment 2, which it calls for contact within, and `exists_centre` and `between_symm`, which Generalities 4's proof adds; until 26 October 2026 that proof added Circle 1 and `exists_point` instead (#477). Contact without, there and in our III.6, does not rest on Diagram-segment 2; the remaining axiom overlap is the Diagram-segment 2 row above. |
| III.5 and Diagram-segment 4 (`len_lt_of_inside`), with Definition I.15 and a magnitude law (`lt_irrefl`) | A proof in `Elements/Figure/Incidence.lean` (19 October 2026): the straight line from the centre through the point within, produced to the circumference, makes the point's distance a part of the radius. Until 26 October 2026 that proof rested on Diagram-segment 2 through the proved rules beneath it, and so did `Audit.III_5_crossing`; they rest now on our radius rule instead, so the audit lemma gives III.5 without Diagram-segment 2, by a proved rule, not an assumption. The remaining axiom overlap is the Diagram-segment 2 row above. |
| III.5 and Diagram-segment 3's second half (`on_circle_of_len_eq`), with Definition I.15 and Generalities 4 (`inside_not_on`) | Proofs in `Elements/Figure/RuleBase.lean` (19 October 2026). Until 26 October 2026 the circle drawn about the centre through the point was the given circle by Diagram-segment 2, which put the point on it; since then Diagram-segment 3's half compares lengths along the straight line from the centre through the point, produced to the circle beyond a point within (Intersections 5) or meeting it before a point without (Intersections 4), with our radius rule. Generalities 4 takes the circle's centre (`exists_centre`): a point within, were it on the circle, would not be the centre, by our radius rule, and the straight line from the centre through it, produced beyond it to the circle, would make the radius there the radius to the point and something more. Until 26 October 2026 Circle 1 gave that step instead, putting the point between itself and a crossing (#477). So `Audit.III_5_radius` rests on neither Circle 1 nor Diagram-segment 2, and on `exists_centre`; the remaining axiom overlap is the Diagram-segment 2 row above. |
| I.2, I.3 and I.23 and existential superposition | The restricted rule exports only an equality about the given figure. The three former audit lemmas returned placed corners, which no exported formula can name, and have been removed. |
| I.13's bound in I.47 and Metric 5 (`angle_le_two_right`) | I.13 and Common Notion 5, after I.13 in `Elements/BookI/Prop13.lean` (28 October 2026): `Prop13.angle_lt_two_right` produces BA beyond A, and the angle beside the triangle's angle at A, which with it makes two right angles by I.13, is greater than nothing. `Prop47.within` and `Elements/BookI/OutlineBound.lean` use that theorem, and no entry rests on Metric 5. |

`Audit.inside_of_between` and `Audit.outside_of_between`, which derive each of Circle 2
and Circle 3 from the other, now reach III.2 through the other rule, so neither is
independent of III.2. Circle 4 also uses
Diagram-segment 2, so the old alternative between those two assumptions in the
III.5 and III.6 discussion below now leaves Diagram-segment 2 as the retained axiom.
The duplicate-circle argument there remains an informal model argument, not a Lean
independence theorem.

I.2 and I.3 do not rest on superposition: they follow Euclid's constructions. I.23
constructs its points through I.22 and obtains its angle equality from I.8. It still
inherits the restricted rule through I.8 and I.20, which supplies the triangle
inequalities; this inherited dependency does not restore the construction shortcut.

From the second axiom retirement until 26 October 2026 the crossing proof
`Audit.III_5_crossing` rested on `circle_eq` too, through the proved `len_lt_of_inside`,
and `Audit.III_5_radius` through the proved `on_circle_of_len_eq`. Since Book Zero came to
rest on our radius rule (#473), neither does: each proves the restated III.5 without that
axiom, as the historical account below describes for the crossing proof, through proved
rules that rest on the radius rule.

### I.13's rule in 14 proofs

Recounted on 22 October 2026, on that day's merged revision `7a55a929`, which held 137
certificate entries (99 propositions, three porisms and 35 companions), after III.1 came to
take its step by I.13 in its own Lean
([issue #168](https://github.com/jackChallis/stoicheia/issues/168)) and II.5 and II.14 came
to prove their right angles in place: the theorem occurs in 14 proofs without passing
through another certified entry, and all 14 call it in their own declarations or their
proposition's helpers. III.1, its porism and III.19 have left the count since 21 October,
and so have II.5, II.14 and II.14's companion `BookII.Prop14.rectangle`; no entry has
joined it. At `84a78856`, with 140 certificate entries (99 propositions, three porisms and
38 companions), a search of the Lean sources still finds the theorem called in these 14
proofs and no others, and the citation closure in `facts.json` still gives 33 entries,
without a new walk of Lean's declarations. On 28 October 2026, at `20d14b0a`, with 149
certificate entries (99 propositions, three porisms and 47 companions), a walk of Lean's
proof terms finds the theorem in the same 14 proofs and no others, and in 44 entries in
all. Eleven have joined the closure since `84a78856`: III.24, which came to cite III.10
when it took Euclid's reductio (#547), and through it III.26 to III.30 and III.30's halves,
`BookIII.Prop30.halves`; and III.18's four companions, `BookIII.Prop18.acute`,
`BookIII.Prop18.contact_locallyEqual`, `BookIII.Prop18.contact_lt` and
`BookIII.Prop18.semicircle_gt`, through III.16 and its companion `BookIII.Prop16.acute`.

On 21 October, three counts, across 130 entries, 136 and 137, found 20 proofs, 19 of them
calling the theorem themselves: these 14; II.5, II.14 and `BookII.Prop14.rectangle`; III.1
and its porism, which called it in III.1's helper `BookIII.Prop1.perpendicular`; and III.19,
which reached it only through that helper. The count of 20 October, across the 122 entries
there were then, found 19 and 18. Of the eight companions that joined between the 122 and
the 130 (III.16's three, III.23's, III.24's two and III.31's two), one added to each count:
`BookIII.Prop31.less`, which reaches the theorem through its own step
`BookIII.Prop31.less_lt_right`. The other seven then reached it only through entries they
cite. None of the seven companions that joined after the 130 added to either count. Six
then reached the theorem only through entries they cite: `BookIII.Prop14.general` through
III.14, `BookIII.Prop15.nearer` through III.15, `BookIII.Prop25.complete` through III.9,
`BookIII.Prop25.kind` through III.2, III.21 and III.22, `BookIII.Prop25.of_circle` through
III.2, III.25 and `BookIII.Prop25.complete`, and III.30's halves, `BookIII.Prop30.halves`,
through III.2, III.21, III.22 and III.28. The seventh, `BookIII.Prop15.le_diameter`, cites
only I.20 and does not reach it.

All 14 proofs call Diagram-angle 3 (`adjacent_eq_of_right`) themselves: II.1 and its
companion `BookII.Prop1.two`, II.3, II.4, II.9, II.11, III.3, III.10, III.15, III.16, III.17
and III.25 in their own Lean, III.10 also in its helper `BookIII.Prop10.right_on_line` and
III.15 in its helper `BookIII.Prop15.perp`; III.9 in its helper `BookIII.Prop9.apart`; and
III.31's companion `BookIII.Prop31.less` in its helper `BookIII.Prop31.less_lt_right`.
III.1's helper `BookIII.Prop1.perpendicular`, which shows that at a point of a straight line
only one straight line is at right angles to it, no longer calls the rule. Where it
produces a straight line through the foot of a right angle, the two angles there together
make two right angles (I.13), and taking the given right angle away leaves the other right
(Common Notion 3): the theorem's own proof, written out in place. So III.1, its porism and
III.19, which use that helper, do not reach the rule through it; III.16, which uses it too,
still calls the rule itself. II.5 no longer calls it either: it proves the right angle HDA
by I.13 and Common Notion 3 in its own Lean. Nor do II.14 and its companion
`BookII.Prop14.rectangle`, which prove the right angle HEG (it is the angle HEB) in the same
way and cite II.5; so neither they nor II.14's other seven companions rest on the rule at
all. Thirty more entries (fifteen propositions, III.16's porism and fourteen companions)
rest on it through these 14. I.13 does not rest on it. The rule gives the right angles
Euclid reads off his figure, as for the rectangles of II.1, where his text says nothing of
them. These 14 are not the 17 of the historical census below, which counted propositions
and porisms on the earlier foundations, II.5 and II.14 among them.

The full dependency closure contains the theorem in 44 entries: 27 propositions, one
porism (III.16's) and 16 companions. The 30 additional entries above reach it only through
entries they cite. Before III.1's change it held 67 on the 137 entries: 40 propositions,
two porisms and 25 companions. The 26 that left with that change are III.1, its porism and
III.19, and 23 entries that reached the theorem only through them: III.2, III.7, III.8,
III.11, III.13, III.21, III.22, III.24 and III.26 to III.32, and eight companions,
`BookIII.Prop7.general`, `BookIII.Prop8.general`, `BookIII.Prop23.point`,
`BookIII.Prop24.equalCircles`, `BookIII.Prop24.equalMeasure`, `BookIII.Prop25.kind`,
`BookIII.Prop30.halves` and `BookIII.Prop31.greater`. The eight that left when II.5 and
II.14 changed are II.5, II.14 and II.14's six companions. These are uses of a proved rule,
not axiom overlaps.

The recount walks Lean's elaborated declarations using the same type, value and
constructor references as `Certificate/Facts.lean`. For the 14, it stops at another
certificate entry or a Common Notion; a second walk, which also stops at a shared lemma
outside the proposition's namespace while following Lean's auxiliary declarations, finds
the same 14 calling it themselves. For the 44, it follows every project declaration. Each
walk counts an entry once when it reaches `Tacit.adjacent_eq_of_right`, before following
that theorem's proof. Since the theorem's proof cites I.13, `facts.json` records I.13 among
the citations of each of the 14; the first walk, stopping at the theorem, finds every
entry's citations as `facts.json` gives them, save I.13 for 13 of these 14. III.16 keeps
I.13 even so, through the I.13 step of `BookIII.Prop1.perpendicular`, which it uses. The 44
are exactly the 14 with every entry whose citations in `facts.json` lead to one of them.
On 22 October 2026 the same walks, run on the second axiom retirement's revision (31 more
rules proved), which had II.5's and II.14's change but not yet III.1's, gave 17, 16 and 53,
of the same kinds, as on the 130 entries before the retirement: the retirement added no use
of the theorem. Searching the Lean sources for the rule's name confirms the calls
listed above; in `Elements/BookIII/Prop16.lean` two shared lemmas call it too,
`Segment.exists_tangent` and `Segment.angle_tangent_of_oppositeSidesOf`, which serve only
`Segment.compare_alike`, a lemma no certificate entry uses. The retired name is absent from
every axiom list; those lists alone cannot count uses of the theorem.

## Historical account, before 19 October 2026

The account below preserves the earlier readings, attributed findings and measured
counts. Its axiom statuses, first users and statements about current dependencies
are superseded by the dated catalogue above. In particular, the former seven-axiom
I.7 shortcut and the 17-proof right-angle census describe the earlier foundations, and
the notes on III.5 and III.6 describe those propositions as they were stated before brief
0008 restated them ([III.5](#iii5) and [III.6](#iii6) above give them as they are now).
The later notes under I.2/I.3 and I.23 are dated updates about the retired construction
shortcuts, and the second and third paragraphs under III.1's corollary are dated updates
about the rule's first user; their old rows remain here as history.

Stoicheia takes the rules of System E (Jeremy Avigad, Edward Dean and John Mumma, 2009) as
its axioms, and a few of them already say what Euclid later proves, or give it in a few
lines. III.2 is the clearest case. System E's Circle 2 says that between two points on or
within a circle every point is within it, and III.2 is that rule for two points on the
circle. Astra pointed this out in the [outside review](outside-review-01.md), with a
one-line proof compiled in Lean, and asked for this catalogue. We are grateful. Two later
readings added to it, and we thank them too: a cold review by Claude saw that
the former existential superposition rule supplied the steps of I.2 and I.3, and Argon's
second review corrected our account of how each rule enters the proofs (the certificate counted a rule a proof reaches
through a lemma as one it calls itself, and now keeps the two apart), found defined words
that our screen left folded, and saw that III.30 belongs among the near misses.

One rule in the catalogue is our own: `exists_centre`, from Definitions I.15 and I.16.
In III.1 it supplies a centre for the proof that the middle point D is within the circle.

A reconstruction that rests on such a rule does not establish the rule independently: it
shows that Euclid's reasoning goes through within our foundations, not that the proposition holds
without the rule. Our III.2 follows Euclid's argument, and it once rested so, through
III.1, on a rule at least as strong as its own conclusion; III.1 now takes that step by
Euclid's own argument for III.2, and no proposition rests on the rule. This catalogue
shows where our foundations give early what Euclid later proves: which rule, where it first
enters the development, and how it reaches the proposition's own proof.

### The catalogue

The eleven historical rows are of three kinds:

- **States it**: the rule, read for the proposition's figure, is its statement, or says more.
- **Gives it at once**: the proposition follows from the rule in a short proof, from at
  most three rules, that cites no proposition. Any other rules in that proof only draw or
  name the figure.
- **Supplies a step**: inside some proof, the rule carries a step that is a proposition's
  content, or a case of it. The first column says which proposition, and in which proofs.
  For I.7 the proof is the audit lemma: Circle 4 carries the proposition's content,
  but the shortest proof we found from the rules alone takes seven of them, the rest
  drawing two circles the statement never mentions and telling them apart, which is more
  than "at once".

"First enters" names the first proposition, in Euclid's order, whose proof uses the rule
without taking it from a proposition it cites. It is read from
[facts.json](../../facts.json) as committed, which keeps the two ways apart
([Certificate/FIELDS.md](../../Certificate/FIELDS.md);
[issue #65](https://github.com/jackChallis/stoicheia/issues/65)): `own_axioms` lists the
rules a proof calls itself, those its own Lean or a helper written for its proposition
(`Prop47.within`, for I.47) names, and `inherited` the rules its own Lean does not name
but reaches through a lemma it calls, of Book Zero (`Elements/Figure/`) or a shared step,
each with the lemma that brings it in. A proposition it cites may rest on such a rule too.
A first user may call the rule itself or inherit it through a shared lemma; the notes
below name those lemmas. A later proof may rest on a rule it
never calls, as III.26 rests on Generalities 2 only through Book Zero's
`EqualCircles.radii`; III.28 and III.29 call that lemma too, and rest on the rule through
III.26 and III.27 as well, which they cite. The note under the table names the lemma the
rule comes through. Each proposition's page marks the same in its list of tacit rules:
"(used here)" for a rule its own Lean calls, and the lemmas for one it inherits.

The audit lemmas were in [Audit/Overlaps.lean](../../Audit/Overlaps.lean), each type the
proposition's own, proved from the rules alone, with the axioms Lean reports for it
pinned beneath. The three construction lemmas have since been removed; the current
catalogue above identifies the surviving overlaps. Under this historical table, each row
has a short note: the proofs that call the rule
themselves, the lemmas and entries through which it reaches the others, and what the Lean
proof does. The notes are read from Lean's proof terms; a search of `Elements/` for the
rule's Lean name finds the same calls.

| Proposition | Rule(s) | Kind | First enters | Audit lemma |
|---|---|---|---|---|
| I.2 ([details](#i2-and-i3)) | Superposition (`superposition`): a triangle can be laid down on a given ray, on a given side, keeping its sides and angles | Supplies a step, in Audit.I_2: laid down at A along AB, a triangle on BC carries the length of BC to A, and drawing that triangle and a point off AB takes nine axioms more | I.4 | Audit.I_2 |
| I.3 ([details](#i2-and-i3)) | Superposition (`superposition`) | Supplies a step, in Audit.I_3: laid down at A along the ray AB, a triangle on the less straight line carries its length onto the ray, and drawing the figure and placing the new point between A and B takes twenty-one axioms more | I.4 | Audit.I_3 |
| I.7 ([details](#i7)) | Circle 4 (`not_same_side_of_circles_meet`): two circles cut one another on opposite sides of the straight line through their centres | Supplies a step, in `Audit.I_7`: I.7 is the rule with its two circles left undrawn, and drawing them and telling them apart takes six rules more | Nowhere: no proof uses it | `Audit.I_7` |
| I.13, a case of it, in 17 proofs from II.1 on ([details](#i13-in-17-proofs)) | Diagram-angle 3 (`adjacent_eq_of_right`): the angle beside a right angle is right | Supplies a step: I.13 makes the two angles two right angles, so the second is right | II.1 | `Audit.adjacent_eq_of_right` runs the other way: the rule, proved from I.13 |
| I.13, a consequence of it, in I.47 ([details](#i13-in-i47)) | Metric 5 (`angle_le_two_right`): no angle exceeds two right angles | Supplies a step: for an angle between two straight lines, I.13 gives it | I.47, its only user | None |
| I.23 ([details](#i23)) | Superposition (`superposition`): a triangle can be laid down on a given ray, on a given side, keeping its sides and angles | Supplies a step, in Audit.I_23: laid down at A along AB, the triangle DCE carries its angle at C to A, and naming the ray and the side takes seven axioms more | I.4 | Audit.I_23 |
| III.1's corollary, in III.1 Por. ([details](#iii1s-corollary)) | Generalities 2 (`centre_unique`): a circle has only one centre | Supplies a step: "a proposition which, if thought necessary, may be added to III. 1 as a corollary" (Heath, vol. 2, p. 8) | III.1's porism; of the propositions themselves, III.14 | None |
| III.2 ([details](#iii2)) | Circle 2 (`inside_of_between`): between two points on or within a circle, every point is within it | States it, and more: the ends may be within the circle as well as on it | Nowhere: no proposition rests on it | `Audit.III_2`, Astra's proof: Circle 2 alone |
| III.2 ([details](#iii2)) | Circle 3 (`outside_of_between`): a straight line that has left a circle does not come back; Circle 2 turned round | Gives it at once: were a point between two points of the circle not within it, the second point would be outside the circle, not on it | Nowhere: no proposition rests on it | `Audit.III_2_outside`: Circle 3 alone |
| III.5 ([details](#iii5-1)) | Diagram-segment 2 (`circle_eq`): a circle is fixed by its centre and radius | Gives it at once: two circles about one centre through one point are one circle | III.5 | `Audit.III_5`: Diagram-segment 2 alone |
| III.6 ([details](#iii6-1)) | Diagram-segment 2 (`circle_eq`), and Generalities 3 (`centre_inside`): a circle's centre is within it | Gives it at once: circles touching within are two circles through one point; circles touching without have no point within both, and a common centre would be one | Diagram-segment 2: III.5. Generalities 3: I.1 | `Audit.III_6`: the two rules alone |

The review records pointed here: a proposition's `[overlap]` named its rule
([review/SCHEMA.md](../../review/SCHEMA.md)).

#### Row by row

##### I.2 and I.3

Our I.2 and I.3 do not rest on superposition. The proofs are Euclid's: I.2 by the
equilateral triangle of I.1 and two circles, I.3 by I.2 and a circle. Our Postulate 3 is
Euclid's collapsing compass, and leaves carrying a distance to I.2.

20 October 2026 update: these two overlap rows are retired. Under the former existential superposition rule,
Audit.I_2 and Audit.I_3 drew a triangle, laid it down and returned one of its placed
corners. The restricted rule permits hypothetical placement within a derivation over
symbols and exports only an equality of lengths, angles or triangles about the given
figure. No exported formula names a placed corner, and no derivation step constructs
anything. The two audit lemmas that returned such corners are retired with their rows.

##### I.7

Nothing brings the rule into our I.7, which does not rest on it. The proof is Euclid's
argument, by I.5, with D in each of its four places (`Prop7.cases`). `Audit.I_7` uses
Circle 4, with Postulates 1 and 3, Diagram-segment 3, Same side 3, Metric 3 and
Generalities 2 to draw the circles and tell them apart.

##### I.13 in 17 proofs

Among propositions and porisms, sixteen of the 17 proofs call the rule themselves: II.1, II.3, II.4, II.5, II.9, II.11,
II.14, III.3, III.10, III.15, III.16, III.17 and III.25 in their own Lean; III.9 in its
helper `Prop9.apart`; and III.1 and its porism in III.1's helper `Prop1.perpendicular`,
which shows that at a point of a straight line only one straight line is at right angles
to it. III.19 reaches the rule only through `Prop1.perpendicular`, which III.16 uses as
well as calling the rule itself. Twenty-five more entries (24 propositions and III.16's
porism) rest on it through these 17. I.13 does not rest on it. The rule gives the right
angles Euclid reads off his figure, as for the rectangles of II.1, where his text says
nothing of them.

21 October 2026 update: III.1 and its porism no longer call the rule, now a theorem.
`Prop1.perpendicular` takes its step by I.13 and Common Notion 3 in its own Lean, so
neither they nor III.19 reach the rule through it, and III.2 no longer rests on it through
III.1. The current census, [I.13's rule in 14 proofs](#i13s-rule-in-14-proofs) above,
counts a different 14: the 12 propositions left here once III.1, its porism and III.19
are taken out, and II.5 and II.14, which now prove their right angles in place, with them;
and two companions.

##### I.13 in I.47

The rule comes in through `Prop47.within`, I.47's helper. It shows that AD does not cross
BC beyond B, where the angle ABD would exceed two right angles; the same case cites I.13
twice.

##### I.23

20 October 2026 update: our proof keeps Euclid's construction. I.22 constructs F and G from three lengths,
I.20 supplies the triangle inequalities, and I.8 proves the angle equality. It rests on
superposition through I.8 and I.20: I.8 calls the restricted rule itself, while I.20
rests on it through I.5 and I.4. Only I.4 and I.8 may call it directly.

The former overlap row and its lemma Audit.I_23 are retired. That lemma used the
existential rule to lay down the triangle DCE and return its placed corners. The
[restricted rule](../../Elements/Foundations/Tacit/Superposition.lean) is an inference
in System E's style: a represented derivation returns an equality about the given figure,
and cannot return its hypothetical corners as constructed points. This is a restriction
on those derivations, not a claim that the whole foundation cannot recover a placement.
I.22 and I.23 legitimately construct congruent figures by Euclid's route. Equivalence
with System E's two printed rules is not claimed.

##### III.1

The construction receives a circle and two points A, B of it, with no centre supplied.
It bisects AB at D, draws DC at right angles and through to E, and bisects CE at F.
Within the construction, only the proof that D is within takes a centre from
`exists_centre`, through
`Prop1.within` and III.2's argument; that witness supplies none of the constructed points.
III.1 takes G for its reductio from `exists_centre`. The rule gives bare
existence; the construction and the proof that F is the centre are III.1's work.

##### III.1's corollary

Heath calls uniqueness "a proposition which, if thought necessary, may be added to
III. 1 as a corollary" (vol. 2, p. 8). III.1's porism calls the rule itself: it makes the
centre III.1 finds the given centre, so that it lies on the cutting straight line. III.14,
III.17 and III.36 call it themselves for the same step, making the centre III.1 finds the
centre their statements speak of. III.26 reaches it only through Book Zero's
`EqualCircles.radii`, that equal circles have equal radii: a circle has only one centre,
so the centres the definition of equal circles names are the given ones. III.28 and III.29
call that lemma too, and rest on the rule through III.26 and III.27 as well, which they
cite.

21 October 2026 update: the porism no longer calls the rule, which now first enters at
III.14. Our porism proves that the given centre lies on the cutting straight line by the
argument of Euclid's reductio: on AB it is D; off AB, the equal adjacent angles put it on
DC. It neither calls III.1 nor uses `centre_unique` or `exists_centre`, and rests on 51
tacit rules to III.1's 56. Two proofs call `centre_unique` themselves: III.14, to identify
the centre III.1 finds with the centre E its statement names, and III.36, to show that the
centre E it takes from `exists_centre` is off AC when DCA is not through the centre.
III.17 now obtains its centre by `Prop1.of_circle` and has no such identification step.
III.26 reaches it only through Book Zero's `EqualCircles.radii`, that equal circles have
equal radii: a circle has only one centre, so the centres the definition of equal circles
names are the given ones. III.28 and III.29 call that lemma too, and rest on the rule
through III.26 and III.27 as well, which they cite. These five, III.14, III.26, III.28,
III.29 and III.36, now use the rule. Seven more entries rest on the rule only through
entries they cite: III.15 through III.14, III.27 through III.26, III.30 through III.28,
III.37 through III.36, and the companions `Prop14.general` through III.14, `Prop15.nearer`
through III.15 and `Prop30.halves` through III.28. Walking Lean's proof terms on 21
October 2026, as for I.13's rule above, finds the theorem in these twelve entries and in
no other, none of them before III.14. Searching `Elements/` for the rule's name confirms
the two calls, and finds three lemmas that call it: Book Zero's `EqualCircles.radii` and
`Centre.every`, and `Arc.eq_of_aligned` in `Elements/BookIII/Squares.lean`. No certificate
entry uses either of the last two. [Former axiom overlaps](#former-axiom-overlaps) gives
the rule as it is now.

22 October 2026 update (#131): III.14 no longer calls III.1 or the rule, for its
statement names the centre E, and III.17 takes its centre from `exists_centre` in place of
`Prop1.of_circle`, by the coordinator's
[decision of that day](../decisions/2026-10-22-iii1-calls-dropped.md) to drop the calls of
III.1 that do no work. So III.36 is now the only proof that calls `centre_unique` itself,
and the rule first enters at III.26. Four proofs use it, III.26, III.28 and III.29
through `EqualCircles.radii` and III.36 itself, and four more entries rest on it only
through entries they cite: III.27 through III.26, III.30 and `Prop30.halves` through
III.28, and III.37 through III.36. III.15, `Prop14.general` and `Prop15.nearer` have
left with III.14. Walking Lean's proof terms on 22 October 2026 finds the theorem in these
eight entries and in no other, and searching `Elements/` for the rule's name finds the one
call, III.36's, beside the three lemmas above.

26 October 2026 update (#547): III.17 again obtains its centre by `Prop1.of_circle`, as
III.4 and III.8 now do, by the coordinator's
[decision of that day](../decisions/2026-10-26-centre-by-iii1.md). None of them calls
`centre_unique`, and a walk of Lean's proof terms on 26 October 2026 finds that none of
them, nor their companions, reaches it.

28 October 2026 update (#584): the rule now first enters at III.10. A walk of Lean's proof
terms on 28 October 2026, at `20d14b0a`, finds eight proofs that rest on it without
passing through another entry, where the walk of 22 October found four. III.26, III.28 and
III.29 reach it through `EqualCircles.radii` and III.36 calls it itself, as before. III.10
reaches it through `CirclesCut.cut_point`, by way of `CirclesCut.of_meet`, in
`Elements/BookIII/Cutting.lean`, since it came to end by III.5 (#475, #547). III.20 and
its companion `BookIII.Prop20.special` reach it through III.20's helper
`angleAtCentre.diameter`, which identifies the centre Lean's choice took with the given
centre, since the angle at the centre of any size moved into `Elements/` (#129); III.27
reaches it through the same helper since it came to take Euclid's halving in every case
(#511). Eighteen more entries rest on it only through entries they cite, 26 in all: III.21
to III.24, III.30 to III.34 and III.37, and the companions `BookIII.Prop20.circumference`,
`BookIII.Prop23.point`, `BookIII.Prop24.equalCircles`, `BookIII.Prop24.equalMeasure`,
`BookIII.Prop25.kind`, `BookIII.Prop30.halves`, `BookIII.Prop31.greater` and
`BookIII.Prop31.less`. The walk agrees with the proved rules `facts.json` lists for each
entry. Searching `Elements/` for the rule's name finds III.36's call, the three lemmas
above, `CirclesCut.cut_point` and `angleAtCentre.diameter`.

##### III.2

Two rules contain III.2, and no proposition rests on either. Circle 2 says it outright, and more,
for its ends may be within the circle as well as on it. Circle 3, that a straight line
that has left a circle does not come back, is Circle 2 turned round: each proves the other
in a line (`Audit.inside_of_between`, `Audit.outside_of_between`), and Circle 3 gives
III.2 at once (`Audit.III_2_outside`). No proposition of Book I rests on either: I.5 and
I.9 take a point "at random" with Book Zero's `exists_between_nearer`, which keeps the
point near enough by the order of the points on the straight line and the adding of
lengths, not by a rule about circles.

Our III.2 is Euclid's reductio, by I.5, I.16 and I.19, with its centre from
`exists_centre`, where Heath's reference is III.1, and it rests on neither rule. Circle 2
used to reach it through III.1, which called the rule to put D, the middle point of AB,
within the circle, so that the straight line drawn through D at right angles to AB meets
the circle on both sides of it: "a fact which Euclid first
demonstrates in III. 2", as Isaac Todhunter observes (Heath, vol. 2, p. 7). III.1's
helper `Prop1.within` proves it by III.2's own argument, from a centre that III.1's
construction takes from `exists_centre` and passes to the helper: on AB that centre is
D itself, and off it I.5, I.16 and I.19 make D nearer the centre than the circumference. II.14, once the first proof to call the rule, needs E, between
B and F, the ends of the diameter of the semicircle BHF, within the circle, so that DE
produced meets it at H, a step Euclid takes without saying why
([gaps in Book II](gaps-book-II.md#ii14)). G, the centre, falls between B and E, so E lies
between the centre and F, and Book Zero's `InsideCircle.of_between_centre` puts it within,
by Definition I.15 and the rules that relate "within" to the radius, with no proposition.

The later proofs that called Circle 2 take the step in one of three ways. Where both ends
are on the circle, III.2's own case, they cite III.2: III.15, III.21, III.22,
III.23 and its companion `Prop23.point`, III.25's companion `Prop25.of_circle` in the
meeting fact `Prop25.meets`, III.30, and III.32 in its helper `Prop32.sameSide`. Where one end is the centre and the other is on the circle, they use
`InsideCircle.of_between_centre`: III.7, III.8, III.12, III.15, III.17, III.20, III.34 and
III.37. III.15 also has L between the centre and the point K within the circle;
`InsideCircle.of_between_centre_of_inside` uses the given point F of the circle to put L
within. Where an end is within the circle and is not its centre, they cite III.2's
corollary `Prop2.within`, III.2 for ends on or within the circle, whose proof produces the
straight line to meet the circle and finds the point between the two points where it meets
it: III.7, III.11, III.15 and III.23. III.13 cites III.2, where Heath's reference is
III.2. III.10 once cited III.2 too, to put K and L within the circle before carrying its
perpendiculars through it; it now produces them by Postulate 2 and needs no point within.

Three more corollaries after III.2 take the place of Book Zero lemmas that rested on
Circle 2: `Prop2.triangle`, that three points of a circle are not on one straight line,
first used in III.8; and `Prop2.oppositeSide` and `Prop2.sameSide`, that a straight line
in a circle has points of the circle on either side of it, first used in the shared
steps of `Circumferences.lean`, which III.24's companions are the first to cite. Stage
3's ground had two more lemmas that called Circle 2, and both now come after III.2.
That a point of the straight line through two points of a circle is on the circle
exactly when it is one of them, and within it exactly when it lies between them, is
`Prop24.chord_cases`, before III.24, by III.2 and `Prop2.triangle`. That a straight
line drawn from within the base of a segment meets its circumference is `Prop25.meets`,
proved by III.2 beside III.25, whose companion `Prop25.of_circle` uses it; III.25's
construction is given the fact, and never sees a circle. Book Zero kept its own three,
Triangle.of_onCircle, exists_onCircle_oppositeSidesOf and exists_onCircle_sameSideOf,
stated for a circle with no centre given, which nothing used, until they were taken
out on 24 October 2026 (#294; [below](#a-separate-piece-of-work)). `Staging/Routes/`
is gone, for the last of its theorems, #129's, have left it for `Elements/`; they rest on
neither Circle 2 nor Circle 3
([checked in the routes report](routes-book-III.md#checks)), and therefore reach none of
those three Book Zero lemmas, as the theorems that left it before do not. The staged
III.1's construction called Circle 2 to put D
within the circle until 19 October 2026, when it moved into `Elements/BookIII/Prop01.lean`
as `Prop1.construction`, which takes that step by `Prop1.within`; `Staging/Centre/`, which
held it, was retired later that day. Since `Prop2.within` is Circle 2 with no supplied
centre, proved from the other rules, Circle 2 and Circle 3 tell us nothing about any
circle that the rest of our foundations do not.

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

**19 October 2026, screen rerun after step 6.** With `Tacit.exists_centre` added to the
rules about circles that `Audit/screen.py` tries in pairs, the screen ran against fresh
certificates at b260c826: 57,240 attempts over 135 statements, eleven closings, all on
III.2, III.5 and III.6. No pair containing `Tacit.exists_centre` closed; but `grind`
refuses that rule, so every attempt that included it searched with none of its rules, and
the run says nothing of the rule. The full result and its comparison with the earlier
runs follow below. The proposed statement of III.30's congruent halves, then staged for the
owner's approval, had no proof or certificate entry, and supplied no overlap evidence. The
owner approved it on 20 October 2026; it is now proved as the companion "III.30 halves",
and no run of the screen yet includes it.

**What the project already says.** The [gap catalogue for Book III](gaps-book-III.md) said
that Circle 2 "already contains III.2", in its introduction and under III.1, where it also
gave Generalities 2 as the corollary Heath would add to III.1. III.2's commentary explains
how Circle 2 and Circle 3 give III.2; III.5's and III.6's explain how the point within
supplies the straight line and the order of its points; and III.10's tells how its last step
reaches III.5 through `CirclesCut.of_meet`, which tells the two centres apart by `circle_eq`. The axiom docstrings name one
more of Euclid's steps: Intersection 5 is "the step Euclid takes for granted in I.1". That
is a gap Euclid leaves and the rule fills, not a proposition he proves later, and it
belongs to the [gap catalogue for Book I](gaps-book-I.md).

**Small certificates.** Four propositions cite no proposition: I.1 and I.4, Euclid's own
beginnings, which rest on Postulate 3 with Intersection 5 and on superposition; and III.5
and III.6, which are rows of the catalogue. In the restated readings, III.5 and III.6 each
rested on thirteen tacit rules, with Definition I.15 and Postulate 1; from the second axiom
retirement until 26 October 2026 each rested on 18, with Definition I.15 and Postulates 1
and 3, for the proved rules beneath their Book Zero lemmas bring in their own; since then
III.5 rests on 12 and III.6 on 16, our radius rule among them, with Definition I.15 and
Postulates 1 and 3. The line through the point within
and the order of its points carry Euclid's comparison, with Common Notion 5 through
`len_lt_of_between`. Three others, I.25, I.23 and I.19, have the fewest rules in
`direct_axioms`, three to seven, but each cites propositions and carries Euclid's
argument.

**A sweep of every rule.** We read each of the 81 tacit rules, with the postulates and
Definition I.15, against the 99 statements and the three porisms, and later against the 19
companions that stages 2 and 4b brought in (I.40's, I.45's, II.1's and II.14's, and those
of III.7, III.8 and III.17), and found no more. Then a mechanical screen,
[Audit/screen.py](../../Audit/screen.py), had Lean's `grind` try every statement against
every axiom alone, every family of axioms (the file that declares them) together, every
pair of the 24 rules about circles, and every pair of families. Its first run, at
d040117, made 399 attempts per statement, 40,698 over the 99 propositions and the
three porisms (39,501 over the propositions alone), and closed III.2, III.5 and III.6,
and nothing else. But it left defined words folded, `Triangle`, `Collinear`, `circumference`
and `standing` among them, so that a statement written with them was searched only in part,
as Argon's second review pointed out; and it lost more than a quarter of its attempts
without a search, for `grind` refuses a rule in which it finds nothing to match, as it does
the twelve rules that only say a point, a straight line or a circle exists, and with it the
rest of the attempt, so that Postulates 4 and 5, for instance, were never tried with the
diagram rules.

The revised screen of `tooling/overlap-screen-unfold` (commit `760b974`) was run against
library revision `89c5da4`. The linked `Audit/screen.py` has had these behaviours on main
since #138. In the revised screen, every definition a statement or a rule
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
point of a circle across the chord from a circumference gives it the same measure: that is
III.21, a proposition, so the near misses of the measure (below) are not found by it, and
are not overlaps with a rule. Nor
does it give `grind` that a magnitude Lean chooses is one magnitude under two descriptions
that hold of the same points, as `standing_eq_circumference` and `standing_congr` show, so a
statement that needs that step is not searched either. Nor does `grind` reason by induction,
or open a figure's fields of itself, so what a figure given with its triangles holds by its
formation is not searched, which only the companions of I.45 and II.14 speak of. The revised
screen is not one of CI's checks: that run took about an hour and a half of processor time,
and nothing runs it of itself; it should be run again when a statement or a rule changes.
The restated III.5 and III.6 of brief 0008 are such a change: the screen unfolds
`CirclesCut` and `TouchesInternally` like the other definitions, but its run must be
renewed on the revision that holds them, for the earlier run does not validate the new
readings. The Diagram-segment 3 and 4 routes for III.5, rows until the second axiom
retirement, were found by reading: each takes
three rules from three families, outside the screen's pairs, and `grind` did not close
the Diagram-segment 4 route in a probe. The screen cannot draw a figure, for `grind` works
with the points and circles a goal already names.
I.7's overlap needs two circles its statement never mentions, so it came from reading.
At that revision the I.23 overlap used a triangle laid down by the existential
superposition rule. The I.2 and I.3 overlaps first drew a triangle to lay down; the
catalogue initially listed them as near misses, then as rows with audit lemmas, since
I.7 likewise drew objects absent from its statement. All three superposition rows and
their audit lemmas are now retired with that existential rule. These screening results
are historical evidence for the revisions named above, not a fresh screen of the
restricted rule.

After step 6, on 19 October, a run against fresh certificates at b260c826, on the
restated statements, added `Tacit.exists_centre` to the rules about circles. It used the
screen as it then stood on that branch, before the revision above reached it: only the
phrase definitions, `CirclesCut` among them, were unfolded, no statement was tried with
no rule, and no rule was left out. It used all 135 certificate entries, 99 propositions, three
porisms and 33 companions, and tried each statement against each of the 88 axioms alone,
each of eight families (the module that declares them), each pair of the 25 circle
rules, and each pair of families. That is 88 + 8 + 300 + 28 = 424 attempts per
statement, 57,240 in all. Its eleven closings are below. Family names are the final
components of their module names; the rule column omits the namespace, writing
`inside_not_on` for `Tacit.inside_not_on`. Each
successful attempt was also recompiled with warnings treated as errors and its axioms
printed: the listed rules, plus Lean's `propext`, `Classical.choice` and `Quot.sound`,
with no `sorryAx`.

| Statement | Attempt: family, family pair or rule pair | Rules used |
|---|---|---|
| III.2 | Diagram | `inside_not_on`, `inside_of_between` |
| III.2 | Definitions + Diagram | `inside_not_on`, `inside_of_between` |
| III.2 | Diagram + Magnitudes | `inside_not_on`, `inside_of_between` |
| III.2 | Diagram + Metric | `inside_not_on`, `inside_of_between` |
| III.2 | Diagram + Superposition | `inside_not_on`, `inside_of_between` |
| III.2 | Diagram + Transfer | `inside_not_on`, `inside_of_between` |
| III.2 | `inside_not_on` + `inside_of_between` | `inside_not_on`, `inside_of_between` |
| III.5 | Diagram + Transfer | `circle_eq`, `inside_not_on` |
| III.5 | Magnitudes + Transfer | `len_lt_of_inside`, `lt_irrefl`, `lt_trans` |
| III.5 | `inside_not_on` + `circle_eq` | `circle_eq`, `inside_not_on` |
| III.6 | Diagram + Transfer | `centre_inside`, `circle_eq`, `inside_not_on` |

No single axiom, porism, companion or other proposition closed. Of the remaining
attempts, 57,196 fell back to `sorry` and 33 timed out at the unchanged limit of 30,000
heartbeats; none counts as a closing. The result matches the eleven closings, all on
III.2, III.5 and III.6, of an earlier run of 51,600 attempts. No pair containing
`exists_centre` closed, and no closing uses it; but `grind` refuses that rule, which only
says that a centre exists, and that screen left no refused rule out, so its try alone and
every attempt with it searched with none of their rules, and the run says nothing of the
rule. The same uncatalogued candidate route
for III.5 remains: `len_lt_of_inside`, `lt_trans` and `lt_irrefl`. Cutting gives a point
of each circle within the other; about a common centre, each would be nearer than the
other. Transitivity and irreflexivity give the contradiction, without Definition I.15.
Its first rule, `len_lt_of_inside`, is Diagram-segment 4, but the route is a separate
candidate, using two points within, not the catalogue's Diagram-segment 4 row through
Definition I.15. This is a further
route for an existing proposition, already reported by the earlier run, not a new
finding of the rerun. It remains a candidate for the coordinator to decide; no catalogue
row is added here.

The runs above came before axiom wave one, which made eight of the rules
theorems, five of them rules about circles, among them Circle 2, by which III.2 closed
in the run on `89c5da4` and in that of 19 October. The second axiom retirement made 31
more theorems, nine of them rules about circles. Run again on the statements of
`58018a3` (21 October 2026), the second axiom retirement's before train C6a was merged
into it, the screen closed III.5 alone, by Diagram-segment 2: the rules that closed III.2
and III.6, Circle 2, Generalities 3 and Generalities 4, are theorems now, and the screen
tries only axioms. Those two rows rest on their audit lemmas, `Audit.III_2` and
`Audit.III_6`. That run read III.5 and III.6 as they were stated before brief 0008
restated them. On this revision, which holds the restated readings, Generalities 4 is a
theorem, so the screen, which tries axioms alone, no longer closes the restated III.5,
which needs that rule to finish (a scratch run of III.2, III.5 and III.6 closed none of
690 tries). So the screen's list of the rows it must find, which still names III.5, is
stale until a check change gives the screen a new canary, tracked in issue #160. And,
already on main, the screen cannot run until its list of the definitions to unfold takes
the 18 words train C6a introduced (`Arc.Congruent`, `Arc.Drawn`, `Arc.measure`,
`InSegment`, `LocallyLess`, `LocallyWithin`, `MixedAngle.Exceeds`, `MixedAngle.FallsShort`,
`MixedAngle.WellFormed`, `MixedAngle.casesOn`, `MixedAngle.region`, `MixedAngle.vertex`,
`NearVertexOpen`, `OnArc`, `OnSideOrLine`, `Places`, `Surrounds` and `WithinAngle`), also in
issue #160; until then the run on the restated readings, above, cannot be made. The
outline companions of I.45 and II.14 also reach definitions in none of the screen's lists,
such as `Figures.Outline.area`, which their statements name; the screen stops on these too
until they are listed. The screen now tries the <!-- count:axioms -->48<!-- /count -->
axioms of the certificate, 9 of them
in its list of rules about circles, `Tacit.exists_centre` among them (the radius rule of 25
October 2026 is not in that list), and unfolds, budgets and leaves out rules as the
revised screen does. No run of it on the restated statements is recorded yet.

**How each rule enters.** Argon's second review pointed out that `direct_axioms` counts a
rule a proof reaches through a lemma as well as one its own Lean names, and found that
II.14 and III.15 called Circle 2 on two points of a circle. The account of "First enters"
above the table and the notes on I.13 in 17 proofs, III.1's corollary and III.2 rest on that
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
- **The steps.** For III.1, its porism and I.13 we found no proof from three rules: each
  needs a construction Euclid makes by earlier propositions, a bisection or a
  perpendicular (I.10, I.11). In the other direction, Diagram-angle 3 is a theorem of
  the remaining axioms: `Audit.adjacent_eq_of_right` proves it from I.13, and Lean's list
  of what that proof rests on does not include it. It stays an axiom, as System E has it.

The retired checks for I.2, I.3 and I.23 used ten, twenty-two and eight axioms
respectively, all under the former existential superposition rule. Those results are
historical evidence about that rule; they do not establish overlaps with the restricted
rule.

### Near misses

- **III.10**, that a circle does not cut a circle at more points than two. Circle 4 with
  Same side 5 gives it when none of the three common points lies on the straight line
  through the centres: each pair would lie on opposite sides of that straight line, and a
  straight line has only two sides. When one of them does lie on it, the work is Euclid's.
  Circle 4 enters no proof.
- **I.4's last clause.** Metric 9 (`area_congruent`) makes the triangles equal once their
  sides and angles are. Euclid's reason there is that the triangles coincide (Common
  Notion 4), his own step in I.4, not a later proposition.
- **Representation and scope.** The measure clause of III.24's companion
  `Prop24.equalCircles` follows from its angle hypothesis alone, and the equal measures of
  III.26, and III.27 whole, hold without the equal circles, because of how a circumference
  is measured: a definition, not a rule. `Audit.III_24_measure`, `Audit.III_26_any` and
  `Audit.III_27_any` prove each so, with their axioms pinned, and the first and the last
  give back the statements of `Prop24.equalCircles` and of III.27. Since arcs got a meaning
  of their own (stage 3 of [brief 0006](../briefs/0006-statements.md)), III.24 concludes
  that the segments are congruent, and III.26 and III.28 that the circumferences are
  congruent too, which needs the equal bases and the equal circles: III.26 no longer holds
  for any two circles, and its audit example has given way to a note saying so. III.1
  takes background centres internally while retaining its construction;
  III.25 keeps the construction separate from correctness and the three classifications
  and measure comparisons, without supplied centres in `Prop25.complete` or `Prop25.of_circle`. These belong to
  the review records, under `[representation]` and `[statement]`.

- **III.30, by the same measure.** I.4 makes the angles DAB and ABD equal, and they stand
  on the halves DB and AD. Each half is measured by the angle standing on it, taken twice,
  so the halves are equal. Euclid goes instead from the equal straight lines AD and DB, by
  III.28, with his step that each half is less than a semicircle; his own III.26 would take
  him from the equal angles to equal halves without either. What the measure saves is
  III.26's work at the circumference, which it reduces to its definition and III.21.
  `Audit.III_30_measure` proves III.30 so, with its own statement and its axioms pinned; it
  cites III.21, which shows that every point of the circle across the chord from a
  circumference gives it the same measure, so it is a near miss of the measure, not of a
  rule. Our III.30 follows Euclid, by III.28, as
  [FORMALIZATION](../FORMALIZATION.md), section 5, asks. III.30's statement kept the
  measure when arcs got a meaning of their own ([brief 0006](../briefs/0006-statements.md),
  stage 3), so this near miss stays.

- **III.11 and III.12, from contact at the point** (25 October 2026, #126). Two steps of
  III.13's companions prove the conclusions of III.11 and III.12 for circles that touch
  at a point, Definition III.3 read there as Heath prefers (`TouchesInternallyAt`,
  `TouchesExternallyAt`): within, the inner centre lies between the outer centre and the
  point of contact (`TouchesInternallyAt.between`); without, the point of contact lies
  between the centres (`TouchesExternallyAt.between`). No rule gives either. Each is a
  proof by I.24 at a centre, with I.20 within and III.2 without, and nothing beneath it
  rests on Circle 2 or Circle 3; from there the companions prove the reading at the point
  the same as the whole-circle reading, for any two circles. So this is another route to
  two conclusions, not an overlap with a rule. Our III.11 and III.12 follow Euclid on the
  whole-circle reading and do not cite the two steps, which come after III.13, in
  `Elements/BookIII/Prop13.lean`.

### A separate piece of work

Each row of the first two kinds names an assumption that contains its proposition.
Deriving those propositions, or those rules, from weaker assumptions would be a separate
piece of work, with its dependencies audited. It would need a check that no proof rests,
by any path, on a rule containing its own conclusion; a ban on citing later propositions
by name cannot see that, as Astra observes. Two small steps are taken here. Diagram-angle
3 is a theorem of the other rules, which I.13 gives back. And III.2 rests on neither rule
that contains it: our proofs take its step by III.2, its corollaries or Definition I.15, and
`Prop2.within` proves Circle 2 from the other rules with no supplied centre. Lean's
certificate shows that no entry rests on Circle 2 or Circle 3, and since 24 October 2026
neither is an axiom: both are proved after III.2, and `scripts/check_fidelity.py` refuses
any entry, proposition, porism or companion, before III.2 that uses either, since such a
use cites III.2. The Book Zero lemmas Triangle.of_onCircle,
exists_onCircle_oppositeSidesOf and exists_onCircle_sameSideOf, in
[`Elements/Figure/OnCircles.lean`](../../Elements/Figure/OnCircles.lean), rested on
Circle 2; they were not certificate entries, nothing used them, and they were taken out on
24 October 2026 (#294). A search of the whole repository finds them now only in prose and
in one comment, in a Book IV scratch prototype that nothing builds. Stage 3 and the mixed
angles, which used them while staged, take those steps by III.2 and its corollaries since
they moved into `Elements/`.

### Keeping it current

`lake build Audit` compiles the audit lemmas and checks their pinned axioms; the library
is not in the default build, and nothing imports it. If a statement or a rule changes so
that an audit lemma stops compiling, its row is out of date: the overlap may have gone,
which is good news, or moved. The first users come from facts.json, and change only when
the proofs, or the lemmas they call, do. A proof that calls Circle 2 or Circle 3 cites
III.2 through it, which no entry before III.2 may; III.2, its corollaries and the two
`InsideCircle` helpers take the step without either.
