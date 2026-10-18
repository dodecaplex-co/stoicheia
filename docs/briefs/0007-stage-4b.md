# Brief 0007: the statements of stage 4b, III.7, III.8 and III.17

*18 October 2026. This brief settles the new statements that make the records of III.7,
III.8 and III.17 full, before any proof work, as [WORKFLOW.md](../WORKFLOW.md), section 2,
requires. Each statement below was written with `sorry` in the `Staging` library, compiled,
and read back in plain words. It now goes to readers who did not write it, to be
challenged, and then to the coordinator for approval. Once approved it is frozen: others
write against these statements, and a later change is a revision of this brief (WORKFLOW,
section 2, "Correcting a frozen brief"), never a quiet edit. The code states what we
formalized; where the code, this brief, a review record and a page disagree, the
disagreement is recorded and reconciled ([FORMALIZATION.md](../FORMALIZATION.md),
section 1).*

The readings are Astra's. Asked what a full statement would say for each of the five
records that stages 2 to 4 leave short of full, Astra answered on
[issue #51](https://github.com/jackChallis/stoicheia/issues/51), run read-only on the
repository at `f17b427`, with a careful reading of each enunciation, the route each needs,
and the pitfalls to avoid. Every statement here follows that answer, and this brief owes
it a great deal: warm thanks to Astra.

Base: the branch was written on main at `f17b427`. The statements are in
`Staging/Stage4b/`, as committed with this brief. `lake build Staging` passes; the new
files hold six statements with `sorry` and three checks that today's statements follow
from them. Nothing in `Elements/` changes, so main's records, lock and CI are untouched.

## The owner's decision

Jack Challis decided on 18 October 2026, after Astra's answer:

1. **I.45 and II.14 go full.** That decision belongs to brief 0006's statements, and this
   brief does not touch them.
2. **Stage 4b is approved.** III.7, III.8 and III.17 are made full by companions that
   follow Astra's readings. III.16 and III.31, whose last clauses speak of mixed angles,
   wait for a prototype of mixed angles first, and are not in this brief.

No new axiom is asked for, and none is expected: Astra proposed routes for all three
through the existing angle construction, triangle congruence, the perpendicular
construction and III.16's proved porism. These are proposed routes, as Astra says, not yet
a result checked by the kernel; the order of proof work below says what happens if a step
needs a fact the axioms lack. The lock's `[axioms]` table stays at 87, and its `[vocabulary]` does
not grow: the statements use only words already there (`Touches`, `OppositeSidesOf`,
`Collinear`, `OutsideCircle`, `InsideCircle`, the angle and the length).

## Conventions

**Companions.** Each new statement is a companion beside the unchanged `theorem PropN`,
which stays as Euclid's worked configuration under his sentences
([FORMALIZATION.md](../FORMALIZATION.md), section 2). Each gets a certificate entry, named
below in quotation marks ("III.7 general"), is listed in the review record's `companions`,
and is shown on the page with its own certificate. A check of the form
`example : type_of% @Elements.BookIII.Prop7 := …` derives today's statement from the
companion, so nothing is lost.

**"Nearer" is an unsigned angle with a ray.** In III.7 and III.8 the nearer straight line
is the one making the less angle, at the point, with the ray through the centre: the ray
FA in III.7, the ray DA in III.8. Our angle `∠ A F B` is that angle, unsigned and less
than two right angles for the points the comparison takes. It is not the distance from the centre, and not the angle with an undirected
straight line: an obtuse angle with FA is not exchanged for its acute supplement. Astra
asked for exactly this reading.

**The comparisons leave the diameter's own points to their own clauses.** The ends of the
diameter are the greatest and the least, which separate clauses state. The comparison "of
the rest" takes two points off the diameter (`¬ Collinear A D B`), on one side of it or on
opposite sides.

**The route across the diameter.** Today's comparison already holds on either side, when
both points are on that side. To compare points on opposite sides, one point is moved to
its equal partner on the other side, and the partner is shown to make the same angle with
the ray through the centre. Euclid's own I.4 step, by which he makes the partner equal,
gives the equal angle too, and Heath explains the comparison across the diameter this way
(vol. 2, pp. 16–17). In III.8 the partner must also lie in the same class, first or second
meeting; that is a geometric step to prove, not something to assume.

## Homes and owners

| Module | What goes in it | Place in the dependency order | Owner |
|---|---|---|---|
| `Elements/BookIII/Prop07.lean` | `Prop7.partner`, then the companion `Prop7.general` | after `theorem Prop7` | the III.7 task |
| `Elements/BookIII/Prop08.lean` | `Prop8.partner`, then the companion `Prop8.general` | after `theorem Prop8` | the III.8 task |
| `Elements/BookIII/Prop17.lean` | the companions `Prop17.general`, `Prop17.inside` | after `theorem Prop17`; already imports III.16 | the III.17 task |
| `Elements/Companions.lean` | the four entries | | the stage's integrator |

`Prop7.partner` and `Prop8.partner` are steps of the companions, and cite their
proposition's construction, so they go after the theorem and before the companion, not
before the theorem. The staged copies are `Staging/Stage4b/Prop07.lean`, `Prop08.lean` and
`Prop17.lean`; each imports only the proposition it accompanies. `Staging.lean`'s imports
and its folder list are the integrator's, and are left as they are: `lake build Staging`
builds every file under `Staging/` whether the root imports it or not.

## III.7, compared on either side of the diameter

`Staging/Stage4b/Prop07.lean`. Companion "III.7 general", with the step `Prop7.partner`.

```lean
theorem Prop7.partner {A D E F G H : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D) (hEFD : Between E F D)
    (hG : OnCircle G ABCD) (hH : OnCircle H ABCD) (hHG : OppositeSidesOf H G A D)
    (hFH : ‖F H‖ = ‖F G‖) :
    ∠ A F H = ∠ A F G

theorem Prop7.general {A D E F : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D) (hEFD : Between E F D) :
    (∀ B : Point, OnCircle B ABCD → B ≠ A → ‖F B‖ < ‖F A‖) ∧
    (∀ G : Point, OnCircle G ABCD → G ≠ D → ‖F D‖ < ‖F G‖) ∧
    (∀ B C : Point, OnCircle B ABCD → OnCircle C ABCD → ¬ Collinear A D B →
      ¬ Collinear A D C → ∠ A F B < ∠ A F C → ‖F C‖ < ‖F B‖) ∧
    (∀ G : Point, OnCircle G ABCD → ¬ Collinear A D G → ∃ H : Point, OnCircle H ABCD ∧
      OppositeSidesOf H G A D ∧ ‖F H‖ = ‖F G‖ ∧
      ∀ K : Point, OnCircle K ABCD → ‖F K‖ = ‖F G‖ → K = G ∨ K = H)
```

- **In plain words.** F is on the diameter AD of the circle ABCD, strictly between the
  centre E and the end D. Of the straight lines from F to the circle, FA, through the
  centre, is greater than every other, and FD, the rest of the diameter, is less than every
  other. Of any two straight lines FB, FC with B and C off the diameter, on one side of it
  or on opposite sides, the one making the less angle with the ray FA is the greater. Each
  point G of the circle off the diameter has exactly one partner H, on the other side, with
  FH equal to FG, and no third point of the circle is as far from F. `Prop7.partner`: a
  point H on the other side of AD from G, with FH equal to FG, makes the same angle with
  FA as G does. Today's III.7 follows (checked by Lean).
- **Coverage.** Heath: "and of the rest the nearer to the straight line through the centre
  is always greater than the more remote, and only two equal straight lines will fall from
  the point on the circle, one on each side of the least straight line." Full: every clause,
  and the comparison for any two of the rest; the restriction "compared on one side of AD
  only" goes. The reading of the point is disclosed: "a point … which is not the centre" is
  read of a point strictly within the diameter, other than the centre, since F at an end
  would make the least straight line nothing. The order E, F, D only names the ends: the end
  beyond F from the centre is called D.
- **Cases.** B and C on one side of AD (today's clause); on opposite sides, with the angle
  AFC acute, right or obtuse (no folding to a supplement); B or C at an end of the diameter,
  left to the greatest and least clauses; equal angles on opposite sides, where the
  comparison is silent: the partner clause gives one equal straight line on the other side,
  and `Prop7.partner` shows that it is equally inclined to FA, as Heath reads the comparison
  across AD (vol. 2, pp. 16–17). That equal angles across AD give equal straight lines is
  not stated, and Euclid's enunciation does not claim it.
- **Route.** The greatest, least and partner clauses are today's, by Euclid's argument
  [I. 20, I. 24, I. 23, I. 4]. Across the diameter: for B and C on opposite sides, C's
  partner H is on B's side with FH equal to FC (today's last clause); `Prop7.partner` makes
  the angle AFH equal to AFC; today's comparison on one side gives FH less than FB.
  `Prop7.partner` by Euclid's construction: the angle FEH' made equal to GEF on the other
  side [I. 23], the triangles GEF and H'EF equal by I.4, so that FH' equals FG and the angle
  EFH' equals EFG, and E is on the ray FA; then H is H', by today's uniqueness on one side.
  (I.8 on the triangles GEF and HEF gives the equal angles at once, from three equal sides;
  a proof that takes that shorter way labels it.)
- **Dependencies.** III.7, I.4 (or I.8), I.23; `angle_onRay_left`, `onRay_of_angle_eq`,
  `OppositeSidesOf.sameSideOf`.
- **Representation notes for the record.** "Nearer" is the less unsigned angle at F with the
  ray FA. F is a point strictly within the diameter, not the centre.

## III.8, compared on either side, within each class

`Staging/Stage4b/Prop08.lean`. Companion "III.8 general", with the step `Prop8.partner`.

```lean
theorem Prop8.partner {A D G K B : Point} {ABC : Circle} (hABC : ∃ M : Point, Centre M ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A)
    (hK : OnCircle K ABC) (hB : OnCircle B ABC) (hBK : OppositeSidesOf B K D A)
    (hDB : ‖D B‖ = ‖D K‖) :
    ∠ A D B = ∠ A D K ∧
    ((∃ C : Point, OnCircle C ABC ∧ Between D B C) ↔
      (∃ C : Point, OnCircle C ABC ∧ Between D K C)) ∧
    ((∃ H : Point, OnCircle H ABC ∧ Between D H B) ↔
      (∃ H : Point, OnCircle H ABC ∧ Between D H K))

theorem Prop8.general {A D G : Point} {ABC : Circle} (hABC : ∃ M : Point, Centre M ABC)
    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)
    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A) :
    (∀ E : Point, OnCircle E ABC → E ≠ A → ‖D E‖ < ‖D A‖) ∧
    (∀ E F : Point, OnCircle E ABC → OnCircle F ABC →
      (∃ H : Point, OnCircle H ABC ∧ Between D H E) →
      (∃ L : Point, OnCircle L ABC ∧ Between D L F) →
      ¬ Collinear D A E → ¬ Collinear D A F → ∠ A D E < ∠ A D F → ‖D F‖ < ‖D E‖) ∧
    (∀ K : Point, OnCircle K ABC → K ≠ G → ‖D G‖ < ‖D K‖) ∧
    (∀ K L : Point, OnCircle K ABC → OnCircle L ABC →
      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →
      (∃ F : Point, OnCircle F ABC ∧ Between D L F) →
      ¬ Collinear D A K → ¬ Collinear D A L → ∠ A D K < ∠ A D L → ‖D K‖ < ‖D L‖) ∧
    (∀ K : Point, OnCircle K ABC → ¬ Collinear D A K → ∃ B : Point, OnCircle B ABC ∧
      OppositeSidesOf B K D A ∧ ‖D B‖ = ‖D K‖ ∧
      ∀ N : Point, OnCircle N ABC → ‖D N‖ = ‖D K‖ → N = K ∨ N = B)
```

- **In plain words.** D is outside the circle ABC, and the straight line DA passes through
  the centre, meeting the circle first at G and again at A. DA is greater than every other
  straight line from D to the circle, and DG less than every other. Of any two points E, F
  of the concave circumference (each with a point of the circle between it and D), off DA,
  on one side of it or on opposite sides, the one making the less angle with the ray DA is
  the farther from D. Of any two points K, L of the convex circumference (each with a point
  of the circle beyond it), off DA, the one making the less angle is the nearer to D. Each
  point of the circle off DA, a point of contact included, has exactly one partner on the
  other side as far from D, and no third. `Prop8.partner`: that partner makes the same angle
  with DA, and is on the convex circumference exactly when the first point is, and on the
  concave exactly when it is. Today's III.8 follows (checked by Lean).
- **Coverage.** Heath: "of the straight lines which fall on the concave circumference, that
  through the centre is greatest, while of the rest the nearer to that through the centre
  is always greater than the more remote, but, of the straight lines falling on the convex
  circumference, that between the point and the diameter is least, while of the rest the
  nearer to the least is always less than the more remote, and only two equal straight lines
  will fall on the circle from the point, one on each side of the least." Full; the
  restriction "compared on one side of DA only" goes. "Nearer to the least", on the convex
  circumference, is the less angle with DG, which is the angle with DA, since G is on the
  ray DA.
- **The classes, and the convention for tangents.** The concave and the convex circumference
  are read as today: the second and the first meeting of a straight line from D with the
  circle. Euclid's lines are "drawn through to the circle", and a straight line touching the
  circle from D does not meet it at two points (Definition III.2), so its point of contact
  should have no point of the circle before it and none beyond it, and falls on neither
  class. That step is not stated in Lean (open question 2). The convention is stated in
  words, in the staged file and in the record. The partner clause, kept from today's statement, covers
  points of contact too: that stronger coverage stays, as Astra advised.
- **No single order across the classes.** The two comparisons are separate clauses, and no
  statement combines them: the near and the far meeting of one straight line from D make the
  same angle with DA and are at different distances.
- **Cases.** Both points on one side (today's clauses); on opposite sides; a point of contact
  of a tangent (on neither class; in the partner clause); A and G, the axial points, left to
  the greatest and least clauses.
- **Route.** The greatest, least and partner clauses are today's [III. 1, I. 20, I. 21,
  I. 24, I. 23, I. 4], with today's modified last step. Across the diameter: for E and F
  concave on opposite sides, F's partner B is on E's side as far from D (today's last
  clause); `Prop8.partner` makes the angle ADB equal to ADF, and B concave; today's
  comparison on one side finishes. The convex case is the same. `Prop8.partner`: the equal
  angle by Euclid's I.4 step at the centre M, as in III.7, with M on the ray DA (or I.8 at
  once, labelled). The class: if K is between D and a point C of the circle, C's partner C'
  makes the angle ADC' equal to ADC, which is ADK, which is ADB, so C' is on the ray DB
  (`onRay_of_angle_eq`), and DC', equal to DC, is greater than DK, equal to DB, so B is
  between D and C'. The concave case is the same with the order reversed. Equal distance
  alone would not do: the step needs the partner's angle and its class.
- **Dependencies.** III.8, III.1, I.4 (or I.8), I.23; `onRay_of_angle_eq`,
  `OppositeSidesOf.sameSideOf`, the order of lengths on a ray.
- **Representation notes for the record.** "Nearer" is the less unsigned angle at D with the
  ray DA. The convex circumference is the first meeting, the concave the second; a point of
  contact of a tangent from D is on neither, by convention, and the partner clause covers it.

## III.17, from a point not within the circle

`Staging/Stage4b/Prop17.lean`. Companions "III.17 general" and "III.17 inside".

```lean
theorem Prop17.general {A : Point} {BCD : Circle} (hBCD : ∃ E : Point, Centre E BCD)
    (hA : ¬ InsideCircle A BCD) :
    ∃ X : Point, Touches A X BCD

theorem Prop17.inside {A : Point} {BCD : Circle} (hA : InsideCircle A BCD) :
    ¬ ∃ X : Point, Touches A X BCD
```

- **In plain words.** Given a circle BCD with a centre, and a point A not within it, there is
  a point X such that the straight line AX touches the circle: it meets the circle and does
  not cut it. A may be outside the circle, and then the point of contact is another point; or
  on it, and then the point of contact is A itself; the proof draws AX at right angles to the
  radius EA [I. 11], and it touches by III.16's porism. `Prop17.inside`: from a point within
  the circle, no point X makes the straight line AX touch it. Together they say that, for a
  circle with a centre, not being within the circle is exactly the condition for the problem
  to have a solution. Today's III.17 follows from `Prop17.general` (checked by Lean).
- **Coverage.** Heath: "From a given point to draw a straight line touching a given circle."
  Full: the point on the circumference, which Euclid leaves to III.16's porism and Heath
  names as the omitted case (vol. 2, p. 44), is included; the restriction "a point outside
  the circle" goes. A point within the circle admits no solution, and `Prop17.inside` says
  so: the enunciation's "a given point" is read, as it must be, of a point for which the
  problem can be solved.
- **The form of the conclusion, and why.** Today's form, a point B of the circle with
  `Touches A B BCD`, cannot hold when A is on the circle: the point of contact is then A, and
  `Touches` (Definition III.2) asks for two different points to name its straight line. Two
  forms work: Astra's `∃ X, Touches A X BCD`, or a straight line and its point of contact
  returned separately, the point allowed to be A. We take the first, which issue #53 also
  names. It says what Euclid's problem asks, in Definition III.2's own word, the word III.16's
  porism concludes and III.18, III.19 and III.37 use; and it already contains the meeting:
  `Touches` asserts a point of the circle on the straight line, the point of contact, which a
  citer reads off it. A separate line and contact point would restate Definition III.2 in
  other words beside it. The cost is that the point of contact, which today's `Prop17`
  returns as B, now sits inside `Touches`, after a straight line is named: the III.17 check
  in the staged file takes four lines to read it off, and a later citer that needs it pays
  the same. A Book Zero lemma would pay it once (open question 5).
- **Cases.** A outside the circle (Euclid's construction; the point of contact is another
  point); A on the circle (the perpendicular to the radius at A); A within (no solution,
  `Prop17.inside`).
- **Route.** For A outside, today's III.17. For A on the circle, as Heath and Astra say: E
  the given centre is not A; the straight line AX drawn at right angles to EA at A [I. 11]
  touches the circle [III. 16, Por.]. The case on the circle is Heath's (vol. 2, p. 44), not
  Euclid's construction, and the record's route says so. `Prop17.inside` is Book Zero's
  `Touches.not_inside`, applied at A itself: a straight line through a point within a circle
  cuts it. It is listed as a companion so that the condition for a solution appears on the
  page with a certificate; it generalizes no clause of the enunciation.
- **Dependencies.** III.17, I.11, III.16 Por.; `Touches.not_inside`.

## The order of proof work

Stage 4b runs beside stage 4, on its own files, and depends on nothing of stages 2 and 3.
Each step leaves `lake build`, `lake build Audit` and `lake build Staging` green.

1. **III.17,** one task: `Prop17.general` and `Prop17.inside`. The shortest, and a check of
   the companion machinery.
2. **III.7,** one task: `Prop7.partner`, then `Prop7.general`.
3. **III.8,** one task: `Prop8.partner`, the angle first and the class after, then
   `Prop8.general`. The hardest of the three; III.7's `partner` is its model.

The three may run in parallel: they share no file. When each is proved, it moves into its
`PropNN.lean`, its staged copy and check are deleted in the same change, and the integrator
adds its entries to `Elements/Companions.lean`. Then the records, the pages and the prose
listed below are brought up to date. If any step turns out to need a fact the axioms lack,
work on it stops and the case goes to Jack, as for every stage.

## Records made stale

Nothing in `Elements/` changes on this branch, so no record is stale yet. When the
companions move:

- `review/III/07.toml`, `review/III/08.toml`, `review/III/17.toml`: the Lean file changes,
  the companions are listed, and the scope goes from `restricted` to `full`, with the
  representation notes above; III.8's route stays `modified`. Each is read again by a
  reviewer, and stamped by no one who did not review it.
- The prose that says these statements are restricted: `mishnah/III/17.md` ("Euclid's
  construction needs A outside the circle, and our statement asks for it"),
  `mishnah/intro/III.md` ("Five statements are restricted …"), `mishnah/III/07.md` and
  `mishnah/III/08.md` where they speak of one side;
  [brief 0004](0004-book-III.md)'s line on "nearer", "on one side of it", and its rows for
  III.7, III.8 and III.17; `docs/reports/gaps-book-III.md` under III.17, for the boundary
  case.
- The generated output (README's Book III scope row, the pages, the certificate), which the
  integrator regenerates, and PROGRAM.md's status table, the coordinator's.

## The checks at the end of stage 4b

- Every companion proved and certified; every check of today's statement compiles where it
  moves.
- `[axioms]` at 87; the vocabulary unchanged.
- Every touched record re-reviewed; III.7, III.8 and III.17 full.

## Open questions for the owner

1. **`Prop17.inside`, a companion or a sentence?** It makes "not within" visibly the
   condition for a solution, as Astra asked, and costs one line of proof. It is not a clause
   of Euclid's enunciation, and III.17 is full without it: it is a remark about when the
   problem can be solved, not a generalization of a clause, and it is listed as a companion
   so that the condition appears on the page with a certificate. "Exactly the condition"
   holds for a circle with a centre, which `Prop17.general` asks for and `Prop17.inside`
   does not. The recommendation is to keep it as a companion; if the owner prefers, it
   becomes a sentence of the record and the page.
2. **The tangent convention, in words or in Lean?** It is stated in words. A small statement,
   `Prop8.tangent`, that a point of contact of a straight line touching from D has no point of
   the circle before it or beyond it, would check the convention, at the cost of one more
   entry. The classes' own hypotheses already exclude such a point, so the recommendation is
   words.
3. **The partner's angle, by I.4 or I.8?** Euclid's step is I.4, after his construction, and
   Heath and Astra describe the route that way; I.8 on three equal sides gives the angle at
   once. The steps are not under Heath's sentences, so either is honest. The recommendation is
   I.4, following the page, and I.8 if the construction proves awkward, labelled in the Lean.
4. **III.16 and III.31** are outside this brief: their mixed angles wait for the prototype the
   owner asked for, on Astra's reading of local containment near the vertex.
5. **A lemma for the point of contact?** The coordinator could add to Book Zero
   `Touches.contact (h : Touches A X α) : ∃ B, OnCircle B α ∧ Collinear A X B`, so that a
   citer of `Prop17.general` (III.37 re-proved against it, say) reads the point of contact
   off in one step. It is a request to the foundations' owner, not part of this brief's
   statements, and nothing here waits for it.

## Appendix: the challenges, and what was done

Two readers challenged the staged statements and this brief on issue #53, at `e5549d8`.
Both would accept "full" for III.7, III.8 and III.17 as staged; both checked each statement
against Astra's readings, and found it true in the standard model and its check of today's
statement sound. Every finding was editorial, about the wording of docstrings and of this
brief; no statement changed. Each was applied, in `Staging/Stage4b/` and here, except the
two optional proposals in the last rows, which are answered.

| Finding | Done |
|---|---|
| III.7, Cases: "the partner clause speaks" of equal angles on opposite sides, but it speaks of equal lengths | Reworded: the comparison is silent; the partner clause gives one equal straight line, and `Prop7.partner` its equal inclination; the converse is not stated, and Euclid does not claim it |
| "None is needed" states sufficiency before any proof; Astra calls it a proposed route | "None is expected", with Astra's own qualification that the routes are proposed, not checked by the kernel |
| "From nothing up to two right angles" suggests the endpoints are in play | "Unsigned and less than two right angles", in the III.7 module doc and under Conventions |
| `Prop17.inside`'s docstring gave the reason ("meets the circle at two points"), not the claim | Now the claim, with its reason by `Touches.not_inside` |
| `Prop8.partner`'s docstring gave only the angle's route, not the class's | The class's route added: the far (near) meeting's own partner on the ray DB, and the order of lengths on the ray |
| `Prop8.general`'s "for it has no point of the circle before it or beyond it" is an unchecked claim | Marked as the convention read from "drawn through", resting on the classes' hypotheses; the module doc and the brief say the step from Definition III.2 is not stated in Lean (open question 2) |
| `Prop17.general`'s docstring and plain words credit it with the perpendicular at A, which is III.18 | Reworded as the route: the proof draws AX at right angles to EA [I. 11], and it touches by III.16's porism; the statement claims only the touching |
| `Prop17.general`'s docstring cited "[III. 17]" inside III.17's own companion | "Today's `Prop17`" |
| The case of A on the circle not labelled as Heath's | Said in the docstring and the Route: Heath's (vol. 2, p. 44), not Euclid's construction, and the record's route says so |
| "Exactly the condition" holds only for a circle with a centre | Qualified in the module doc, `Prop17.inside`'s docstring, the plain words and open question 1 |
| `Prop17.inside` is a remark about solvability, not a generalization of a clause | Kept as a companion; the brief and module doc say why: the condition appears on the page with a certificate |
| The point of contact now sits inside `Touches`, costing every citer the unpacking | The statement kept; the cost stated under "The form of the conclusion"; `Touches.contact` proposed to the coordinator as open question 5 |
| Optional: strengthen `Prop7.partner` to an iff, `‖F H‖ = ‖F G‖ ↔ ∠ A F H = ∠ A F G` | Answered, not applied: the companion needs only the forward direction, the reverse is no clause of Euclid's and would add a ray-meets-circle step to the proof; the Cases now say it is not stated |
