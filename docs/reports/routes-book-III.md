# Euclid's routes in Book III

*21 October 2026.*

This report answers issues #125, #126, #127, #129, #130 and #131. Five of them ask for
Euclid's own argument where our proofs of Book III take another way, or for something his
words say that our Lean does not yet say; the sixth asks which of our calls of III.1 do any
work. The Lean is in seven files under `Staging/Routes/`, and none of it is in `Elements/`
yet. Its declarations are in two namespaces:

```text
Elements.BookIII.Staging   III.20 in general, with its helper, its special case and
                           the theorem that a circumference is its angle at the centre
Elements.BookIII.Routes    everything else
```

III.20 in general changes the statement of a main theorem, and FORMALIZATION, section 6,
stages a changed main theorem in the first namespace, under the proposition's own name,
while the theorem it replaces is still declared in `Elements`; the three theorems that go
with it are named after it. The rest are new proofs of statements that do not change, and
new drafts. No rule names a namespace for them; the coordinator chose on 22 October 2026
that they keep this one (see "Open questions", below).

**The statements the files stand on.** [Brief 0008](../briefs/0008-centre.md) restates
Book III so that every circle has a centre (`Tacit.exists_centre`). The trains C6a, C6b and
C6c carry the next move of Book III's files into `Elements/`, those restatements among it.
As their head, train C6c carries the other two, and in this report it stands for all three.
This branch changes no file of `Elements/`, and not `facts.json`: they are those of the
head of train C6c that it last merged, and, once train C6c is on main, those of the main it
last merged. The immutable comparison `git diff
e9bac7964aa1222d4fa3ca7c7a4a215abf7dbfc3
e09f40f6aae8b83ab70217f68a50b3b36ce6c6ff -- Elements facts.json` prints nothing. The
same comparison with `--stat` lists the eleven files the branch changes: the seven under
`Staging/Routes/`; `Staging.lean`, in its
imports and its paragraph on `Routes/`; this report; the decisions page,
[brief 0002](../briefs/0002-decisions.md), in its routes bullet alone; and
[docs/reports/overlaps.md](overlaps.md), the coordinator's file, in its sentence on staged
work, which 5fca8529, a commit of the pre-merge validation (WORKFLOW, section 10), made
true of `Staging/Routes/` with the coordinator's approval of 21 October 2026. Since then
the routes bullet has left the decisions page for an entry file of its own,
[docs/decisions/2026-10-21-routes-book-iii.md](../decisions/2026-10-21-routes-book-iii.md),
in the same words, as [WORKFLOW](../WORKFLOW.md), section 10, "Decision entries", asks
once entry files are in use: the branch now leaves the page as it finds it and adds that
file in its place. Main did not
have the restatements when this report was written, and these files land after train C6c.
In this report, **the statement in `Elements/`** or **the proof in `Elements/`** of a
proposition is the one train C6c leaves in `Elements/BookIII/`, which is the one on this
branch. The files were written on main's statements as at 2e8aecf and then moved onto those
in `Elements/`: III.8, III.27, touching at a point and the angle of contact at 4a6d9a49,
and III.20, III.21 and III.26 at 9f8c8adb. Independent readers read both moves, and
86c5748d and c868a9fc answer their minor findings ("Who read what", at the end). For these
files train C6c changes six things:

- a centre that a statement uses nowhere else is taken inside the proof, by the rule, and
  no longer given (brief 0008, section 4);
- III.24 and III.26 conclude that the segments, or the circumferences, are congruent, as
  well as equal in measure;
- contact within, `TouchesInternally`, asks for a point of the inner circle within the
  outer, where it asked that the circles be two (brief 0008, section 7);
- the mixed angles are in `Elements/`;
- III.1's porism is argued directly from its given centre;
- III.35 to III.37 take their centre by the rule.

Two things stand between these files and `Elements/`. The first is the move itself. Once
train C6c has landed, each staged proof goes into its proposition's file, with its review
record read again, its passages rewritten where the route has changed, and its page made
afresh. The second is the owner's approval of every new statement and definition: the
reading of Definition III.3 at the point of contact (#126), the angle at the centre of any
size and III.20 for it (#129), and the angle of contact after III.18 (#130). **No new
statement or definition in these files is approved.** The proofs for III.8 and III.27 prove
the statements in `Elements/` and stand on nothing new. Those for III.20 as `Elements/`
states it (III.20's special case, below), III.21 and III.26 prove the statements in
`Elements/` too, but rest on the draft angle at the centre, and so wait for its approval as
well.

The coordinator's orders of 21 October 2026 for this work directed these proofs into new
files under `Staging/Routes/`. WORKFLOW, section 2, admits in `Staging/` the proofs of a
prototype the coordinator has approved, as the decisions page records for the mixed angles
and for the restricted superposition rule. On 22 October 2026 the coordinator confirmed
that those orders were the coordinator's, and are not the owner's approval of a prototype;
this report claims none. The files stand in `Staging/` as unfinished work, under the
owner's rule of 20 October 2026 (WORKFLOW, section 10, "Unfinished work may land on main,
with its issue"), while an issue labelled `blocks-release` tracks their move into
`Elements/`. The orders approve no statement or definition, and no move into `Elements/`.

| Issue | File | What it holds | Statement |
|---|---|---|---|
| #125 | [`Prop08.lean`](https://github.com/jackChallis/stoicheia/blob/fc3dffa892a32be571c28b208dfb40189226db93/Staging/Routes/Prop08.lean) | III.8, with Euclid's last step | as in `Elements/` |
| #127 | [`Prop27.lean`](https://github.com/jackChallis/stoicheia/blob/fc3dffa892a32be571c28b208dfb40189226db93/Staging/Routes/Prop27.lean) | III.27 by Euclid's reductio and halving, the obtuse case by the remainders, the right read off the measure | as in `Elements/` |
| #126 | [Touching.lean](https://github.com/jackChallis/stoicheia/blob/fc3dffa892a32be571c28b208dfb40189226db93/Staging/Routes/Touching.lean) | Definition III.3 read at the point of contact, and its agreement with our reading of the whole circles | new, a draft |
| #129 | [Prop20.lean](https://github.com/jackChallis/stoicheia/blob/fc3dffa892a32be571c28b208dfb40189226db93/Staging/Routes/Prop20.lean), [Prop21.lean](https://github.com/jackChallis/stoicheia/blob/fc3dffa892a32be571c28b208dfb40189226db93/Staging/Routes/Prop21.lean), [Prop26.lean](https://github.com/jackChallis/stoicheia/blob/fc3dffa892a32be571c28b208dfb40189226db93/Staging/Routes/Prop26.lean) | the angle at the centre of any size; III.20 for it; III.21 and III.26 by Euclid's one argument | III.20 in general new, a draft; III.20's special case, III.21 and III.26 as in `Elements/` |
| #130 | [AngleOfContact.lean](https://github.com/jackChallis/stoicheia/blob/fc3dffa892a32be571c28b208dfb40189226db93/Staging/Routes/AngleOfContact.lean) | III.16's comparisons for every straight line touching a circle, after III.18 | new, a draft |
| #131 | none | which calls of III.1 do work | analysis only |

"As in `Elements/`" in the last column means that the staged theorem has exactly the type
of the theorem in `Elements/`, which each file checks with Lean in its last declaration
(see "Checks", at the end).

**Open questions.** Three were the coordinator's, and the coordinator answered them on 22
October 2026, under the owner's delegation of small calls that day:

1. whether the orders of 21 October 2026 are recorded as the approval of a prototype under
   WORKFLOW, section 2: they are not, for they were the coordinator's orders (above);
2. whether the declarations other than those of III.20 in general keep the second
   namespace above, which no rule names, or are renamed: they keep it;
3. whether the five calls of III.1 under Heath's "[III. 1]", which do no work, stay under
   brief 0008's rule or are dropped as dummy citations: they are dropped, in #131's own
   train, after this one (#131, at the end).

The owner's is the approval of each draft in the text it has now (the next section), and
with it the question, under #126, of the clause that contact within at a point asks for.

## For the owner: the drafts as they now stand

Issues #126 and #129 asked for a brief first. This section, with the sections on #126,
#129 and #130 below, stands as that proposal; a proposition brief follows the owner's
approval.

The drafts await approval in the text they have now. Moving them onto the statements in
`Elements/` changed no definition, and eleven theorems, each only by dropping hypotheses.
The first column names each theorem within its namespace; the second says what it lost:

```text
in Elements.BookIII.Staging
Prop20                          {E} (hE : Centre E ABC)
Prop20.circumference            (hE : Centre E α)

in Elements.BookIII.Routes
Touching.small                  {G} (hG : Centre G β)
TouchesInternallyAt.whole       {F G} (hF : Centre F α) (hG : Centre G β)
TouchesExternallyAt.whole       {F G} (hF : Centre F α) (hG : Centre G β)
touchesInternally_iff           (hα : ∃ F : Point, Centre F α) (hβ : ∃ G : Point, Centre G β)
touchesExternally_iff           (hα : ∃ F : Point, Centre F α) (hβ : ∃ G : Point, Centre G β)
circlesTouch_iff                (hα : ∃ F : Point, Centre F α) (hβ : ∃ G : Point, Centre G β)
Touching.internally_of_between  (hαβ : α ≠ β)
Prop18.contact_locallyEqual     {D} (hD : Centre D ABC)
Prop18.contact_lt               {D} (hD : Centre D ABC)
```

Each centre dropped appeared nowhere else in its statement, so it goes by brief 0008's rule
(section 4), as the statements in `Elements/` lose theirs: III.20 in general takes its
centre by the rule, under Euclid's "let the angle BEC be an angle at its centre", the
theorem that a circumference is its angle at the centre needs none, and the three agreements
now speak of any two circles. The hypothesis that the circles are two, in the theorem that
leads from the straight line through the centres to contact within, was used by no proof
once the contact within of `Elements/` stopped asking for it; and with G between F and C
they are two in any case, for F and G differ and a circle has only one centre.

Five theorems speak of the contact within of `Elements/`, whose third clause now asks for a
point of the inner circle within the outer, where it asked that the circles be two. That
point shows the circles two, so the clause asks more, and each of the five now reads
differently, in one of three ways:

```text
concludes more    TouchesInternallyAt.whole, Touching.internally_of_between
assumes more      TouchesInternallyAt.of_whole
relates anew      touchesInternally_iff, circlesTouch_iff
```

Two conclude contact within, and so say more than they did: the theorem that contact
within at C is contact within of the whole circles, and the theorem that leads from the
straight line through the centres to contact within, which also lost its hypothesis that
the circles are two. One assumes it, and so asks more of what it is given: the theorem that
contact within of the whole circles is contact within at C, whose text has not changed,
and which now finds the circles two from that point. The two agreements, for contact
within and for the two contacts together, now prove the reading at the point the same as
the whole-circle reading of `Elements/`.

Every other draft has the text it had on main's statements as at 2e8aecf, and so have the
five definitions: the reading near a point, the three contacts at a point, and the angle at
the centre. Copies of facts that are now in `Elements/`, four in Touching.lean and fifteen
steps of III.16's comparisons in AngleOfContact.lean, are deleted, and those facts are
cited from `Elements/`.

## III.8: Euclid's own last step (#125)

**What Euclid does.** III.8 ([heath/III/08.md](../../heath/III/08.md)) compares the
straight lines drawn from a point D outside a circle. Having proved the order on the
concave circumference and the order on the convex, he constructs DB on the other side of
DA, equal to DK, by I.4 at the centre M, and supposes a third straight line DN equal to DK:
"that is, the nearer to the least DG equal to the more remote: which was proved
impossible." The order on the convex circumference does the work.

**What `Elements/` does.**
[Elements/BookIII/Prop08.lean](../../Elements/BookIII/Prop08.lean) takes that last step by
I.24 at the centre M, for every point of the circle: unequal angles at M give unequal
straight lines from D. Its record, [review/III/08.toml](../../review/III/08.toml), gives the
route as modified, and the [gap catalogue](gaps-book-III.md) says why under III.8: the
convex order does not reach a DN ending on the concave circumference, or a DK that touches
the circle.

**What the staged file does.** It keeps the statement and the proof in `Elements/`, and
changes only the last step. When N is off DA, it is compared with DB or DK, whichever lies
on its side of DA. If both are on the convex circumference, the one making the less angle
with DA is the nearer to the least DG, and so the less, by the convex order proved earlier
in the same proof: that is Euclid's step. If the two angles are equal, N lies on the same
ray from D and as far from D, and so is the same point. Two points of the concave
circumference are compared by the concave order in the same way, a case Euclid's figure
leaves aside. On DA itself, N is A or G, the greatest and the least. The helpers
`Prop8.outside`, `Prop8.within` and `Prop8.on_diameter` are cited from III.8's file in
`Elements/`. The file ends with its own check that the statement is the one in `Elements/`:

```lean
example : type_of% @Elements.BookIII.Routes.Prop8 = type_of% @Elements.BookIII.Prop8 := rfl
```

**What remains of the departure.** I.24 at M stays for the cases neither order reaches:
the two points on different circumferences, or one of them a point where a straight line
from D touches the circle, which lies on neither. Each order compares points of one
circumference only, for the two points where one straight line from D meets the circle
make one angle with DA and lie at different distances from D. The file labels each case
where it stands. These cases lie within Euclid's statement, so under
[review/SCHEMA.md](../../review/SCHEMA.md) the route stays modified, with a narrower note:
the I.24 step now serves only where his order cannot.

**What is left.** No approval is needed. At the move the staged proof replaces the proof
in `Elements/BookIII/Prop08.lean`; the record is read again, with its passage at "that is,
the nearer to the least DG equal to the more remote" and its route note rewritten; and the
gap catalogue's entry and the mishnah's paragraph on "which was proved impossible" say what
changed. The companions `Prop8.partner` and `Prop8.general` use the statement, which does
not change. The staged proof still takes the centre by III.1 under Heath's "[III. 1]", as
the proof in `Elements/` does (#131, below).

## III.27: Euclid's reductio and halving, the obtuse case by the remainders (#127)

**What Euclid does.** III.27 ([heath/III/27.md](../../heath/III/27.md)) proves the angles
at the centres equal by a reductio: were BGC the greater, the angle BGK made equal to EHF
would stand on a circumference equal to EF by III.26, and so "BK is also equal to BC, the
less to the greater: which is impossible." Then he halves: "And the angle at A is half of
the angle BGC, and the angle at D half of the angle EHF". The halving holds where the
angles at A and D are acute. Heath, having set out the cases under III.26, writes of
III.27 that "the remarks about the method of treating the different cases apply here also"
(vol. 2, p. 59).

**What `Elements/` does.**
[Elements/BookIII/Prop27.lean](../../Elements/BookIII/Prop27.lean) keeps Euclid's reductio
at the centres, and his halving where the centres lie on the sides of A and D. Elsewhere the
angles at A and D are right or obtuse, and the proof in `Elements/` halves the measure of
the circumference instead (`Circumference.standing`: a circumference is twice the angle
standing on it). That is the shortcut [FORMALIZATION](../FORMALIZATION.md), section 5, names
for "III.27, III.30 and III.26's measures", "by the circumference measure alone", before it
says "take his route, for his inferences are the proposition's content". The record,
[review/III/27.toml](../../review/III/27.toml), gives the route as modified.

**What the staged file does.** It writes Euclid's argument, his reductio and his halving
together, once, for any points of the two circles on the centres' sides whose angles stand
on equal circumferences, and uses it as the centres fall. A first step shows that equal
circumferences put the centres alike: both on the sides of A and D, both on BC and EF, or
both beyond them, since a circumference is less than a semicircle, a semicircle, or greater
as its centre lies (`Circumference.lt_semicircle`, `Circumference.semicircle`,
`Circumference.gt_semicircle`).

```lean
theorem Prop27.sides {A B C D E F G H : Point} {ABC DEF : Circle} (hG : Centre G ABC)
    (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hC : OnCircle C ABC)
    (hD : OnCircle D DEF) (hE : OnCircle E DEF) (hF : OnCircle F DEF)
    (hBCA : Triangle B C A) (hEFD : Triangle E F D)
    (heq : standing ABC B A C = standing DEF E D F) :
    (SameSideOf G A B C ∧ SameSideOf H D E F) ∨ (Between B G C ∧ Between E H F) ∨
      (OppositeSidesOf G A B C ∧ OppositeSidesOf H D E F)
```

- **Acute**, as in Euclid's figure: his argument runs at A and D themselves.
- **Obtuse**: we pass to the circumferences that remain, as III.26 passes to "the
  circumference BKC which remains". The angles standing on them at points X and Y of the
  circles, on the centres' sides, are acute, and his argument makes them equal; then III.22
  leaves the angles at A and D as what remains of two right angles (C.N. 3). This is the
  treatment Heath proposes under III.26, which his remark carries over to III.27.
- **Right**: the centres lie on BC and EF, and there is no angle at the centre to halve.
  Each angle is an angle in a semicircle, and right (`Prop24.angle_type`). That step still
  rests on the measure of the circumference: `Prop24.angle_type` reads the right angle off
  it, the semicircle being two right angles (`Circumference.semicircle`) and the angle in
  it half of that (`Circumference.eq`).

In the reductio, under "therefore the circumference BK is equal to the circumference EF"
[III. 26], III.26 in `Elements/` gives BK and EF equal in measure and congruent. The
comparison with BC that follows is by measure, so the Lean takes the measures, as III.27 in
`Elements/` does; a remark in the staged file says why. The file does not call
`Circumference.standing`. Its theorem for III.27 has the statement in `Elements/` exactly,
and the file ends with Lean's check of that, as III.8's does (see "Checks").

**What remains of the departure.** Euclid's halving covers acute angles alone, so the
obtuse and right cases are argued another way, by III.22 and by the angle in a semicircle;
each is labelled where it stands. As in `Elements/`, K is laid on the ray of I.23 at the
distance GB, so that it is on the circle, and "the less to the greater" is read from the
angles at G (`Circumference.centre`). The obtuse and right cases lie within Euclid's
statement, so the route stays modified. Its note changes from the measure to III.22 for the
obtuse case, and keeps the measure for the right case, which still rests on it through
`Prop24.angle_type`. The measure still compares the circumferences in every case: the
staged file's first theorem sorts the centres by it, calling `Prop24.angle_type` for where
they lie, and the reductio reads "the less to the greater" from it, so `Circumference.eq`
[III. 21] lies beneath the acute and obtuse cases too. What the note records is where the
angles at A and D are read off the measure: now the right case alone.

**What is left.** No approval is needed: nothing new is stated or defined, and the step that
puts the centres alike is a helper of III.27, before it in its file. At the move the staged
proof replaces the proof in `Elements/`, the record is read again with its route note, and
the gap catalogue's entry for III.27, which tells of `Circumference.standing`, is revised.

## Definition III.3 read at the point of contact (#126)

**What Euclid says, and how it has been read.** "Circles are said to touch one another
which, meeting one another, do not cut one another" (Definition III.3,
[heath/III/front.md](../../heath/III/front.md)). Heath reports Isaac Todhunter on two
opinions of it: one, that it "only means that the circles do not cut in the neighbourhood
of the point of contact, and that it must be shown that they do not cut elsewhere"; the
other, that "the definition means that the circles do not cut at all". "Todhunter thinks
the latter opinion correct." Heath himself prefers "to read the definition as meaning
simply that the circles meet at a point but do not cut *at that point*", and observes that
Euclid "does practically assume" in III.11 to III.13 "the theorem that circles touching at
one point do not intersect anywhere else" (vol. 2, p. 3).

**What `Elements/` does.**
[Elements/Foundations/DefinitionsIII.lean](../../Elements/Foundations/DefinitionsIII.lean)
reads the definition of the whole circles, Todhunter's reading. `TouchesInternally`: the
circles meet at C, some point of the inner circle is within the outer, and no point of the
inner circle falls outside the outer. `TouchesExternally`: they meet at C, and no point is
within both. `CirclesTouch`: one of these, either way round within. The point within came
with train C6c, in place of "they are two circles" (brief 0008, section 7). So our
definitions carry what Heath says Euclid practically assumes, as the gap catalogue says
under III.11.

**What the staged file does.** It says "near C" with a circle about C, as Euclid would draw
one, and with no numbers, as the mixed angles of `Elements/` say "near the vertex"
(`LocallyWithin`, in `Elements/Foundations/DefinitionsIII.lean`). Each new definition is
the whole-circle definition with "every point" narrowed to "every point near C", save one
clause:

- near C every point has a property when every point within some circle about C has it;
- the circles touch within at C when they meet at C, are two circles, and near C no point
  of the inner circle falls outside the outer;
- they touch without at C when they meet at C, and near C no point is within both;
- they touch at C when they touch within, either way round, or without.

```lean
def Touching.Near (C : Point) (p : Point → Prop) : Prop :=
  ∃ γ : Circle, Centre C γ ∧ ∀ P : Point, InsideCircle P γ → p P

def TouchesInternallyAt (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧ α ≠ β ∧
    Touching.Near C (fun P => OnCircle P β → ¬ OutsideCircle P α)

def TouchesExternallyAt (α β : Circle) (C : Point) : Prop :=
  OnCircle C α ∧ OnCircle C β ∧
    Touching.Near C (fun P => InsideCircle P α → ¬ InsideCircle P β)

def CirclesTouchAt (α β : Circle) (C : Point) : Prop :=
  TouchesInternallyAt α β C ∨ TouchesInternallyAt β α C ∨ TouchesExternallyAt α β C
```

The one clause is the third of contact within: `TouchesInternally` asks for a point of the
inner circle within the outer, and contact within at C asks that the circles be two. The
proofs bridge it both ways. From the whole circles, that point of the inner circle is not
on the outer (System E, Generalities 4), so the circles are two. Back to the whole circles,
the step from the straight line through the centres finds the point: with G, the inner
centre, between F, the outer centre, and C, the straight line from G to a point off FG
meets the inner circle at X, off FG (Intersections 5), and FX is less than FG, GX together
[I. 20], which are FG, GC, that is FC; so X is within the outer circle. Whether contact
within at C should instead take the clause of `Elements/`, read near C, is a question for
the owner.

Then the agreement: since every circle has a centre (`Tacit.exists_centre`), the reading at
the point and the reading of the whole circles say the same for any two circles, for
contact within, for contact without, and for the two together.

```lean
theorem touchesInternally_iff {α β : Circle} {C : Point} :
    TouchesInternally α β C ↔ TouchesInternallyAt α β C

theorem touchesExternally_iff {α β : Circle} {C : Point} :
    TouchesExternally α β C ↔ TouchesExternallyAt α β C

theorem circlesTouch_iff {α β : Circle} {C : Point} :
    CirclesTouch α β C ↔ CirclesTouchAt α β C
```

The whole-circle reading gives the local one at once. The other way is the content, and it
goes through the straight line joining the centres, which the proofs take by the rule:

```lean
theorem TouchesInternallyAt.whole {α β : Circle} {C : Point} (h : TouchesInternallyAt α β C) :
    TouchesInternally α β C

theorem TouchesExternallyAt.whole {α β : Circle} {C : Point} (h : TouchesExternallyAt α β C) :
    TouchesExternally α β C

theorem Touching.internally_of_between {α β : Circle} {C F G : Point} (hF : Centre F α)
    (hG : Centre G β) (hCα : OnCircle C α) (hCβ : OnCircle C β) (h : Between F G C) :
    TouchesInternally α β C
```

With F the centre of the outer circle and G that of the inner, contact within at C puts G
between F and C; contact without puts C between F and G. Were C off the straight line FG, a
small circle about C would cut the inner circle at a point farther from F than C is, by
I.24 at G, as III.7 compares straight lines from a point to a circle; without, it would give
a point within both circles near C, by I.24 and III.2. Were C on that straight line but on
the wrong side, I.20, or a point of a radius near C, would do the same. From the straight
line through the centres, I.20 and Definition I.15 give the whole circles, and, within, the
point of the inner circle within the outer, as above.

**What remains of the departure.** The two steps that put C on the straight line through
the centres reach the conclusions of III.11 and III.12 by a route that is not Euclid's. The
file says so, and does not offer them as his proofs: the statements of III.11 to III.13
keep the whole-circle reading, and the agreement belongs beside Definition III.3 and
III.11's commentary. The proofs use Book I, III.2 and System E's diagram and construction
rules, Intersections 5, 8 and 9 among the latter, with the rule that every circle has a
centre, and nothing that rests on Circle 2 or Circle 3.

**What is new, and what is left.** The four definitions and the theorems about them are
new, a draft for the owner's approval, and not approved; nothing in `Elements/` uses them.
The agreement holds for any two circles, its centres taken by the rule. No fact is proved
here again: the five small facts the agreement shares with the mixed angles are cited from
`Elements/`, `exists_circle_about` and `onLine_of_collinear` from
`Elements/Figure/Regions.lean`, and `foot_nearest`, `len_lt_of_add_lt` and
`surrounds_sameSideOf` from `Elements/BookIII/MixedAngles.lean`; two of them,
`onLine_of_collinear` and `foot_nearest`, come through `surrounds_sameSideOf`, which cites
them. The file's step that near a point off a straight line every point is on its side is
`surrounds_sameSideOf` said with a distance in place of a circle, and is proved from it.

## The angle at the centre of any size: III.20, III.21 and III.26 (#129)

**What Euclid does, and what Heath says of it.** III.20
([heath/III/20.md](../../heath/III/20.md)) proves the angle at the centre double of the
angle at the circumference: in his first figure "the whole angle BEC is double of the whole
angle BAC", in his second "the angle BEC which remains is double of the angle BDC". III.21
([heath/III/21.md](../../heath/III/21.md)) and III.26
([heath/III/26.md](../../heath/III/26.md)) rest on it. Heath's notes say how far it
reaches. Euclid "had no idea of III. 20 applying *in terms* … to the case where the angle
at the circumference, or the angle in the segment, is *obtuse*" (vol. 2, p. 48). Of III.21:
"Under the restriction that the 'angle at the centre' used in III. 20 must be less than two
right angles, Euclid's proof of this proposition only applies to the case of a segment
greater than a semicircle" (vol. 2, p. 49). And of III.26: "As in III. 21, if Euclid's
proof is to cover all cases, it requires us to take cognisance of 'angles at the centre'
which are equal to or greater than two right angles. Otherwise we must deal separately with
the cases where the angle at the circumference is equal to or greater than a right angle"
(vol. 2, p. 57).

**What `Elements/` does.** Our angles are always less than two right angles. So III.20 in
`Elements/`, [Elements/BookIII/Prop20.lean](../../Elements/BookIII/Prop20.lean), keeps the
centre on A's side of BC, where the angle at the centre is the angle BEC, and its route is
Euclid's. III.21 in `Elements/` gives Euclid's argument for the segment greater than a
semicircle and Robert Simson's completion for the rest, after Heath, for whom "The simplest
proof, of many, seems to be that of Simson" (vol. 2, p. 49). III.26 in `Elements/` takes
Heath's separate cases: it sorts
the angles at A and D as acute, right or obtuse (`Prop24.angle_type`), and takes Euclid's
argument for the acute, the diameters for the right, and III.22 for the obtuse, passing to
the acute angles in the other segments. Its clauses conclude that the circumferences are
congruent as well as equal in measure. The records of III.21 and III.26 give their routes
as modified.

**What the staged files do.** Prop20.lean adds a new object: the angle at the centre of a
circle α standing on the circumference BKC. It is defined as Euclid draws it in III.20's
first figure. Take a diameter AEF through the centre E, with A and F on opposite sides of
BC and F on K's side; the angle at the centre is the angles BEF and FEC together. It is a
magnitude of the angle kind, and may be two right angles or more; it uses no new primitive
and no axiom. Lean chooses one such diameter, as our measure of a circumference chooses one
angle, and the file proves that the choice does not matter.

```lean
noncomputable def angleAtCentre (α : Circle) (B K C : Point) : Angle :=
  Classical.epsilon fun x => ∃ E A F : Point, Centre E α ∧ OnCircle A α ∧ OnCircle F α ∧
    Between A E F ∧ OppositeSidesOf A K B C ∧ SameSideOf F K B C ∧ x = ∠ B E F + ∠ F E C
```

Its bridge to our angles: it does not depend on the diameter, on the centre, or on the point
K that names the side; it is the angle BEC when the centre lies across BC from K, two right
angles when the centre is on BC, and, when the centre lies on K's side, what makes four
right angles with the angle BEC, and so greater than two right angles. Then III.20 for every
angle at the centre, by Euclid's own proof: the diameter, the isosceles triangles and I.32,
then the sum of BEF and FEC (his first figure, which now covers the centre within the angle
BAC whether it lies on A's side of BC, on BC, or beyond it) or their difference (his
second). Its statement names no centre, for the angle at the centre is the circle's; the
proof takes the centre E by the rule, under Euclid's setting-out. From it the file derives
III.20 exactly as `Elements/` states it (its special case, which keeps the E its conclusion
uses), and shows that our measure of the circumference BKC is, in every case, the angle at
the centre standing on it. The file declares the three in the namespace of a changed main
theorem, as this report's opening says:

```lean
namespace Elements.BookIII.Staging

theorem Prop20 {A B C K : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hAK : OppositeSidesOf A K B C) :
    angleAtCentre ABC B K C = ∠ B A C + ∠ B A C

theorem Prop20.special {A B C E : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hEA : SameSideOf E A B C) :
    ∠ B E C = ∠ B A C + ∠ B A C

theorem Prop20.circumference (hB : OnCircle B α) (hC : OnCircle C α)
    (hK : Triangle B C K) : circumference α B K C = angleAtCentre α B K C
```

Prop21.lean then gives Euclid's two steps for every segment: the angles BAD and BED are
each half of the one angle at the centre standing on the circumference BCD, and halves of
one angle are equal; Simson's completion drops out. Under Euclid's "let the centre of the
circle ABCD be taken, and let it be F", the Lean takes F by the rule, as III.21 in
`Elements/` does; a remark in the staged file says that the general III.20 takes the centre
itself, that F is that centre, and that nothing below needs it named.

Prop26.lean gives Euclid's one argument for every case: equal angles at the
circumferences give equal angles at the centres, their doubles; the bases are equal by I.4;
the segments are similar and on equal straight lines, and so equal by III.24, which makes
them congruent, with their circumferences equal in measure (`Prop24.equalMeasure`); and the
circumferences that remain are equal in measure. The sorting of the angles drops out, and so
does the passage to the other segment by III.22 for the bases. That the circumferences that
remain are congruent as well, which each clause of III.26 in `Elements/` concludes, cannot
come by subtraction. The staged proof takes it as the proof in `Elements/` does, and labels
it under "therefore
the circumference BKC which remains is equal to the circumference ELF": at points X and Y of
the circles on the sides of K and L, the angles make two right angles with the equal angles
at A and D [III. 22], and so are equal; the segments there are similar, and on the equal
bases BC and EF they are congruent [III. 24]. Both files have the statements in `Elements/`
exactly, and end with Lean's check of that; so does Prop20.lean, for III.20's special
case.

**What remains of the departures.** Euclid's sentences are kept, and the Lean under each
does his step; what is new is the reading of his "angle at the centre" as an angle that may
be two right angles or more. That reading is ours, made after Heath's notes, and not
Euclid's: Heath says he "would not have recognised the 'angle' greater than two right
angles" (vol. 2, p. 48). Besides, the proof of III.20 cites I.13 and III.2, which Heath's
references for III.20 do not give: I.13 for the angles about the centre, and III.2 for the
point where the diameter crosses BC. III.20 still writes out the case Euclid leaves out, the
centre on AB or on AC, as the proof in `Elements/` does. III.26 keeps one division into
cases, at I.4, labelled where it stands: where the angles at the centres are two right
angles, BC and EF are diameters and there are no triangles for I.4; where they are greater,
I.4 applies to the angles BGC and EHF that remain of four right angles. For the congruence
of the circumferences that remain, III.26 takes III.22 and III.24 in place of Euclid's
subtraction, as the proof in `Elements/` does, labelled where it stands. And III.26's
statement takes the two pairs of equal angles one at a time, so that III.20 supplies the
other pair at the end, as in `Elements/`.

**What is new, and what is left.** New, a draft for the owner's approval, and not approved:
the definition of the angle at the centre with the theorems about it, III.20 in general, and
the theorem that a circumference is its angle at the centre. The staged proofs of III.20's
special case, of III.21 and of III.26 keep the statements in `Elements/`, but rest on the
draft, so they can replace the proofs there only once it is approved; the files say so. Then
the records of III.20, III.21 and III.26 are read again, and the gap catalogue's entries,
which tell of Simson's completion and of the separate cases, revised. One step of
Prop20.lean, that an angle of a triangle is less than two right angles, repeats a lemma
private to I.13's file, and on adoption should be cited from one home.

## The angle of contact after III.18 (#130)

**What Euclid says.** III.16 ([heath/III/16.md](../../heath/III/16.md)) draws AE at right
angles to the diameter AB from its extremity, and proves that "the angle of the semicircle
is greater, and the remaining angle less, than any acute rectilineal angle". III.18
([heath/III/18.md](../../heath/III/18.md)) proves that if a straight line touches a circle,
the straight line joined from the centre to the point of contact "will be perpendicular to
the tangent". So, after III.18, every straight line touching a circle is III.16's, and
III.16's angle of contact, with its comparisons, belongs to every one of them.

**What `Elements/` does.** The mixed angles are in `Elements/`: their words in
`Elements/Foundations/DefinitionsIII.lean`, and III.16's comparisons, in III.16's figure,
as its companions `Prop16.semicircle`, `Prop16.remaining` and `Prop16.acute`
([review/III/16.toml](../../review/III/16.toml)). The
[report on the mixed angles](mixed-angles-prototype.md), section 3, says that for a
straight line given only as touching the circle, that the angle of contact does not depend
on the straight line naming its branch is not proved, since the route would need III.18.

**What the staged file does.** AngleOfContact.lean cites the steps of III.16's
comparisons from `Elements/` (`Prop16.inside_sameSideOf`, `Prop16.horn_locallyEqual`,
`Prop16.horn_lt` and `Prop16.semicircle_gt`, in `Elements/BookIII/Prop16.lean`, with facts
of `Elements/BookIII/MixedAngles.lean` and `Elements/Figure/Regions.lean`), and proves none
of them again. What it adds is new. Let AE touch the circle ABC, with centre D, at A, and
let AD be produced beyond the centre to B. By III.18 the angle BAE is right, so AE is
III.16's straight line, and III.16's two parts hold for it. Then, in the words of the mixed
angles, for every straight line touching a circle:

- the angle of contact, read near A, does not depend on the straight line from A into the
  circle that names its branch of the circumference;
- it falls short of every acute rectilineal angle EAF placed at A along AE, on the
  circle's side;
- the angle of the semicircle exceeds every acute rectilineal angle BAF placed along the
  diameter, on E's side;
- both are angles as Euclid draws them, and every acute rectilineal angle can be placed at
  A for each comparison, by I.23.

An angle of contact is as Euclid draws it (well formed, in the word of the mixed angles)
when A is on the circle, AE touches it (Definition III.2), the ray AB passes within the
circle, and B is off AE.

```lean
theorem Prop18.contact_locallyEqual {A B B' E : Point} {ABC : Circle}
    (hm : (MixedAngle.ofContact A E ABC B).WellFormed)
    (hm' : (MixedAngle.ofContact A E ABC B').WellFormed) :
    LocallyEqual A (MixedAngle.ofContact A E ABC B).region
      (MixedAngle.ofContact A E ABC B').region

theorem Prop18.contact_lt {A B E F : Point} {ABC : Circle}
    (hm : (MixedAngle.ofContact A E ABC B).WellFormed) (hF : SameSideOf F B A E)
    (hEAF : ∠ E A F < ∟) : (MixedAngle.ofContact A E ABC B).FallsShort E F

theorem Prop18.semicircle_gt {A B D E F : Point} {ABC : Circle} (hD : Centre D ABC)
    (hA : OnCircle A ABC) (hAE : Touches A E ABC) (hADB : Between A D B)
    (hF : SameSideOf F E A B) (hBAF : ∠ B A F < ∟) :
    (MixedAngle.ofSegment A B ABC E).Exceeds B F
```

The first two name no centre, and take it by the rule; the third keeps D, through which its
diameter AB is drawn. The fourth statement is a theorem of its own in the file, after these
three; and three steps before them give the right angle at A, III.16's two parts for AE,
and the side of AE on which every branch lies.

**The route.** It is Euclid's order: III.18 makes the touching straight line III.16's, and
III.16's comparisons do the rest; nothing later than III.18 is cited. One departure
remains, labelled in the file: the comparisons are argued as the mixed angles argue them,
directly from III.16's second part, where Euclid argues by reductio. Nothing in the file
rests on Circle 2 or Circle 3. Five of its seven theorems rest on the rule that every
circle has a centre, through III.2 and the steps of `Elements/` they cite, and the two that
name no centre take theirs from it; the two steps that give the right angle at A and
III.16's two parts for AE do not rest on it.

**What is new, and what is left.** The statements after III.18 are new, a draft for the
owner's approval, and not approved. They are written in the words of the mixed angles in
`Elements/`: the mixed angle, its being well formed, local equality, exceeding and falling
short. Their home in `Elements/` is part of their approval.

## The calls to III.1 that do no work (#131)

*This section is analysis only.* It changes no file of Book III, and nothing of the Lean it
proposes has been compiled. Its figures are those of `Elements/` and `facts.json` at
e09f40f6, where `centre_unique` and `adjacent_eq_of_right` are theorems, not axioms. In the
figures below the first number of each pair is measured, read from `facts.json`. The
second is computed: a Lean walk of the dependencies, as Lean's collectAxioms walks them,
which takes the dropped call out of the proof that makes it and puts the rule in its place.
Run with nothing dropped, the walk gives each of the 137 entries exactly its `axioms` in
`facts.json`. "Checks", at the end, says at which revisions the figures were found, and why
they hold at e09f40f6 ("The figures of #131").

**The finding.** On main as at 2e8aecf, III.1 is called nine times in eight proofs: III.2,
III.4, III.8, III.14, III.17, III.35, III.36 (twice) and III.37. Train C6c removes four of
the nine, in III.35, III.36 (both) and III.37, where Heath gives no reference: they take the
centre by the rule. Train C6c also removes III.17's use of `centre_unique`, and III.1's
porism no longer calls III.1 or `centre_unique`, for it is argued directly from its given
centre. Train C6c keeps the five calls that stand under Heath's "[III. 1]", in III.2, III.4,
III.8, III.14 and III.17, his only references to III.1 itself in Book III (III.9 and III.10
cite its porism). None of the five does any work. Each proof keeps only the centre from what
III.1 returns: the rule gives one, and in III.14 the statement names the centre that III.1
is then shown to find. Keeping them is deliberate: [brief 0008](../briefs/0008-centre.md)
froze the rule "a bracket means III.1, none means the rule", its question 8 settled III.17,
and FORMALIZATION, section 3, says that "proofs cite III.1 where Heath does". Of the three
calls an earlier reading found doing work, two remain; the table marks them, and the third,
the porism's, is gone.

| Proposition | Call | Does work | On main, 2e8aecf | In `Elements/`, e09f40f6 | The route that drops it |
|---|---|---|---|---|---|
| III.2 | III.1, under "[III. 1]" | no | present | present | take D from the rule; a passage of the kind given |
| III.4 | III.1, under "[III. 1]" | no | present | present | take F from the rule; a given passage, which adds that "not through the centre", said of every centre, applies to it |
| III.8 | III.1, under "[III. 1]" | no | present | present | take M from the rule; a given passage; the route stays modified, for its I.24 step |
| III.14 | III.1 and `centre_unique`, under "[III. 1]" | no | present | present | delete both; the statement's E stands; the record's given passage, revised |
| III.17 | on main, III.1 and `centre_unique`, after a search for two points of the circle; on train C6c, III.1 run on a circle alone; under "[III. 1]" | no | present | present, as III.1 run on a circle alone | take E from the rule; the helper passage becomes a given one |
| III.35 | III.1, no reference | no | present | gone: the rule | nothing more |
| III.36 | III.1 twice, no reference | no | present | gone: the rule, in each case | nothing more |
| III.36 | `centre_unique`, at "let the centre E be taken" | **yes** | present | present | keep |
| III.37 | III.1, no reference | no | present | gone: the rule | nothing more |
| III.1's porism | III.1 and `centre_unique` | yes, on main | present | gone: argued directly | nothing more |
| III.1 run on a circle alone, a lemma | III.1 | **yes** | staged only | present | keep (brief 0008, question 6); once III.17's call goes, nothing in `Elements/` calls it |
| the lemma on aligned arcs | the rule twice and `centre_unique` six times | no, in substance | in `Staging/Stage3/Aligned.lean` only | present, in `Squares.lean` | optional, and untried: split on the arcs' kind first and use the centres it gives; no certified entry uses the lemma |

**Why the two marked calls do work.**

- **III.36's `centre_unique`.** The case split is Euclid's, on whether DCA passes through
  the centre, and it is said of every centre. Uniqueness turns "not through every centre"
  into "not through E". Moving the centre before the split would break Euclid's order; and
  `centre_unique` is a theorem on train C6c, proved in `Elements/Figure/Circles.lean`, not
  an axiom.
- **III.1 run on a circle alone.** It is III.1 for a circle with no points named, so its
  whole output is the centre found.

**Outside Book III's own proofs.** Book Zero's `EqualCircles.radii` and `Centre.every`, the
overlap audit and the crossing audit use `centre_unique` for uniqueness. That is work, and
out of scope here. III.9 and III.10 cite III.1's porism under "[III. 1, Por.]"; the porism
does work.

**What leaves the certificate.** These are the rules each entry rests on (its `axioms` in
`facts.json`), with the call dropped and the rule in its place. The drops chain: III.8
reaches III.1 through III.2 as well as by its own call, and III.37 reaches it through
III.17.

| Entry | At e09f40f6: measured, then computed | What leaves |
|---|---|---|
| III.2 | 61 to 59 | `exists_point_same_side`, `inside_not_on` |
| III.4 | 61 to 58 | `between_of_inside_chord`, `exists_point_same_side`, `inside_not_on`; I.18 and I.19 leave from beneath |
| III.8, and its companion, with III.2's drop (III.8's alone changes nothing) | 63 to 62 | `exists_point_same_side` |
| III.14, and its companion | 70 to 69 | the rule, `exists_centre` |
| III.15 | no change (70) | nothing: it rests on the rule through III.2 as well |
| III.17, and its companion | 63 to 61 | `between_of_inside_chord`, `exists_point_on_circle` (Points 7) |
| III.37 | 73 to 72 | `exists_point_on_circle` |
| III.35, III.36 | already done | |

`exists_point_same_side` and `inside_not_on` come into III.1 through `exists_off_line`, the
point off AB that I.11 needs there; `between_of_inside_chord` is III.1's own, and
`exists_point_on_circle` that of III.1 run on a circle alone, which takes two points of the
circle by it.

More widely: 45 entries rest on the rule that every circle has a centre, and 43 would after
the drops, for III.14 and its companion come off it entirely, as their statements, which
name E, would lead a reader to expect. 38 entries change, 31 of them only by losing
`exists_point_same_side`. III.1 sits beneath 42 entries besides itself, and would sit
beneath none; III.9 and III.10, and the entries that cite them, keep III.1's porism, which
no longer rests on III.1. So the change is small in the count of rules and large in the
dependency graph.

**The page, once a bracketed call goes.** The row of Heath's references still shows III.1,
and the Lean's citations no longer do. [GRAPH.md](../../GRAPH.md) names the references the
Lean does not cite: two of Heath's 86 in Book III on train C6c (III.5 in III.10, and III.10
in III.24). The five drops would make seven, as the page generator's own functions count
them on `facts.json` with III.1 taken from the five proofs' citations. A reference with no
call has precedents: III.24's [III. 10], under a passage note, and I.22's [I. 20]. III.29 is
a precedent only for taking a centre with no call, for Heath gives no reference there.

**The policy question, for the coordinator.** Brief 0008's rule, "a bracket means III.1,
none means the rule", keeps the five calls. Against it stands FORMALIZATION, section 5: "No
dummy citations. Never add a theorem call to make the Lean's dependencies match Heath's
references." Brief 0008 itself reasons so of III.10's last step, where splitting the cases
"cites III.5 only to match Heath's bracket, since the rule ends both cases, and
FORMALIZATION section 5 forbids that". For the rule, the same section says that "A checked
intermediate fact tied to a real sentence of Euclid is legitimate, even if the final proof
term could do without it", and that where the page promises Euclid's argument the Lean
follows "the propositions he uses". We
recommend dropping the five calls, each with a passage of the kind given: a passage of the
kind different would make four routes modified with no change in the reasoning. The
measurements on train C6c leave the recommendation as it was. The staged III.8 of #125
repeats the call of III.8 in `Elements/`, and the same change would apply to it. On 22
October 2026 the coordinator chose to drop the five calls, for a citation that does no work
counts against the argument, and gave the change to #131's own train, after this one,
which records the decision.

**Changes for later, once train C6c has landed.**

1. **The coordinator's decision first** ([WORKFLOW](../WORKFLOW.md), section 2,
   "Correcting a frozen brief"): a dated correction to brief 0008, replacing its rule in
   section 4 and its table, in the appendix row and in question 8, with FORMALIZATION,
   section 3's row for a circle's centre, and brief 0004's "Circles and their centres". No
   statement changes.
2. **A fresh measurement** of main once train C6c has landed (`lake build`, then
   `Certificate/Facts.lean`), as the baseline.
3. **One change to the Lean**, one owner to each file: III.14 first, which is a deletion;
   then III.2, III.4, III.8 and III.17, with the rule; then the imports of III.1's file
   that are no longer used, where the build allows; and, in the same change, every
   `#guard_msgs` pin of axioms downstream of III.2 and III.8 renewed. Seven of the pins in
   the crossing audit, `Audit/Crossing.lean`, list rules that would leave. Each renewal is
   read for the four names that brief 0008's question 7, as corrected, forbids.
4. **The records**: the five passages above, and III.15's note, which says that III.15
   rests on the rule through III.14 and III.2, and would then through III.2 alone. The
   records made stale are those of III.2, III.4, III.8, III.14 and III.17 (their Lean) and
   III.15 (its note); each is stamped by an independent reader, at the revision delivered.
5. **The prose**: the mishnah of III.2, III.14 and III.17; the paragraph of Book III's
   introduction on taking the centre; the gap catalogue's account of how proofs take a
   centre; the entry of `overlaps.md` on III.1's uniqueness corollary; and the reason given
   for III.2's expectation in
   [tests/certificate_expectations.json](../../tests/certificate_expectations.json) ("III.1,
   which it cites"), whose pinned value stands.
6. **The integrator** makes the pages, CERTIFICATE.md and GRAPH.md afresh.
7. **Optional**: the lemma on aligned arcs, as in the table; and, if the staged III.8 lands,
   the same change there.

**What could not be settled here.** The coordinator settled the policy on 22 October 2026:
#131's later train will drop the five bracketed calls. Their implementation and compiled
verification remain for that train. The second figure of each pair is computed by the walk,
not built from changed Lean. How far the audit pins shrink is inferred, for they are not in
`facts.json`; `lake build Audit` will tell.

## Checks

Each check below names the revision it ran on. The staged Lean is the same from e786ffc3
to e09f40f6: in that span no file of `Staging/`, `Certificate/` or the toolchain changes,
nor `Staging.lean`, and `Elements/` changes only in the proof of III.1's step
`Prop1.perpendicular`, with its docstring, and in doc comments of two other files, as
"The figures of #131", below, says. A later merge that changes no file of `Staging/`,
`Elements/` or `facts.json`, or the toolchain, leaves the outcomes of the Lean checks below
as they are, and one that does is checked again at the head the pull request lands. The
checks of style and links read the texts of the whole repository, so their counts move
with any merge; the pull request records the checks at the head it lands.

**Historical Lean execution at e09f40f6aae8b83ab70217f68a50b3b36ce6c6ff.** The retained
Lean evidence is the explicit build of the seven route modules, the separate elaboration
of their seven files, and the runs of RoutesCheck.lean and Cutoff.lean. The two scratch
files are given whole below with their SHA-256.

**Lean reproduction.** In a clean checkout of that revision, first run the two immutable
comparisons below. Save the complete Lean blocks below as RoutesCheck.lean and Cutoff.lean
at the worktree root, then run the remaining commands in order. These commands reproduce
the Lean evidence, not the editorial checks of the later report:

```sh
export PATH=$HOME/.elan/bin:$PATH
git diff e9bac7964aa1222d4fa3ca7c7a4a215abf7dbfc3 \
  e09f40f6aae8b83ab70217f68a50b3b36ce6c6ff -- Elements facts.json
git diff e9bac7964aa1222d4fa3ca7c7a4a215abf7dbfc3 \
  e09f40f6aae8b83ab70217f68a50b3b36ce6c6ff --stat
lake build Staging.Routes.Prop08 Staging.Routes.Prop20 Staging.Routes.Prop21 \
  Staging.Routes.Prop26 Staging.Routes.Prop27 Staging.Routes.Touching \
  Staging.Routes.AngleOfContact
for f in Prop08 Prop20 Prop21 Prop26 Prop27 Touching AngleOfContact; do
  lake env lean Staging/Routes/$f.lean
done
lake env lean RoutesCheck.lean
lake env lean Cutoff.lean
```

Every retained Lean validation command exited 0. Each of the seven files, elaborated alone,
gave no message at all, so the five type equalities they end with hold. The build of the
seven modules had no warning from `Staging/Routes/`; its only warnings are the two unused
variables at lines 165 and 166 of `Elements/Figure/Circles.lean`. The build and the two
scratch modules reported, in order:

```text
Build completed successfully (107 jobs).
routes_check: 7 modules, 51 declarations, 38 theorems, 5 type equalities, 7 contact roots, 1476 constants walked beneath them, 0 findings
Book III modules reached from the contact roots: [Elements.BookIII.Prop16,
 Elements.BookIII.Prop02,
 Elements.BookIII.Prop01,
 Elements.BookIII.Prop18,
 Elements.BookIII.MixedAngles]
modules reached: [Elements.BookIII.MixedAngles,
 Elements.BookIII.Prop01,
 Elements.BookIII.Prop02,
 Elements.BookIII.Prop16,
 Elements.BookIII.Prop18,
 Staging.Routes.AngleOfContact]
cutoff_check: 7 roots, 1462 constants walked, 0 findings
```

**Historical editorial validation at
11bcfea5ddde58341627a76cf0dab242fd320951.** That commit has
e09f40f6aae8b83ab70217f68a50b3b36ce6c6ff as its parent and changes this report alone, so
it identifies exactly the later report text that the two full-repository editorial checks
read. At that commit `python3 scripts/check_style.py` reported `✓ style: the hard rules
hold (S1–S26)`, and `python3 scripts/check_links.py` reported `✓ links: all 14096 relative
links and anchors in 485 Markdown files resolve`. Those are historical results for that
committed report, not results reproduced by the clean e09f40f6 checkout above.

**Report validation after 11bcfea5.** At 4186e342ae9d66c7a36d32c8866c42280bbe57a0, with
this report as the only working-tree modification, the review correction ran:

```sh
git diff --check -- docs/reports/routes-book-III.md
python3 scripts/check_links.py docs/reports/routes-book-III.md
```

Both commands exited 0. The first gave no output; the second reported `✓ links: all 36
relative links and anchors in 1 Markdown files resolve`. No style check was run on that
working-tree version.

At c8e23b2ee329752b71674e544b396986e8a829c0, with the report version later committed at
14a18ce7418d29f90a0e57af37f784860003db16 as the only working-tree modification, the
documentation step ran the same two commands and `python3 scripts/check_style.py
--no-lean`. All three exited 0. The first gave no output; the second reported `✓ links: all
36 relative links and anchors in 1 Markdown files resolve`; the third `✓ style: the hard
rules hold (S1–S11 and S13–S26)`. That run skips S12, which asks Lean and needs `Elements`
built, and no build was made for it, so S12 was last run on this report at 11bcfea5.

RoutesCheck.lean takes its list from Lean's environment, not from a list written by
hand: every declaration of the seven modules, 51, and among them the 38 theorems, those
neither private nor internal. Each finding is an error, so that `lake env lean` fails on
any. It finds any of the 51 declared as an axiom, and puts each to Lean's collectAxioms,
finding `sorryAx`,
Circle 3 (`Tacit.outside_of_between`), and any axiom that is neither one of Lean's three
nor declared under `Elements/Foundations/`. It walks every constant beneath the 38
theorems, statements and proofs, and finds Circle 2 (`Tacit.inside_of_between`, a theorem
proved from Circle 3) or Circle 3 if either is reached. It finds any of the five
staged theorems, for III.8, III.20's special case, III.21, III.26 and III.27, whose type is
not identical to that of the theorem in `Elements/`, binder names and binder kinds
included, with the same universe parameters: a stricter test than the `rfl` that closes
each file. And it walks every constant beneath the seven theorems of AngleOfContact.lean,
finding any of a proposition of Book III later than III.18 (in its module, or under its
name) or staged in another file, and lists the modules of Book III reached. So, at
e09f40f6 as at bd69bb9b (below), none of the 38 theorems uses `sorry`, none of the seven
files declares an axiom, nothing in them rests on an axiom beyond the foundations and
Lean's three, or on Circle 2 or Circle 3, the five staged theorems have exactly the types
of the theorems in `Elements/`, and nothing beneath the angle of contact is later than
III.18: the modules of Book III reached are those of III.1, III.2, III.16, III.18 and the
mixed angles.

Cutoff.lean, the cutoff walk of the run at 9a0f8ba1 below, walks every constant beneath
the seven theorems of AngleOfContact.lean, statements and proofs, and finds any in the
module of a proposition of Book III later than III.18, or in
`Elements/BookIII/Circumferences.lean`, whose steps cite III.20 to III.22. It walks as
RoutesCheck.lean does, but for the constructors of each inductive type it meets, which
that module adds and this one does not: with them added, it too walks 1476 constants. So
1476 and 1462 are counts of two walks, not of a change. A third scratch module, walking
beneath all 51 declarations in the same way, found none of Book Zero's three lemmas
Triangle.of_onCircle, exists_onCircle_oppositeSidesOf and exists_onCircle_sameSideOf
beneath them, and Circle 3 among the axioms of each: so the sentence 5fca8529 writes in
[docs/reports/overlaps.md](overlaps.md), that the staged theorems reach none of the three,
holds. These checks built nothing beyond the seven modules and what they import. The style
check's rule S12, which asks Lean, importing `Elements`, whether each name in backticks
exists, read the modules the seven reach as built at e09f40f6, and the rest of
`Elements/` and `Audit/` as built at 9a0f8ba1: they declare the same names, for since then
`Elements/` has changed only in the proof of `Prop1.perpendicular` and in doc comments, and
`Audit/` in a doc comment.

RoutesCheck.lean, whole (SHA-256
358bcbd39808bfa4b690395d8b183a53ddbf8240bd07fdc92b548a7ad8846a0c):

```lean
import Lean
import Staging.Routes.Prop08
import Staging.Routes.Prop20
import Staging.Routes.Prop21
import Staging.Routes.Prop26
import Staging.Routes.Prop27
import Staging.Routes.Touching
import Staging.Routes.AngleOfContact

open Lean Elab Command

/-- Every constant beneath `n`, statement and proof, walked as Lean's collectAxioms walks. -/
partial def walk (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  let some ci := env.find? n | return
  let mut next := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then next := next ++ v.getUsedConstants
  if let .inductInfo v := ci then next := next ++ v.ctors.toArray
  for c in next do walk env c

def beneath (env : Environment) (roots : Array Name) : NameSet :=
  ((roots.forM (walk env)).run {}).2

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

/-- `k`, when `n` is `Elements.BookIII.Propk` or a name under it. -/
def bookIIIProp? (n : Name) : Option Nat :=
  match n.components with
  | e :: b :: p :: _ =>
    let s := p.toString
    if e == `Elements && b == `BookIII && s.startsWith "Prop" then (s.drop 4).toNat? else none
  | _ => none

run_cmd do
  let env ← getEnv
  let circle2 := `Elements.Tacit.inside_of_between
  let circle3 := `Elements.Tacit.outside_of_between
  let pairs : List (Name × Name) :=
    [(`Elements.BookIII.Routes.Prop8, `Elements.BookIII.Prop8),
     (`Elements.BookIII.Staging.Prop20.special, `Elements.BookIII.Prop20),
     (`Elements.BookIII.Routes.Prop21, `Elements.BookIII.Prop21),
     (`Elements.BookIII.Routes.Prop26, `Elements.BookIII.Prop26),
     (`Elements.BookIII.Routes.Prop27, `Elements.BookIII.Prop27)]
  for n in [circle2, circle3] ++ pairs.map (·.1) ++ pairs.map (·.2) do
    unless env.contains n do throwError "{n} is not declared"
  let mods := env.header.moduleNames.filter (`Staging.Routes).isPrefixOf
  let mut decls : Array Name := #[]
  for m in mods do
    let some i := env.getModuleIdx? m | throwError "{m} is not imported"
    decls := decls ++ env.header.moduleData[i.toNat]!.constNames
  let theorems := decls.filter fun n =>
    !isPrivateName n && !n.isInternal && env.find? n matches some (.thmInfo _)
  let mut findings : Array MessageData := #[]
  for n in decls do
    if env.find? n matches some (.axiomInfo _) then
      findings := findings.push m!"{n} is declared as an axiom"
    for a in ← collectAxioms n do
      if a == ``sorryAx then findings := findings.push m!"{n} uses sorry"
      else if a == circle3 then findings := findings.push m!"{n} rests on Circle 3"
      else unless [``propext, ``Classical.choice, ``Quot.sound].contains a ||
          (`Elements.Foundations).isPrefixOf (moduleOf env a) do
        findings := findings.push m!"{n} rests on {a}, outside the foundations"
  let under := beneath env theorems
  for n in [circle2, circle3] do
    if under.contains n then findings := findings.push m!"{n} lies beneath the theorems"
  for (s, e) in pairs do
    let some a := env.find? s | unreachable!
    let some b := env.find? e | unreachable!
    unless a.type.equal b.type && a.levelParams == b.levelParams do
      findings := findings.push m!"{s} and {e} differ in type"
  let contact := theorems.filter (moduleOf env · == `Staging.Routes.AngleOfContact)
  let below := beneath env contact
  let mut reached : NameSet := {}
  for n in below.toList do
    let m := moduleOf env n
    if (`Elements.BookIII).isPrefixOf m then reached := reached.insert m
    if (bookIIIProp? m).any (· > 18) || (bookIIIProp? n).any (· > 18) then
      findings := findings.push m!"{n}, in {m}, is later than III.18"
    if (`Staging).isPrefixOf m && m != `Staging.Routes.AngleOfContact then
      findings := findings.push m!"{n}, in {m}, is staged elsewhere"
  for f in findings do logError f
  logInfo m!"routes_check: {mods.size} modules, {decls.size} declarations, \
    {theorems.size} theorems, {pairs.length} type equalities, {contact.size} contact roots, \
    {below.size} constants walked beneath them, {findings.size} findings\n\
    Book III modules reached from the contact roots: {reached.toList}"
```

Cutoff.lean, whole (SHA-256
aaf0e04f8d468c16cb1a7eded373104c34e6c2485ba813fb816c356f8a35367d):

```lean
import Lean
import Staging.Routes.AngleOfContact

/-! Scratch check, outside the repository: walk every constant beneath the seven theorems of
`Staging/Routes/AngleOfContact.lean` (statements and proofs) and list the Book III modules
they come from. A module `Elements.BookIII.PropNN` with NN > 18, or
`Elements.BookIII.Circumferences` (steps citing III.20-III.22), is a finding. -/

open Lean Elab Command

def roots : List Name :=
  [`Elements.BookIII.Routes.Prop18.diameter, `Elements.BookIII.Routes.Prop18.parts,
   `Elements.BookIII.Routes.Prop18.branch, `Elements.BookIII.Routes.Prop18.contact_locallyEqual,
   `Elements.BookIII.Routes.Prop18.contact_lt, `Elements.BookIII.Routes.Prop18.semicircle_gt,
   `Elements.BookIII.Routes.Prop18.acute]

def laterThan18 (m : Name) : Bool :=
  let s := m.toString
  if s == "Elements.BookIII.Circumferences" then true
  else if s.startsWith "Elements.BookIII.Prop" then
    match (s.drop "Elements.BookIII.Prop".length).toNat? with
    | some n => n > 18
    | none => false
  else false

elab "#cutoff_check" : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots.toArray
  for r in roots do
    unless env.contains r do logInfo m!"MISSING ROOT {r}"
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut used := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      used := used ++ v.getUsedConstants
    for c in used do
      unless seen.contains c do todo := todo.push c
  let mut mods : NameSet := {}
  let mut bad : Nat := 0
  for n in seen.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if (`Elements.BookIII).isPrefixOf m || (`Staging).isPrefixOf m then
      mods := mods.insert m
    if laterThan18 m then
      logInfo m!"LATER {n} ({m})"; bad := bad + 1
  logInfo m!"modules reached: {mods.toList.map toString |>.toArray.qsort (· < ·)}"
  logInfo m!"cutoff_check: {roots.length} roots, {seen.size} constants walked, {bad} findings"

#cutoff_check
```

**At bd69bb9b5e6790e00e9c25d8417b6d1898446733.** 70108dd0 records these checks, run in this
order from the root of a clean checkout of that commit, with nothing uncommitted and no
build of its own before them: the build of the seven modules, each file elaborated alone,
`lake build Staging`, and RoutesCheck.lean. The build, the seven files and the module
reported what they report at e09f40f6, above, and `lake build Staging` completed (109 jobs)
with the same two warnings of `Elements/Figure/Circles.lean` and no other. Then, with
70108dd0's edits to this report in place, `lake build Elements` completed (153 jobs), and
`scripts/check_style.py` and `scripts/check_links.py` passed, the second reporting
`all 14071 relative links and anchors in 484 Markdown files resolve`. Three copies of the
module, run on the same build after it and then deleted, showed what it finds. The first
printed the names of the 38 theorems: one each in `Prop08.lean` and Prop21.lean, two each
in Prop26.lean and `Prop27.lean`, eleven in Prop20.lean, four of them in the namespace
of a changed main theorem, fourteen in Touching.lean and seven in AngleOfContact.lean.
The second added Circle 2 to the theorems walked and III.20 of `Elements/` to the roots of
the angle of contact, Circle 2 and Circle 3 to the declarations put to collectAxioms, and
paired the staged III.8 with III.8's general companion. It gave the seven findings those
seeds call for: Circle 2 and Circle 3 beneath the theorems, Circle 3 declared as an axiom,
Circle 3 beneath each of the two, the types unlike, and III.20 later than III.18. The third
added a theorem resting on a new axiom and one proved by `sorry`, and gave a finding for
each.

**At 9a0f8ba1, with the edits that e786ffc3 commits.** The edits change no declaration:
they delete from Touching.lean its import of I.12, which nothing in the file used;
correct a sentence of its docstring and one of the doc comment of `Staging.lean`; and
change this report. On that tree er_check.sh, a scratch script outside the repository,
built the seven modules and put the 38 theorems to Lean's collectAxioms, looking for what
the scratch module at 80e85ec6, below, looks for. It reported:

```text
Build completed successfully (107 jobs).
routes_check: 38 theorems, 0 findings
```

`lake build Staging` completed (109 jobs) with no warning from `Staging/Routes/`; its only
warnings are the two unused variables at lines 165 and 166 of
`Elements/Figure/Circles.lean`. Each of the seven files, elaborated alone with `lake env
lean`, gave no message at all, so the five type equalities they end with hold.
Cutoff.lean, above, found no proposition of Book III later than III.18 beneath the seven
theorems for the angle of contact, and reached the modules of Book III it reached at
80e85ec6:

```text
cutoff_check: 7 roots, 1462 constants walked, 0 findings
```

It walked 520 at 80e85ec6, and gives 520 again when run there. The difference is the merge
60dc26e0: I.4 and I.8, beneath the angle of contact, are now proved by the restricted rule
of superposition, and 289 of the 1462 constants are in its modules, while 776 are Lean's
own, where 193 were. Then `scripts/check_style.py` and `scripts/check_links.py` passed:

```text
✓ style: the hard rules hold (S1–S26)
✓ links: all 14061 relative links and anchors in 484 Markdown files resolve
```

**At 80e85ec6, the Lean as delivered then.** The seven modules were built, and a scratch
module outside the repository put every theorem they declare, other than the private steps
the others use, to Lean's collectAxioms. It looks for `sorryAx`; for an axiom declared
outside `Elements/Foundations/` other than Lean's own three (`propext`, `Classical.choice`,
`Quot.sound`); and for Circle 3, which Circle 2 now rests on, so that it finds both. It
reported:

```text
Build completed successfully (102 jobs).
routes_check: 38 theorems, 0 findings
```

So none of the 38 uses `sorry`, none rests on an axiom beyond the foundations and Lean's
three, and none rests on Circle 2 or Circle 3. Then:

```sh
export PATH=$HOME/.elan/bin:$PATH
lake build Staging
lake env lean Staging/Routes/Prop08.lean    # and each of the other six files
```

`lake build Staging` completed (110 jobs) with no warning from `Staging/Routes/`; its only
warnings are the two unused variables at lines 165 and 166 of
`Elements/Figure/Circles.lean`. Each of the seven files, elaborated alone, gave no message
at all. So the checks that five of them end with hold: the staged theorems for III.8,
III.20's special case, III.21, III.26 and III.27 have exactly the types of the theorems in
`Elements/` (`type_of%` on each side, closed by `rfl`). Last, a scratch walk of every
constant beneath the seven theorems for the angle of contact, statements and proofs, found
no proposition of Book III later than III.18; the modules of Book III it reached are those
of III.1, III.2, III.16, III.18 and the mixed angles:

```text
cutoff_check: 7 roots, 520 constants walked, 0 findings
```

At 80e85ec6, `scripts/check_style.py` failed on six names in this report that Lean,
importing `Elements` alone, does not know: the staged names written in backticks, and
Lean's collectAxioms. This report writes them in words or in code blocks, and the style
check passes on it (above, at 11bcfea5).

**At bd9c4b76, in the code review.** The reviewer ran the same build and axiom check, with
the same result but for the count of jobs (101), found no warning from `Staging/Routes/` in
`lake build Staging`, had Lean close the five type equalities in a scratch file, and walked
the dependencies for anything later than its proposition: III.27 reaches III.26 at most,
and the angle of contact III.18. `scripts/check_style.py` and `scripts/check_links.py`
passed there.

**At a7724676, in the pre-merge validation** (WORKFLOW, section 10). It built the seven
modules with III.21, III.26 and III.27 of `Elements/` (102 jobs, with no warning from
`Staging/Routes/`). A temporary scratch module, deleted after the run, closed the five type
equalities by `rfl`, put the 38 theorems to Lean's collectAxioms as above, and walked the
proof terms beneath the seven theorems for the angle of contact for a proposition of
Book III later than III.18. It reported:

```text
routes_check: 38 theorems, 5 type equalities, 7 contact cutoffs, 0 findings
```

**At 86c5748d, after the first readers' findings.** The seven files were built with `lake
build Staging`, with no warning from any of them, and the axiom check, run on the six
modules that import them, reported 101 jobs and 38 theorems with no findings. There were 57
before the port; the 19 copies of facts now in `Elements/` went with it. A scratch file
closed the five type equalities, and found nothing later than III.18 beneath the theorems
for the angle of contact. c868a9fc changed Prop20.lean and Prop26.lean after it.

**The figures of #131.** At 9f8c8adb, whose `Elements/` was train C6c's as at 80292b0a,
`lake build` and `lake env lean Certificate/Facts.lean` wrote a `facts.json` identical to
the one committed, which the figures of #131 read; the walk behind the computed figures
agrees with it on all 137 entries. These measurements replaced the estimate of an earlier
version of #131, made from main at 2e8aecf and an earlier train C6c (d3e9a8c).

At 9a0f8ba1 the measurement was made again, for the merge 60dc26e0 had brought to
`Elements/` main's restricted rule of superposition, with I.4 and I.8 proved by it, and
changed no file of `Elements/BookIII/`. `lake build` completed (153 jobs), and `lake env
lean Certificate/Facts.lean` reported:

```text
certificate: 99 propositions, 3 porisms and 35 companions written to facts.json, with 80 axioms and 242 words of the vocabulary they and the entries are stated in
```

The `facts.json` it wrote is, byte for byte, the one committed at 9a0f8ba1; the files the
run writes were then restored, and none was left changed. Compared with the one at
9f8c8adb, each of the 137 entries has the same `axioms`; what changes is the vocabulary
(125 words, now 242), the type of the rule of superposition, and, for I.4 and I.8 alone,
the record of which rules each proof calls itself and through which steps it reaches the
others. A scratch walk outside the repository gives, with nothing dropped, each entry
exactly its `axioms` there, and with the five calls dropped every computed figure of #131:
each pair of the table, the rules that leave, III.8's call alone changing nothing, the 45
entries on the rule and 43 after, the 38 that change and the 31 of them that lose only
`exists_point_same_side`, and the 42 entries beneath III.1 and none after. The page
generator's own functions, run on that `facts.json`, give two of Heath's 86 references in
Book III uncited, III.5 in III.10 and III.10 in III.24, and seven with III.1 taken from the
citations of the five proofs. The third code review ("Who read what") ran the certificate
and the walk again at bd69bb9b, whose `Elements/` and `facts.json` are those of 9a0f8ba1,
and found the same.

At e09f40f6 neither the certificate nor the walk, which imports all of `Elements`, was run
again, for these checks built no more than the seven modules; the figures hold there all
the same. The `facts.json` committed at e09f40f6, which is train C6c's, gives each of the
137 entries exactly the `axioms` it has at 9a0f8ba1, so every measured figure stands, and
45 entries rest on the rule, as before. It differs from the one at 9a0f8ba1 only in what
five entries, III.1, its porism, III.16, III.17 and III.19, record of the steps through
which they reach their rules, line numbers of steps in III.1's file among them, and, for
III.1 and its porism, of the rules their proofs call themselves. The Lean of `Elements/`
differs only in doc comments and in the proof of III.1's step `Prop1.perpendicular`, that
at a point of a straight line only one straight line is at right angles to it, which now
takes the right angle beside a right angle by I.13 and C.N. 3, where it called the theorem
`adjacent_eq_of_right`. A scratch module that sets the old proof beside the new, in one
environment, finds the same 58 axioms beneath each by Lean's collectAxioms. No dropped call
lies beneath that step, so the walk finds beneath every entry, with the calls dropped or
not, the axioms it found at 9a0f8ba1, and every computed figure stands. Run on that
`facts.json` with `scripts/render.py` as it is at e09f40f6, the page generator's functions
give again 86 references and two uncited, as [GRAPH.md](../../GRAPH.md) says, and seven
with the five calls dropped.

**Who read what.**

- **Before the port.** On main's statements as at 2e8aecf, an independent reader read each
  file against Heath's text, and a code review read the whole branch at 4504fa48, answered
  at 4cd7c77d.
- **The port.** Three independent readers, who wrote none of it, read it against Heath's
  text where a file has his sentences and against train C6c's tree: one `Prop08.lean` and
  `Prop27.lean`, and another Touching.lean and AngleOfContact.lean, at 4a6d9a49; the
  third Prop20.lean, Prop21.lean and Prop26.lean, at 9f8c8adb. Each passed it with
  minor findings. 86c5748d answers the first two (a remark wanted under III.26's step in
  III.27, the unused hypothesis that the circles are two in the step from the straight line
  through the centres, and docstrings that named a centre the statement no longer has or
  told the history of the move), and adds a remark on F in III.21, which the third reader,
  reading 9f8c8adb, asked for independently. c868a9fc answers the third's other two: III.20
  and III.26 import what they cite, and III.26's docstring says that the segments are
  similar.
- **The code review.** After this report was rewritten (78b3d913, bd9c4b76), an
  independent code review read the whole branch at bd9c4b76, against the repository's
  standards and the six issues. It found the five staged proofs of statements in
  `Elements/` exact, each route as its issue asks, and every figure of #131 it checked
  right. Its material findings were a fact of the mixed angles proved again in
  Touching.lean, checks and readings in this report not tied to the revision delivered,
  and a miscount of the coordinator's questions in the decisions entry. 80e85ec6 answers
  four of its findings on the Lean (that fact, now cited from `Elements/`; "main's" in the
  Lean; Heath's note on III.26 quoted on III.27's page; and the type checks), and 7d9ffaed
  those on the report and the decisions entry. Two of its minor findings, both in the
  Lean, were left open then. e786ffc3 answers one: the header of
  Touching.lean called Intersections 8 and 9, which are construction rules, diagram
  rules, and now names both kinds. The other is kept by choice: the staged III.21 takes the
  centre F under Euclid's sentence, as III.21 in `Elements/` does, and uses it nowhere
  below, and a remark in the file says why; the second code review found the remark true.
- **The pre-merge validation** (WORKFLOW, section 10). It completed at e225a060; its Lean
  checks are those above at a7724676, and its lint did not catch the six names that
  `scripts/check_style.py` rejects (above, at 80e85ec6). Its commits: a7724676, which put
  III.20 in general and the three theorems named after it in the namespace of a changed
  main theorem, with the files that cite them, and wrote the sentence on the prototype that
  7d9ffaed replaced; 09a88a7b, its record of those checks; and e225a060, a sentence on
  review status, which 7d9ffaed replaced.
- **The second code review.** An independent code review read the delta from bd9c4b76 to
  7d9ffaed, which holds the three commits of the pre-merge validation, 80e85ec6 and
  7d9ffaed, and the merge 60dc26e0. It found the earlier findings answered, but for the two
  minor ones above, and the renaming of III.20 in general and its three theorems
  consistent, with no type changed. Its own findings, one material and four minor, are
  answered by e786ffc3: three sentences of this report that the
  merge had made false, with checks that all predated the merge (the opening, #131 and
  "Checks"); the import of I.12 in Touching.lean, which nothing used; two sentences of
  this list; and a sentence of `Staging.lean` on its folders.
- **The pre-merge validation at bd69bb9b** (WORKFLOW, section 10). Its review found that
  "Checks" tied the evidence for the revision delivered to 9a0f8ba1 and to edits it did not
  name, with no command of its scratch checks written out. 70108dd0, a follow-up to
  bd69bb9b in documentation only, answers it, and changes this report alone: the checks at
  bd69bb9b, with the module they ran given whole, an account of the merges after 9a0f8ba1
  in this report's opening and under #131, and e786ffc3 named where the text meant it. Its
  tests, run at 70108dd0, found the seven modules building and none of what the checks
  above look for. Its documentation step found that this branch had made false the
  sentence of [docs/reports/overlaps.md](overlaps.md) on staged work, and 5fca8529, as the
  coordinator directed, changes that sentence alone: `Staging/Routes/` holds seven Lean
  files, whose theorems rest on neither Circle 2 nor Circle 3, and so reach none of Book
  Zero's three lemmas that rest on Circle 2. The writer of this report's later edits, who
  wrote neither commit, read both in full. 5fca8529's sentence holds at e09f40f6
  ("Checks"). Of
  70108dd0's text, this report's later edits replace the account of the merges by what
  holds at every merge (the opening), drop the scratch path it gave for the module, which
  is given whole above, and correct its sentence that the scratch modules of the earlier
  runs were not kept: the cutoff walk's was, and is given whole above too.
- **The third code review.** An independent code review read e786ffc3 and the merges
  33236005 and bd69bb9b, at bd69bb9b, and ran its checks again there, the certificate and
  the walk of #131 among them. It found the second review's findings answered and every
  claim of e786ffc3 true, and two findings of its own: a material one, of stale revision
  ties, for the merges after e786ffc3 had made false this report's account of the merges
  and the revision it tied its checks to; and a minor one, the chronology of the remark on
  F, above. This report's later edits answer both: the opening says what holds of
  `Elements/` and `facts.json` at every merge, in place of an account of each merge; #131
  gives its figures at e09f40f6; "Checks" ties each check to the revision it ran on; and the
  remark on F is told in the order it came.
- **The fourth code review.** An independent code review read the merge e09f40f6 and this
  report at 11bcfea5, against the repository's standards and the six issues, and ran its
  Lean checks again there. It found the merge resolved as stated, `Elements/` and
  `facts.json` those of train C6c, every claim it checked true, and nothing blocking; its
  six minor findings are proposed for a follow-up issue, and hold nothing here.
- **Not yet read independently.** The pre-merge validation's three commits after 11bcfea5
  (4186e342, c8e23b2e and 14a18ce7), which change this report alone and were read in full
  before they were accepted; the merges e32f4bed and a63196b4, which change no file of this
  branch but the decisions page, from which a63196b4 takes the routes bullet; the entry
  file that holds it now, in the same words, and the sentence of the opening that says so;
  the merges cb942da7 and 0afcc617, which change no file of this branch, the second
  bringing train C6c onto this branch through main; the record of the coordinator's
  answers of 22 October 2026 in the entry file, `Staging.lean` and this report; and this
  list's last two entries.

## Addendum: III.8 and III.27 moved into `Elements/`

*22 October 2026.*

Card #332 moved the routes for III.8 and III.27 into
[Elements/BookIII/Prop08.lean](../../Elements/BookIII/Prop08.lean) and
[Elements/BookIII/Prop27.lean](../../Elements/BookIII/Prop27.lean). Their statements and
`--` lines did not change. The declarations changed namespace, and the checks that their
types matched the theorems in `Elements/` left with the staged copies, since each moved
proof is now that theorem. `Prop27.sides` moved with III.27, whose file now imports III.22
and III.24. The historical table above keeps the staged filenames as its labels and links
them to commit fc3dffa892a32be571c28b208dfb40189226db93, where both files remain.

The route of III.8 now uses Euclid's order for points on the same circumference, while
I.24 remains for points on different circumferences and for a point of contact. The route
of III.27 now uses Euclid's reductio and halving for the acute case, III.22 for the obtuse
case, and the angle in a semicircle for the right case. Both routes therefore remain
modified. The gap catalogue and the mishnah of each proposition now give those limits,
and the generated pages, certificate, graph and facts were made afresh after the move.

**On branch lean/promote-routes-332 at 10b9ccee with this train's edits** (22 October 2026,
card #332, the move of III.8 and III.27 into `Elements/`). Before the staged copies were
deleted, they were built against the moved files, and their two type equalities closed by
`rfl` once more. Then `lake build Elements.BookIII.Prop08 Elements.BookIII.Prop27 Staging`
completed (107 jobs), as did `lake build Elements` (185 jobs) and the three audit modules
that import `Elements` (187 jobs, every pin holding). The moved files gave no warning, and
no message at all elaborated alone, and hold no `sorry` and no command that FORMALIZATION,
section 7, forbids; the only warnings were the four unused variables of
`Elements/Figure/Circles.lean` and `Elements/BookIII/Prop31.lean`, which import neither.
`python3 scripts/check_style.py` and `python3 scripts/check_links.py` passed (`✓ style: the
hard rules hold (S1–S26)`; `✓ links: all 14247 relative links and anchors in 504 Markdown
files resolve`), and `python3 scripts/check_fidelity.py` found two problems alone: the
stamps of the records of III.8 and III.27, whose Lean has changed, are stale until those
records are read again.

These commands, the imports of RoutesCheck.lean above and its pairs for III.8 and III.27,
and the runs above that name `Staging/Routes/Prop08.lean` or `Prop27.lean`, are those of
the files as they stood at the revisions given. Both files have since moved into
`Elements/BookIII/Prop08.lean` and `Prop27.lean`, and the staged copies are gone, so these
commands reproduce at those revisions only.

## Addendum: the five calls of III.1 dropped (#131)

*22 October 2026.*

#131's own train drops the five calls, by the coordinator's
[decision entry of that day](../decisions/2026-10-22-iii1-calls-dropped.md), which
records the decision and corrects brief 0008 (item 1 of "Changes for later", above). In
`Elements/BookIII/`:

- III.2 (`Prop02.lean`) takes the centre D from `Tacit.exists_centre` where it called
  III.1;
- III.4 (`Prop04.lean`) takes F from the rule, and its conditions said of every centre
  apply to it;
- III.8 (`Prop08.lean`, Euclid's route since the addendum above) takes M from the rule,
  and its condition that every centre lies between G and A applies to it;
- III.14 (`Prop14.lean`) loses its call of III.1 and of `centre_unique`, and takes no
  centre, for its statement names E;
- III.17 (`Prop17.lean`) takes E from the rule where it called `Prop1.of_circle`.

Every `--` line and every statement is as it was. None of the five files imports III.1's
file now; III.1 and `Prop1.of_circle` stay, and no proof in `Elements/` calls either but
`Prop1.of_circle`'s own call of III.1.
`lake build Audit` then failed on eleven pins and on no other, and each was renewed from
Lean's own message: in `Audit/Crossing.lean`, the pins of `Audit.III_5_today`,
`Audit.III_6_today`, `Audit.III_11_today`, `Audit.III_13_today`, of the crossing bridge
and its step (since 26 October 2026 `Elements.CirclesCut.of_meet` and
`Elements.CirclesCut.cut_point`, pinned there still) and of `Audit.within_point`; in `Audit/Overlaps.lean`, those of
`Audit.III_26_any`, `Audit.III_27_any`, `Audit.III_24_measure` and
`Audit.III_30_measure`. Each lost one name, `Tacit.exists_point_same_side`, and gained
none. The pin of `Audit/Centre.lean` holds unchanged.

The certificate, run again on this train's revision (item 2), measures what the walk
computed in the second table above: III.2 from 61 rules to 59, III.4 from 61 to 58, III.8
and its companion from 63 to 62, III.14 and its companion from 70 to 69, III.15
unchanged at 70, III.17 and its companion from 63 to 61, and III.37 from 73 to 72; 45
entries on the rule and 43 after; 38 entries changed, 31 of them only by losing
`exists_point_same_side`; and no entry now cites III.1, where five did. The records of
III.2, III.4, III.8, III.14 and III.17, and III.15's note, were read again and stamped by
independent readers. Under Heath's "[III. 1]" in III.2, III.4, III.8 and III.17 the
centre now comes from the rule, so each of those passages is one argued another way, and
the routes of III.2, III.4 and III.17 are modified by that one step, as "The policy
question" foresaw; III.14's passage stays given, for its statement names E. The pages,
CERTIFICATE.md and GRAPH.md were made afresh. So
items 1 to 6 are done, but for the reason given for III.2's expectation in
`tests/certificate_expectations.json` ("III.1, which it cites"), whose pinned value
stands and whose owner is asked to change it. The row for #131 in the opening table,
"analysis only", and the last sentence of the section on III.8, that its proof takes the
centre by III.1, are of this report's date.

## Correction to the #131 addendum

*23 October 2026.*

The #131 addendum's phrase "Euclid's route" for III.8 is too broad. III.8 remains
modified: it uses Euclid's orders where they apply and I.24 where neither order reaches,
including points on different circumferences and points of contact. Its centre M now
comes from `Tacit.exists_centre` under Heath's "[III. 1]".

## Addendum: the angle of contact after III.18 moved into `Elements/` (#130)

*25 October 2026.*

On 25 October 2026 the owner chose, of the options put to them in item 15 of the
coordinator's decisions waiting, "A": to approve the three drafts of this report, #126,
#129 and #130, as they stand. The coordinator's record of that ruling is on #126, #129,
#130 and #332, and the
[decision entry of that day](../decisions/2026-10-25-routes-iii-contact.md) records it
with this move. The section "For the owner: the drafts as they now stand", the words "not
approved" in the section on #130, and the row for #130 in the opening's table, "new, a
draft", are of this report's date.

Under that approval, as part of #332, the seven theorems of AngleOfContact.lean moved
into [Elements/BookIII/Prop18.lean](../../Elements/BookIII/Prop18.lean), after III.18's
proof, and from the namespace of the routes into III.18's own:

```text
Elements.BookIII.Prop18.diameter              a step: AE at right angles to AB [III. 18]
Elements.BookIII.Prop18.parts                 a step: III.16's two parts for AE
Elements.BookIII.Prop18.branch                a step: each branch on the diameter's side
Elements.BookIII.Prop18.contact_locallyEqual  the companion III.18 contact_locallyEqual
Elements.BookIII.Prop18.contact_lt            the companion III.18 contact_lt
Elements.BookIII.Prop18.semicircle_gt         the companion III.18 semicircle_gt
Elements.BookIII.Prop18.acute                 the companion III.18 acute
```

Their statements are as staged, hypothesis names included. Before the staged copy was
deleted, Lean compared each moved type with the staged one, binder names and universe
parameters included, and found all seven the same; only the namespace changed. Their
docstrings and remarks came with them, revised only where a sentence spoke of staging or
approval, save `Prop18.acute`: its independent reader found that its placing of the acute
angle by I.23 proved again the steps of III.16's companion `Prop16.acute`, so its proof
now cites `Prop16.acute` and `Prop16.semicircle_wellFormed`, and its docstring gains a
last sentence saying so; its statement is unchanged. The staged file's module text is now a section after III.18's proof, without the
issue number, the sentence that `Elements/` had none of these statements, and the status
line, and it says instead that III.16's companions prove the comparisons in III.16's
figure and these prove them for every touching straight line; the last sentence of
`Prop18.semicircle_gt`'s docstring names III.16's companion `Prop16.semicircle` where it
named `Elements/`. The module text of `Prop18.lean` gains a paragraph on the companions,
and the file three imports, none later than III.18:
[Elements/BookI/Prop23.lean](../../Elements/BookI/Prop23.lean),
[Elements/BookIII/MixedAngles.lean](../../Elements/BookIII/MixedAngles.lean) and
[Elements/BookIII/Prop16.lean](../../Elements/BookIII/Prop16.lean). No `--` line, and no
other statement, changed.

The fifteen copies of III.16's steps left the staged file at 4a6d9a49, as "For the owner"
says, and the moved Lean proves none of them again: it cites `Prop16.inside_sameSideOf`,
`Prop16.horn_locallyEqual`, `Prop16.horn_lt`, `Prop16.semicircle_gt`, `Prop16.acute` and
`Prop16.semicircle_wellFormed`, with
`NearVertexOpen.mono_near` and `LocallyLess.congr_left` of the mixed angles. A scratch
Lean file, outside the repository, read the built library: no other declaration of
`Elements/` has the type of any of the seven. It also walked every constant beneath them,
statements and proofs, through every declaration it met: none reaches Circle 2, Circle 3,
Points 9 or Intersection 2, all four now theorems proved after III.2, nor any module of
Book III after III.18; no `sorry` is beneath them, and every axiom is Lean's own or one of the
foundations. `Prop18.diameter` and `Prop18.parts` do not rest on `Tacit.exists_centre`;
the other five do.

The four statements are companions of III.18, listed in
[Elements/Companions.lean](../../Elements/Companions.lean) after III.17's, so the
certificate has 42 companions where it had 38. Each is proved, with 44 of our axioms
beneath it, `Tacit.exists_centre` among them. No other entry changed, but for III.18's
list of what is attached to it. `Prop18.contact_locallyEqual` is the first entry stated
with `LocallyEqual`, a word of the foundations, in
[Elements/Foundations/DefinitionsIII.lean](../../Elements/Foundations/DefinitionsIII.lean),
so the vocabulary that `facts.json` gives grows from 262 words to 263.
`Certificate/axioms.lock` holds the same words, so it changes with it, and the two hashes
of the lock with it, by a decision of their own; until then `scripts/check_fidelity.py`
names the word.

`Staging/Routes/AngleOfContact.lean` is deleted, and `Staging.lean` no longer imports it.
Its module text now says that the angle of contact has moved home, and that `Routes/`
holds the files of #126 and #129, approved with it, which wait for a move of their own.
The opening's table links AngleOfContact.lean to commit
fc3dffa892a32be571c28b208dfb40189226db93, where it remains as it was staged, as its rows for
#125 and #127 do. The commands of "Checks" above that name the staged file or its module
reproduce at the revisions they give only.

III.18's review record names the four companions in its statement, says in a route note
how they follow Euclid's order, and carries the tag `mixed-angles-local`, with a note on
the angle of contact as Euclid draws it. The verdicts of its last reading are taken out,
and its stamps are that reading's, so `scripts/check_fidelity.py` reports that its
statement and its Lean file have changed since it was reviewed. A reader who did not
write them reads the record, the new paragraph of III.18's mishnah and the moved Lean
again, and stamps the record. III.16's record and mishnah say nothing that this move makes
untrue.

**On branch lean/iii-contact-after18 at bedbba23 with this train's edits** (25 October
2026, card #332, the move of #130). `lake build` completed (189 jobs), as did
`lake build Staging` (106 jobs) and `lake build Audit` (194 jobs, every pin holding).
`Prop18.lean`, elaborated alone, gave no message, and the build's only warnings were the
four unused variables of `Elements/Figure/Circles.lean` and
`Elements/BookIII/Prop31.lean`, which it does not touch. `lake env lean
Certificate/Facts.lean` wrote 99 propositions, 3 porisms and 42 companions.
`python3 scripts/check_style.py` and `python3 scripts/check_links.py` passed
(`✓ style: the hard rules hold (S1–S26)`; `✓ links: all 16150 relative links and anchors
in 556 Markdown files resolve`), and `python3 scripts/sweep_citations.py` found no hit in
`Prop18.lean`. `python3 scripts/check_fidelity.py` found four problems: `LocallyEqual`,
not yet in the lock, and the three stale stamps of III.18's record. `python3
scripts/check_acceptance.py --quick` passes P10 for III.18 now. Of its 18 failing items,
eight are new against the report it last wrote on main, at b46efb93: E2, for
`LocallyEqual`, and III.18's P2 and P11 to P16, until its record is read again and
stamped.

**Completion on the delivered revision.** The lock and its two model hashes were renewed,
and III.18's record was read against `8d1358248` by an independent reader and stamped in
`f94a335b`. Its six review verdicts now pass, and the page and program status were made
afresh. The prospective failures in the preceding snapshot therefore belong to
`bedbba23` with the move's then-uncommitted edits, not to the delivered revision.

## Addendum: Definition III.3 read at the point of contact moved into `Elements/` (#126)

*25 October 2026.*

On 25 October 2026 the owner chose, of the options put to them in item 15 of the
coordinator's decisions waiting, "A": to approve the three drafts of this report, #126,
#129 and #130, as they stand. The coordinator's record of that ruling is on #126 and #332,
as on #129 and #130, and the
[decision entry for this move](../decisions/2026-10-25-routes-iii-touching.md) records it.
In the section on #126, the words "a draft for the owner's approval, and not approved",
"nothing in `Elements/` uses them" and "the agreement belongs beside Definition III.3 and
III.11's commentary", and the row for #126 in the opening's table, "new, a draft", are of
this report's date.

Under that approval, as part of #332, the four definitions of Touching.lean moved into
[Elements/Foundations/DefinitionsIII.lean](../../Elements/Foundations/DefinitionsIII.lean),
beside `TouchesInternally`, `TouchesExternally` and `CirclesTouch`, in the namespace
`Elements`, and its fourteen theorems into
[Elements/BookIII/Prop13.lean](../../Elements/BookIII/Prop13.lean), after III.13's proof,
in the namespace `Elements.BookIII`:

```text
Elements.Touching.Near                           near C, every point has the property
Elements.TouchesInternallyAt                     contact within, at the point
Elements.TouchesExternallyAt                     contact without, at the point
Elements.CirclesTouchAt                          Definition III.3, at the point
Elements.BookIII.Touching.len_lt_of_outside      a step
Elements.BookIII.Touching.sameSide_of_near       a step
Elements.BookIII.Touching.small                  a step: the small circle about C
Elements.BookIII.TouchesInternallyAt.between     a step: III.11's conclusion, at the point
Elements.BookIII.TouchesExternallyAt.between     a step: III.12's conclusion, at the point
Elements.BookIII.Touching.internally_of_between  a step
Elements.BookIII.Touching.externally_of_between  a step
Elements.BookIII.Prop13.touchesInternally_iff    the companion III.13 touchesInternally_iff
Elements.BookIII.Prop13.touchesExternally_iff    the companion III.13 touchesExternally_iff
Elements.BookIII.Prop13.circlesTouch_iff         the companion III.13 circlesTouch_iff
Elements.BookIII.TouchesInternallyAt.of_whole    a way of the agreement within
Elements.BookIII.TouchesExternallyAt.of_whole    a way of the agreement without
Elements.BookIII.TouchesInternallyAt.whole       the other way within
Elements.BookIII.TouchesExternallyAt.whole       the other way without
```

Each was staged in the namespace of the routes, under `Elements.BookIII`. The definitions
now stand in `Elements`, and the steps in `Elements.BookIII`, each under its staged name;
the three agreements, staged as touchesInternally_iff, touchesExternally_iff and
circlesTouch_iff, take the prefix Prop13 as well, by FORMALIZATION's rule for a companion's
name. No other name changed. Before the staged copy was deleted, Lean compared
each moved type with the staged one, the staged names read as the moved ones, binder names,
binder kinds and universe parameters included, and each definition's value too, and found
all eighteen the same, with their docstrings, which came unchanged. A second comparison,
after the change to the agreements' proofs below, against the staged file as committed,
found the same. Review then added one sentence to the docstring of `Touching.Near`: it is
`Surrounds p C`, its arguments in the other order, as Lean accepts by `rfl`, and the
docstring now points to `LocallyWithin` as below in the same file. The lock records no
docstring, so it is unchanged by that sentence.

The proofs changed in two places. The definitions are no longer in the steps' namespace,
so `TouchesInternallyAt.between hF hG h`, and its kin for contact without, stand where the
staged proofs of `TouchesInternallyAt.whole` and `TouchesExternallyAt.whole` wrote
`h.between hF hG`; and the agreement for the
two contacts together names the other two agreements by their new names. And the two
agreements for contact within and for contact without no longer pair two steps,
`⟨TouchesInternallyAt.of_whole, TouchesInternallyAt.whole⟩`: `scripts/sweep_citations.py`
lists a companion whose proof comes down, in every branch, to one application of a helper,
and FORMALIZATION, section 5, has such a hit fixed, never declared. So each agreement now
carries both ways in its own proof, with the steps and remarks of the staged proofs of
the four ways, and the four ways, their statements and docstrings as staged, follow
the agreements, each cited from its way of the agreement; the sweep then finds no hit in
`Prop13.lean`. Through the agreements, `TouchesInternallyAt.of_whole` and `TouchesExternallyAt.of_whole` now rest on
`Tacit.exists_centre` as well.

The staged module text is now a section after III.13's lemmas, "Definition III.3 read at
the point of contact, after III.13", without the issue number and the status line. Its
"This file stages Heath's reading" reads "Heath's reading, said at the point, is defined
beside them"; it names the agreements by their new names; and its last paragraph says that
the two lemmas come after III.13, without its clause that the agreement belongs beside
Definition III.3 and III.11's commentary. Its headings are a level lower, the heading of the
definitions is gone with them, the heading over the two ways from the whole circles gives way to one
over all four ways, and the paragraph on small facts opens "Five others are proved
elsewhere" where it said they "are in `Elements`". The module text of `Prop13.lean` gains a
paragraph on the companions, and the file three imports, none later than III.13:
[Elements/BookI/Prop20.lean](../../Elements/BookI/Prop20.lean),
[Elements/BookI/Prop24.lean](../../Elements/BookI/Prop24.lean) and
[Elements/BookIII/MixedAngles.lean](../../Elements/BookIII/MixedAngles.lean). The module
text of `DefinitionsIII.lean` names, among its words, circles touching "read of the whole
circles and, as Heath prefers, at the point of contact". No `--` line, and no other
statement, changed.

The four copies of facts of `Elements/` that Touching.lean once held, which it named
Touching.exists_circle, Touching.onLine_of_collinear, Touching.len_lt_of_add_lt and
Touching.foot_nearest, left it at 4a6d9a49, as "For the owner" says, and their facts, `exists_circle_about`,
`onLine_of_collinear`, `len_lt_of_add_lt` and `foot_nearest`, are cited from
`Elements/`, with `surrounds_sameSideOf`. A scratch Lean file, outside the repository, read
the built library: no other declaration of `Elements/` has the type of any of the fourteen
theorems, binder names aside, and `exact?` found no fact of `Elements/` that proves any of
the five whose statements use no new word. It also walked every constant beneath the
eighteen, statements and proofs: none reaches Circle 2, Circle 3, Points 9 or Intersection 2,
nor any module of Book III after III.13, nor III.11's or III.12's; the modules of Book III
reached are III.2's, the mixed angles' and III.13's own. No `sorry` is beneath them, and
every axiom is Lean's own or one of the foundations. A planted Circle 3 and a planted III.20
among the roots were each found.

The three agreements are companions of III.13, listed in
[Elements/Companions.lean](../../Elements/Companions.lean) after III.8's, so the
certificate has 45 companions where it had 42. Each is proved, with 44 of our axioms
beneath it, `Tacit.exists_centre` among them. III.13 touchesInternally_iff cites I.12, I.17,
I.19, I.20 and I.24; III.13 touchesExternally_iff cites those and III.2; III.13
circlesTouch_iff cites the other two. No other entry changed, but for III.13's list of what
is attached to it. The four definitions are first reached by these companions' statements,
so the vocabulary that `facts.json` gives grows from 263 words to 267, and
`Certificate/axioms.lock`, which holds the same words, was written again by its tool, with
the two hashes of the lock and the formal model's record of it, by the decision entry above.

Touching.lean is deleted, and `Staging.lean` no longer imports it. Its module text now says
that Definition III.3 read at the point has moved home, and that `Routes/` holds #129's
files alone. The opening's table links Touching.lean to commit
fc3dffa892a32be571c28b208dfb40189226db93, where it remains as it was staged, as its rows
for #125, #127 and #130 do, and this report's other mentions of the file are no longer set
as code, since `scripts/check_style.py` reads a name in backticks as a Lean name once the
file is gone. The commands of "Checks" above that name the staged file or its module
reproduce at the revisions they give only.

III.13's review record names the three companions in its statement, says in a route note
that they follow III.13 and are not Euclid's, and adds to its representation note the
reading at the point; its mishnah gains a paragraph on them. III.11's mishnah said that
neither Heath's local contact nor its agreement with ours had been formalised; it now says
that both are, after III.13. The verdicts of III.13's last reading are taken out, and so are
III.11's on commentary and sign-off, which that sentence leaves unread. The stamps are the
last reading's, so `scripts/check_fidelity.py` reports that III.13's statement, Lean file
and record have changed since it was reviewed. A reader who did not write them reads both
records, the two mishnah paragraphs and the moved Lean again, and stamps III.13's record.
III.12's record and mishnah, and III.11's record, say nothing that this move makes untrue.
Book III's brief said, on 19 October, that contact read at the point had not been
formalised; that sentence stays, with a dated note below it saying that it is overtaken.
The [overlap catalogue](overlaps.md) gains, among its near misses, a dated entry on the two
steps that reach III.11's and III.12's conclusions by another route.

**On branch lean/iii-touching-at-point at 68a110e6 with this train's edits** (25 October
2026, card #332, the move of #126). `lake build` completed (189 jobs), as did
`lake build Staging` (104 jobs) and `lake build Audit` (194 jobs, every pin holding).
`Prop13.lean`, elaborated alone, gave no message, and the build's only warnings were the
four unused variables of `Elements/Figure/Circles.lean` and `Elements/BookIII/Prop31.lean`,
which it does not touch. `lake env lean Certificate/Facts.lean` wrote 99 propositions, 3
porisms and 45 companions, with 48 axioms and 267 words. `python3 scripts/check_style.py`
and `python3 scripts/check_links.py` passed (`✓ style: the hard rules hold (S1–S26)`;
`✓ links: all 16195 relative links and anchors in 558 Markdown files resolve`, before this
paragraph), and `python3 scripts/sweep_citations.py` found no hit in `Prop13.lean`.
`python3 scripts/check_fidelity.py` found three problems, the stale stamps of III.13's
record, and holds the lock as written. The model's generator changed only the line of
`model/Model/Laws.lean` that records the lock's hash, and `lake build` in `model/`
completed (2691 jobs). `python3 scripts/check_acceptance.py --quick`, writing its report
outside the repository, passes E6 now. Of its 18 failing items, nine are new against the
#130 branch's head, 68a110e6: III.13's P2 and P11 to P16, until its record is read again and
stamped, and III.11's P14 and P16, until its mishnah's changed sentence is read and those
verdicts are recorded again.

**Completion on the delivered revision.** III.11's and III.13's records were read in full
against `d87e0632f` by an independent reader who wrote neither, and stamped in
`3621cd0ef`: III.13's six verdicts pass, and III.11's applicable verdicts pass,
with representations `n/a`; the pages and the program's status were made afresh. The
verdicts taken out, the stale stamps and the failures in the snapshot above belong to
`68a110e6` with the move's then-uncommitted edits, not to the delivered revision.

## Addendum: the angle at the centre of any size, III.20, III.21 and III.26 moved into `Elements/` (#129)

*26 October 2026.*

On 25 October 2026 the owner chose, of the options put to them in item 15 of the
coordinator's decisions waiting, "A": to approve the three drafts of this report, #126,
#129 and #130, as they stand. The coordinator's record of that ruling is on #126, #129, #130
and #332, and the [decision entry for this move](../decisions/2026-10-25-routes-iii-centre.md)
records it. In the section on #129, the words "New, a draft for the owner's approval, and not
approved", "they can replace the proofs there only once it is approved" and "on adoption
should be cited from one home", and the row for #129 in the opening's table, "III.20 in
general new, a draft", are of this report's date.

Under that approval, as part of #332, the definition of Prop20.lean moved into the
foundations, beside `circumference`, and the theorems of Prop20.lean, Prop21.lean and
Prop26.lean into Elements' files of the same names:

```text
Elements.angleAtCentre                       the definition, in DefinitionsIII.lean
Elements.BookIII.angleAtCentre.diameter      a step: any such diameter gives the same angle
Elements.BookIII.angleAtCentre.congr         a step: only K's side of BC counts
Elements.BookIII.angleAtCentre.within        a step: the angle BEC, the centre across BC from K
Elements.BookIII.angleAtCentre.semicircle    a step: two right angles, the centre on BC
Elements.BookIII.angleAtCentre.reflex        a step: with the angle BEC, four right angles
Elements.BookIII.angleAtCentre.reflex_gt     a step: greater than two right angles
Elements.BookIII.angleAtCentre.size          a step: less, two right angles or greater
Elements.BookIII.Prop20.across_side          a step: the centre in Euclid's second figure
Elements.BookIII.Prop20                      III.20, for the angle at the centre of any size
Elements.BookIII.Prop20.special              the companion III.20 special
Elements.BookIII.Prop20.circumference        the companion III.20 circumference
Elements.BookIII.Prop21                      III.21, by Euclid's two steps
Elements.BookIII.Prop26.alike                a step: equal angles at the centres lie alike
Elements.BookIII.Prop26                      III.26, by Euclid's one argument
```

with the five private steps of Prop20.lean, sameSideOf_beyond, diameter_cases,
diameter_within, diameter_beyond and diameter_eq, private in Elements' Prop20.lean too.
The definition and its theorems were staged in the namespace of the routes, and III.20 in
general with the three theorems named after it in that of a changed main theorem; the
definition now stands in `Elements`, the rest in `Elements.BookIII`, under the staged
names. III.20 in general takes the name of III.20, and III.20 as `Elements/` stated it until
now is its companion III.20 special, as FORMALIZATION's rule for a statement that changes
asks. Before the staged copies were deleted, a scratch Lean file outside the repository
wrote out each staged declaration's type, binder names, binder kinds and universe
parameters included, and the definition's value, the staged names read as the moved ones;
after the move a second wrote out the moved declarations the same way, and all twenty were
the same, with their docstrings, but for one clause added to that of
`angleAtCentre.reflex_gt` (below). The same strict comparison, at the #126 branch's head,
a245221b, found the staged III.20 special, III.21 and III.26 to have exactly the types of
III.20, III.21 and III.26 in `Elements/`; and the staged files' three closing checks,
`type_of%` on each side closed by `rfl`, held in a scratch file against those three
statements written out. The checks are not kept in the repository: each moved proof is now
the theorem it was checked against, and III.20 special keeps III.20's former statement.

The staged step that an angle of a triangle is less than two right angles repeated a lemma
private to I.13's file, triangle_angle_lt_two_right, proved there by I.13 and Common
Notion 5. That lemma is now the one home of the fact: it loses the word `private` and takes the
name `Prop13.angle_lt_two_right`, by FORMALIZATION's rule for a proposition's helpers, its
statement and proof unchanged; the staged step is not kept, `angleAtCentre.reflex_gt` and
`angleAtCentre.size` cite it, and the docstring of `angleAtCentre.reflex_gt` gains a clause
naming it. I.13's review record is read again for the removal of `private` and the rename to
`Prop13.angle_lt_two_right`. `Elements/` also has the
fact in public, in Book I after I.29, as `Figures.OutlineBound.angle_lt_two_right`, which
`exact?` found for the staged statement; it rests on Metric 5
(`Tacit.angle_le_two_right`, no angle exceeds two right angles), and citing it would have
added that axiom to III.26 and to the propositions that cite III.26, so it is not cited.
No other staged step is a fact of `Elements/`: a scan of every
declaration of `Elements/` found none with the type of any of the 21 staged declarations,
but for the three staged proofs of statements in `Elements/`, and `circumference` and
`standing`, whose type the definition shares with a value of its own; and `exact?` found
nothing that proves any of the six other steps whose statements use no new word.

The module text of Prop20.lean is the staged file's, without the issue number, the status
line and the comparison with the proof it replaces, and says instead that the reading of
the angle at the centre is ours, made after Heath's notes, and not Euclid's. Those of
Prop21.lean and Prop26.lean now say the same of their proofs, and Prop26.lean's keeps its
account of the congruence of the remainders. In Prop21.lean's remarks, "the general III.20" is now "III.20",
named by its name in `Elements/`, `BookIII.Prop20`. The module text of
`DefinitionsIII.lean` names the angle at the centre among its words, and its paragraph on
circumferences gains a sentence on how it is read. III.26's closing check, that its
measures alone follow from it, stays, as the overlap catalogue's audit file says. The old
proofs of III.21 and III.26 had no helper outside their proofs: Robert Simson's completion
and Euclid's case for the greater segment in III.21, and the sorting of the angles in
III.26, were steps of those proofs and went with them. `Prop24.angle_type`, by which III.26
sorted them, stays, for III.24's companion `Prop24.equalCircles`, III.27 and III.28 use it.
No `--` line, and no statement other than III.20's, changed.

The six files of `Elements/` that cited III.20 cite it still. III.21 and III.26 cite III.20
in general. `Prop24.equalCircles`, III.27 (twice), III.28 and `Circumference.centre` cite
`Prop20.special`, and so does `Audit.III_27_any` in the overlap catalogue's audit file;
`lake build Audit` then held every pin unchanged. Three sentences of the comments of
III.27's file that compared its cases with III.26's, which now has no such cases, were made
true. The certificate's entries that cite III.20 special are III.24 equalCircles, III.25
kind, III.27, III.28 and III.29, through those steps, and III.20 now cites I.13 and III.2
as well as I.5 and I.32, and rests on `Tacit.exists_centre`, 45 axioms where it had 44.

The two companions are listed in [Elements/Companions.lean](../../Elements/Companions.lean)
after III.18's, so the certificate has 47 companions where it had 45. Each is proved, with
45 of our axioms beneath it. III.20 and III.20 circumference are the first entries whose
statements reach `angleAtCentre`, so the vocabulary that `facts.json` gives grows from 267
words to 268, and `Certificate/axioms.lock`, which holds the same words, was written again
by its tool, with the two hashes of the lock and the formal model's record of it, by the
decision entry above.

Prop20.lean, Prop21.lean and Prop26.lean are deleted, and with them `Staging/Routes/`,
which is now empty and gone: every draft of this report is in `Elements/`, and #332's work
is done. `Staging.lean` imports nothing, and its module text now says that nothing is
staged, what has moved home, and how a later brief stages a statement; `lake build Staging`
still completes. The opening's table links the three files to commit
fc3dffa892a32be571c28b208dfb40189226db93, where they remain as they were staged, as its rows
for #125, #126, #127 and #130 do, and this report's other mentions of the three staged
files are no longer set as code. The commands of "Checks" above that name a staged file or
its module reproduce at the revisions they give only.

III.20's review record now says that its statement speaks of the angle at the centre of
any size, with its two companions, and gains a route note and a representation note;
its passages are those of the new proof. III.21's route is `euclid`: the Lean takes
Euclid's two steps for every segment, and III.21 has no passage argued another way, so the
schema allows it; its record says that the reading of the angle at the centre is ours and
that III.20 cites I.13 and III.2, and declares the centre F, which Euclid's sentence takes
and nothing below names, as unused. III.26's route stays `modified`: the congruence of the
remainders is still argued by III.22 and III.24, a passage argued another way, and its
route note gives that, the one division into cases at I.4, and the reading. III.27's record
says that its Lean now cites III.20 special. The verdicts of each record's last reading
are taken out, and its stamps are that reading's, so `scripts/check_fidelity.py` reports
the four as changed since they were reviewed; a reader who wrote none of them reads each
again, with the mishnah of III.20, III.21, III.26 and III.27, which now tell the new
reading and routes, and stamps it. The gap catalogue's entries for III.20, III.21 and
III.26 no longer tell of Simson's completion or of the separate cases, and the
[overlap catalogue](overlaps.md)'s sentence on the staging folder says that it is gone.

**On branch lean/iii-centre-any-size at a245221b with this train's edits** (26 October
2026, card #332, the move of #129). `lake build` completed (189 jobs), as did
`lake build Staging` (3 jobs, nothing staged) and `lake build Audit` (194 jobs, every pin
holding); the build's only warnings were the four unused variables of
`Elements/Figure/Circles.lean` and `Elements/BookIII/Prop31.lean`, which it does not touch.
`lake env lean Certificate/Facts.lean` wrote 99 propositions, 3 porisms and 47 companions,
with 48 axioms and 268 words, and after the last edit wrote the same file again. A scratch
walk beneath the fourteen moved theorems, statements and proofs, found no `sorry`, no axiom
but Lean's three and the foundations', none of Circle 2, Circle 3, Points 9 or Intersection
2, and no module of Book III after the theorem's proposition; Circle 3 and III.21, planted
among its roots, were each found. `python3 scripts/check_style.py` and
`python3 scripts/check_links.py` passed (`✓ style: the hard rules hold (S1–S26)`;
`✓ links: all 16248 relative links and anchors in 560 Markdown files resolve`),
`python3 scripts/heath.py` held, and `python3 scripts/sweep_citations.py` found one hit in
the moved files, III.21's centre F, which its record declares. `python3
scripts/check_fidelity.py` found eleven problems, the stale stamps of the records of III.20,
III.21, III.26 and III.27, and of III.24 and III.28, whose Lean files changed by one call
each; it holds the lock as written. The model's generator changed only the line of
`model/Model/Laws.lean` that records the lock's hash, and `lake build` in `model/`
completed (2691 jobs). `python3 scripts/check_acceptance.py --quick`, writing its report
outside the repository, passes P10 for III.20, III.21 and III.26, and E6, now. Of its 48
failing items, 42 are new against the last run of the #126 branch, a full run at 3a76a448,
which merges main into it after a245221b: III.20's, III.21's, III.24's, III.26's, III.27's
and III.28's P2 and P11 to P16, until their records are read again and stamped.

**Completion on the delivered revision.** After that snapshot, I.13's lemma became the one
home of the fact that an angle of a triangle is less than two right angles, in place of
Book I's `Figures.OutlineBound.angle_lt_two_right`, as said above, so I.13's record was
stale too; III.26 to III.30 then rest on the axioms they rested on before, and III.20
alone gains one, `Tacit.exists_centre`. The gap catalogue's entry for III.27 was made true
as well. An independent reader who wrote none of them read the records of III.20, III.21,
III.26 and III.27 in full, and those of I.13, III.24 and III.28 for their one change, and
stamped them at `d2e249c39` (III.28's at `4aad4576`, after one note was corrected). Review
then found III.21's passage note on the joins, III.27's commentary on the right angles and
III.28's Lean comments on the diameters untrue of the new Lean, and asked that I.13's lemma,
now public, take a name by FORMALIZATION's rule; all four were corrected, and the records
of I.13, III.20, III.21, III.27 and III.28 read and stamped again. The stale stamps and failures of the snapshot above belong
to its revision, not to the delivered one.

**Follow-up, 26 October 2026.** The review of the second reading round found five things
this addendum leaves out or says loosely; they are recorded here, and the paragraphs above
stand as written.

- **The second round's stamps.** The records of I.13, III.20, III.21, III.24 and III.27
  were stamped again at `5afb1d6a4`, III.24's for its run line, which the reader corrected
  to name the change it was read for, and III.28's at `7d4aa4370`. III.26's record was not
  read in that round; it was read again in full, and stamped at `90238039b`, for #252.
- **Whose words were read.** The corrected sentence of III.27's mishnah, III.28's passage
  note on the diameters and the text of III.28's two Lean comments on them were written by
  the reader of that round, GPT-6 Astra (Codex), in the session that then stamped III.27,
  at `5afb1d6a4`, a commit before that sentence, which `688cabe4d` carries; the corrected
  sentence of III.28's mishnah was written by a second session of the same reader; and
  each was committed word for word (commits `688cabe4d` and `3e021eb5a`). A third session,
  which wrote none of them, stamped III.28. Every one of these readings is of the family
  that wrote the sentences, so the stamps on those sentences rest on a reading by their
  authors' family, not by the other family. The review checked each sentence and found it
  true of the Lean.
- **The rule for the name.** The rule cited above for `Prop13.angle_lt_two_right`,
  "FORMALIZATION's rule for a proposition's helpers", should be FORMALIZATION's section 6,
  "Where lemmas live", and its rule for a porism or any corollary: a consequence of one
  proposition that later proofs share is a corollary after it, as this lemma is, after
  I.13. The rule for a helper puts it before its proposition.
- **III.28's corrections.** Besides its Lean comments, III.28's passage note on the
  diameters, its mishnah and its entry in the gap catalogue (commit `68b862505`) were
  corrected, and its record read again for all of them; the account above, and the gap
  entries it lists, leave those out.
- **The right angles of III.27.** In the section on #127 above, the sentence that in the
  right case "there is no angle at the centre to halve" is of that section's date: the
  angle at the centre standing on a semicircle is now `angleAtCentre`, two right angles
  (`angleAtCentre.semicircle`). III.27's proof does not halve it, and still reads its
  right angles off `Prop24.angle_type`;
  [#511](https://github.com/jackChallis/stoicheia/issues/511) proposes Euclid's halving
  there.

## Addendum: the centre by III.1's construction (#547)

26 October 2026. By the owner's decision recorded on
[#547](https://github.com/jackChallis/stoicheia/issues/547), "Yes - follow Euclid when
possible.", and the coordinator's [decision entry of that day](../decisions/2026-10-26-centre-by-iii1.md),
III.4, III.8 and III.17, with `Prop8.partner` and `Prop17.general`, take the centre under
Heath's "[III. 1]" by III.1's construction through `Prop1.of_circle`; III.2 follows after
ship C7's train P3 ([#477](https://github.com/jackChallis/stoicheia/issues/477)). Every
audit pin holds unchanged. No entry's axioms change; the five entries cite III.1 through
the shared step `Prop1.of_circle`, and Heath's references with no call fall from six to
three. The reading of #131's section above, that such a call does no work, is overtaken.

28 October 2026. After ship C7's train P3
([#477](https://github.com/jackChallis/stoicheia/issues/477)), III.2 too takes its centre
under Heath's "[III. 1]" by III.1's construction, through `Prop1.of_circle`, which is now
listed as III.1's companion, with a certificate entry of its own
([decision entry](../decisions/2026-10-28-iii2-centre.md)); its route is `euclid`. III.8's
last step now goes by Euclid's two orders in every case, I.21 for the convex circumference
and I.24 for the concave, and a point of contact, which ends both orders, is never the
nearer (`Prop8.contact_last`); its route is `euclid`. III.26, III.28 and III.29 remain
`modified`, and their records say why.
