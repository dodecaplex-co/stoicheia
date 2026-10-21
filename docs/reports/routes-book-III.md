# Euclid's routes in Book III

*21 October 2026.*

This report answers issues #125, #126, #127, #129, #130 and #131. Five of them ask for
Euclid's own argument where our proofs of Book III take another way, or for something his
words say that our Lean does not yet say; the sixth asks which of our calls of III.1 do any
work. The Lean is in seven files under `Staging/Routes/`. Every declaration is in the
namespace `Elements.BookIII.Routes`, which departs from `Elements.Book<B>.Staging.PropN`,
the name FORMALIZATION, section 6, gives staged proofs; whether to rename it or record the
exception is the coordinator's decision. None of it is in `Elements/` yet.

**The statements the files stand on.** [Brief 0008](../briefs/0008-centre.md) restates
Book III so that every circle has a centre (`Tacit.exists_centre`). The trains C6a, C6b and
C6c carry the next move of Book III's files into `Elements/`, those restatements among it,
with main as at 2e8aecf. This branch merged their head, train C6c as at 80292b0a (the merge
is 9679f978), and its `Elements/` has not changed since. As their head, train C6c carries
the other two, and in this report it stands for all three. Main did not have the
restatements when this report was written, and these files land after train C6c. In this
report, **the statement in `Elements/`** or **the proof in `Elements/`** of a proposition is
the one train C6c leaves in `Elements/BookIII/`, which is the one on this branch. The files
were written on main's statements as at 2e8aecf and then moved onto those in `Elements/`:
III.8, III.27, touching at a point and the angle of contact at 4a6d9a49, and III.20, III.21
and III.26 at 9f8c8adb; 86c5748d answers the minor findings of the independent readers of
the first of these. For these files train C6c changes six things:

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

WORKFLOW, section 2, admits these proofs in `Staging/` only as those of a prototype the
coordinator has approved; recording `Staging/Routes/` so, as the 18 October entry records
the mixed angles, is the coordinator's to confirm, and the files wait for it before they
land.

| Issue | File | What it holds | Statement |
|---|---|---|---|
| #125 | [`Prop08.lean`](../../Staging/Routes/Prop08.lean) | III.8, with Euclid's last step | as in `Elements/` |
| #127 | [`Prop27.lean`](../../Staging/Routes/Prop27.lean) | III.27 by Euclid's reductio and halving, for angles of every size | as in `Elements/` |
| #126 | [`Touching.lean`](../../Staging/Routes/Touching.lean) | Definition III.3 read at the point of contact, and its agreement with our reading of the whole circles | new, a draft |
| #129 | [`Prop20.lean`](../../Staging/Routes/Prop20.lean), [`Prop21.lean`](../../Staging/Routes/Prop21.lean), [`Prop26.lean`](../../Staging/Routes/Prop26.lean) | the angle at the centre of any size; III.20 for it; III.21 and III.26 by Euclid's one argument | III.20 in general new, a draft; III.20's special case, III.21 and III.26 as in `Elements/` |
| #130 | [`AngleOfContact.lean`](../../Staging/Routes/AngleOfContact.lean) | III.16's comparisons for every straight line touching a circle, after III.18 | new, a draft |
| #131 | none | which calls of III.1 do work | analysis only |

"As in `Elements/`" in the last column means that the staged theorem has exactly the type
of the theorem in `Elements/`, which Lean checks (see "Checks", at the end).

## For the owner: the drafts as they now stand

The drafts await approval in the text they have now. Moving them onto the statements in
`Elements/` changed no definition, and eleven theorems, each only by dropping hypotheses.
The first column names the theorem in the namespace `Elements.BookIII.Routes`, the second
what it lost:

```text
Prop20                          {E} (hE : Centre E ABC)
Prop20.circumference            (hE : Centre E α)
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

Five statements say more than they did, for they speak of the contact within of `Elements/`,
whose third clause asks for a point of the inner circle within the outer. Four keep their
text; the fifth is the theorem above that lost its hypothesis that the circles are two:

```text
TouchesInternallyAt.of_whole    Touching.internally_of_between    TouchesInternallyAt.whole
touchesInternally_iff           circlesTouch_iff
```

Every other draft has the text it had on main's statements as at 2e8aecf, and so have the
five definitions: the reading near a point, the three contacts at a point, and the angle at
the centre. Copies of facts that are now in `Elements/`, four in `Touching.lean` and fifteen
steps of III.16's comparisons in `AngleOfContact.lean`, are deleted, and those facts are
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

## III.27: Euclid's halving, for angles of every size (#127)

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
`Elements/` does, and a remark there says why. The file does not call
`Circumference.standing`. Its theorem for III.27 has the statement in `Elements/` exactly;
the file carries no check of that, and Lean checked it for this report (see "Checks").

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
III.11's commentary. The proofs use Book I, III.2 and System E's diagram rules,
Intersections 5, 8 and 9 among them, with the rule that every circle has a centre, and
nothing that rests on Circle 2 or Circle 3.

**What is new, and what is left.** The four definitions and the theorems about them are
new, a draft for the owner's approval, and not approved; nothing in `Elements/` uses them.
The agreement holds for any two circles, its centres taken by the rule. No fact is proved
here again: the four small facts the agreement shares with the mixed angles are cited from
`Elements/`, `exists_circle_about` and `onLine_of_collinear` from
`Elements/Figure/Regions.lean`, and `foot_nearest` and `len_lt_of_add_lt` from
`Elements/BookIII/MixedAngles.lean`.

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

**What the staged files do.** `Prop20.lean` adds a new object: the angle at the centre of a
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
the centre standing on it.

```lean
theorem Prop20 {A B C K : Point} {ABC : Circle} (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hAK : OppositeSidesOf A K B C) :
    angleAtCentre ABC B K C = ∠ B A C + ∠ B A C

theorem Prop20.special {A B C E : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)
    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hEA : SameSideOf E A B C) :
    ∠ B E C = ∠ B A C + ∠ B A C

theorem Prop20.circumference (hB : OnCircle B α) (hC : OnCircle C α)
    (hK : Triangle B C K) : circumference α B K C = angleAtCentre α B K C
```

`Prop21.lean` then gives Euclid's two steps for every segment: the angles BAD and BED are
each half of the one angle at the centre standing on the circumference BCD, and halves of
one angle are equal; Simson's completion drops out. Under Euclid's "let the centre of the
circle ABCD be taken, and let it be F", the Lean takes F by the rule, as III.21 in
`Elements/` does; a remark there says that the general III.20 takes the centre itself, that
F is that centre, and that nothing below needs it named.

`Prop26.lean` gives Euclid's one argument for every case: equal angles at the
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
exactly.

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
`Prop20.lean`, that an angle of a triangle is less than two right angles, repeats a lemma
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

**What the staged file does.** `AngleOfContact.lean` cites the steps of III.16's
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
proposes has been compiled. Its facts were read from this branch at 9f8c8adb, whose
`Elements/` is train C6c's as at 80292b0a, the one it lands on main; 86c5748d changed only
files under `Staging/Routes/`. That tree holds main as at 2e8aecf, with main's retirements
of axioms, so `centre_unique` and `adjacent_eq_of_right` are theorems there. For this report
its certificate was built afresh (`lake build`, then `lake env lean
Certificate/Facts.lean`), and the `facts.json` it wrote is, byte for byte, the one committed
at 9f8c8adb. In the figures below the first number of each pair is measured, read from that
`facts.json`. The second is computed: a Lean walk of the dependencies, as Lean's
collectAxioms walks them, which takes the dropped call out of the proof that makes it and
puts the rule in its place. Run with nothing dropped, the walk gives each of the 137 entries
exactly its `axioms` in `facts.json`. An earlier version of this section measured main at
2e8aecf and an earlier C6c (d3e9a8c), and estimated the tree that merges them; this tree is
that merge, and its measurements replace the estimate.

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

| Proposition | Call | Does work | On main, 2e8aecf | On train C6c, 80292b0a | The route that drops it |
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

| Entry | On train C6c: measured, then computed | What leaves |
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
follows "the propositions he uses". The coordinator decides between these readings. We
recommend dropping the five calls, each with a passage of the kind given: a passage of the
kind different would make four routes modified with no change in the reasoning. The
measurements on train C6c leave the recommendation as it was. The staged III.8 of #125
repeats the call of III.8 in `Elements/`, and the same change would apply to it.

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

**What could not be settled here.** Whether FORMALIZATION, section 5, permits the bracketed
calls is the coordinator's question. The second figure of each pair is computed by the walk,
not built from changed Lean. How far the audit pins shrink is inferred, for they are not in
`facts.json`; `lake build Audit` will tell. And nothing proposed here has been compiled.

## Checks

**The Lean, at 86c5748d.** The seven files were built (`lake build Staging`, which imports
all seven), with no warning from any of them, and every theorem they declare, other than
the private steps the others use, was put to Lean's collectAxioms. The check looks for
`sorryAx`, for an axiom declared outside `Elements/Foundations/` other than Lean's own three
(`propext`, `Classical.choice`, `Quot.sound`), and for Circle 3, which Circle 2 now rests
on, so that it finds both. Run on the six modules that import the seven files, it reported:

```text
Build completed successfully (101 jobs).
routes_check: 38 theorems, 0 findings
```

So none of the 38 uses `sorry`, none rests on an axiom beyond the foundations and Lean's
three, and none rests on Circle 2 or Circle 3. There were 57 before the port; the 19 copies
of facts now in `Elements/` went with it. In a scratch file outside the repository, Lean
also checked that the staged theorems for III.8, III.20's special case, III.21, III.26 and
III.27 have exactly the types of the theorems in `Elements/` (`type_of%` on each side,
closed by `rfl`); the file for III.8 carries that check itself. And it checked that nothing
beneath the seven theorems for the angle of contact, statement or proof, is a proposition of
Book III later than III.18.

**The certificate, at 9f8c8adb.** `lake build` and `lake env lean Certificate/Facts.lean`
wrote a `facts.json` identical to the one committed, which the figures of #131 read; the
walk behind the computed figures agrees with it on all 137 entries.

**Who read what.** Independent readers, who wrote none of it, read the port at 4a6d9a49,
against Heath's text where a file has his sentences and against train C6c's tree: one read
`Prop08.lean` and `Prop27.lean`, the other `Touching.lean` and `AngleOfContact.lean`. Both
passed it, with minor findings: a remark wanted under III.26's step in III.27, the unused
hypothesis that the circles are two in the step from the straight line through the centres,
and docstrings that named a centre the statement no longer has or told the history of the
move; 86c5748d answers them. The port of `Prop20.lean`, `Prop21.lean` and `Prop26.lean`, at
9f8c8adb, is being read by an independent reader as this report is written, and its findings
are not in it. The changes at 86c5748d, and this report, have not been read by an
independent reader; the branch's code review will review them. Before the port, each file
was read against Heath's text by an independent reader, and the whole branch was reviewed at
4504fa48, with the answers to that review at 4cd7c77d.
