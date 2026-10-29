# Brief 0012: Book IV, figures in and about a circle

*Status, 21 October 2026: outside the consolidation release. The owner chose, of the
options put to them that day, to rule this brief outside that release, as [the decisions
entry of that day](../decisions/2026-10-21-briefs-0010-and-0012.md) records. It stays the
draft described below, not approved, and its scratch,
[`docs/reports/crew/scratch-IV/`](../reports/crew/scratch-IV/), stays on main as committed,
built by nothing; its order of work (section 11) begins only after the owner's gate. Brief
0010, whose approval the opening below awaits, was approved that day; its question 3, on
which question 8 below waits, was left open.*

*19 October 2026. **A draft, for challenge and for the owner's and the coordinator's
approval: nothing in it is frozen, and nothing changes with it.** Book IV is the first new
book since the outside review, and [brief 0005](0005-astra-review.md) asks that it start
"with briefs approved before proofs", each new foundation with "a one-statement prototype
before any fleet". This brief is that start ([issue #97]): it gives every statement of Book
IV in Lean, the words they use, where each word and fact lives and who owns it, the
convention for what a construction is given, the bridges from the new words to Book III's
circumferences, and a prototype for each new foundation. The statements were written with
`sorry` in a scratch file and compiled against main; the prototypes were proved there
(section 9). Nothing in `Elements/`, `Staging/`, the scripts or the review records changes:
the order of work in section 11 begins only after approval, and after the owner's gate,
Books I to III each at 95 or more. Once approved, the brief is frozen, as
[WORKFLOW.md](../WORKFLOW.md), section 2, says, and a later change is a revision of it. The
code states what we formalized; where the code, this brief, a record and a page disagree,
the disagreement is recorded and reconciled ([FORMALIZATION.md](../FORMALIZATION.md),
section 1).*

Base: main at `89c5da4`. The scratch files are in
[`docs/reports/crew/scratch-IV/`](../reports/crew/scratch-IV/), committed unbuilt, as
WORKFLOW, section 2, keeps scratch proofs: `Statements.lean` holds the words and every
statement with `sorry`, and each `Prototype*.lean` repeats the words, unchanged, and proves
one statement. From the root of a checkout that has built `Elements` (and `Staging`, for
the bridge), `lake env lean docs/reports/crew/scratch-IV/<file>` checks each.

The statements are written as they will stand when one decision already taken has landed,
and one still proposed: [brief 0008](0008-centre.md)'s rule that every circle has a
centre, approved, so a given circle carries no hypothesis that it has one; and, if the
owner approves it, brief 0010's `len A B` ([#69], a draft for the owner) for the length
the library now writes `‖A B‖`. The angle is still written `∠ A B C`, as brief 0010's
question 9 leaves it until the owner answers.
Lean reads the two forms as one term, so nothing here depends on the second. No statement
of Book IV is about areas; IV.10's proof uses II.11's rectangle and square, and IV.12's the
squares of I.47, as they stand.

The draft was challenged on 19 October by a reader who did not write it, Astra (through
Codex, read-only), which found no false statement and no degenerate answer, confirmed the
five prototypes, and returned it for correction with two material findings and two
editorial; each is answered, and the appendix lists them. Warm thanks to Astra. A first
reading during the challenge found four gaps of its own (IV.16's further claims, two of the
bridges, IV.1's chord from a given point, and the tangents of the general companion), which
were mended before its report and are listed there too.

Our debts are many and gladly owed. The words are Heath's (*The Thirteen Books of Euclid's
Elements*, vol. 2, Cambridge, 1908, pp. 78–111), whose notes on Book IV show where Euclid
leaves a step to the reader and where the text was argued over, by Simson, Todhunter and
Heiberg. The rules beneath them are the System E of Jeremy Avigad, Edward Dean and John
Mumma, with LeanEuclid's corrections. The convention for what a construction is given is
Astra's, from the outside review, and was first tried on III.25 (brief 0005, stage 4). Warm
thanks to each.

## 1. What #97 asks, and where this brief answers it

| Done when | Here |
|---|---|
| a brief, challenged and frozen, gives every Book IV statement in Lean | section 6, all sixteen propositions, the porism of IV.15, the addition to IV.5 and the closing claims of IV.16; challenged once (the appendix), and a second challenge, approval and freeze are the next steps (section 11) |
| settles the construction-input convention that III.25's core prototyped | section 5 |
| defines inscribed and circumscribed figures and regular polygons, with their bridge theorems to Book III's arcs | sections 3, 4 and 7 |
| names each new word's home and owner | section 8 |
| carries a one-statement prototype for each new foundation, proved, before the proof waves start | section 9 |

## 2. What Book IV needs

Book III draws a circle's centre, its tangents and its segments; Book IV puts figures in
circles and circles in figures. Its seven definitions say what it is for a rectilineal
figure to be inscribed in a circle or circumscribed about one, and for a circle to be
inscribed in a figure or circumscribed about it. Its sixteen problems do it: a straight
line fitted into a circle (IV.1); a triangle of given angles in a circle and about one (IV.2,
IV.3); a circle in a triangle and about one (IV.4, IV.5); the square (IV.6 to IV.9); the
isosceles triangle with each angle at the base double the third (IV.10), which gives the
pentagon, in a circle and about one, and a circle in and about it (IV.11 to IV.14); the
hexagon (IV.15), with a porism; and the fifteen-angled figure (IV.16). Heath reports De
Morgan's advice for reading the book: "the idea of dividing a revolution into equal parts
should be kept prominent in considering Book IV." (vol. 2, p. 83).

Four things in it are new to the edition.

1. **Figures of any number of sides, given by their corners.** Books I and II have
   triangles, parallelograms and squares by their corners, and stage 2 gives a figure for
   its area, with its triangles. Book IV needs a pentagon, a hexagon and a fifteen-angled
   figure by their corners, with their sides and angles, and the claim that one is
   "equilateral and equiangular".
2. **Inscribed and circumscribed.** Definitions IV.3 to IV.6, read with Book III's
   circle and touching straight line.
3. **The circle divided.** The regular figures are built by cutting the circle into equal
   circumferences: IV.11 makes five equal ones and adds them ("let BCD be added to each"),
   and IV.16 counts fifteenths of the circle. So the new words need bridges to Book III's
   circumferences, and Book III's `Circumference.add`, proved in stage 3, is used at last.
4. **What a construction is given.** Every proposition of Book IV is a problem. What each
   receives, and in what form, is settled once (section 5).

## 3. The words

The definitions are Heath's, vol. 2, p. 78, checked against the page image:

> 1. A rectilineal figure is said to be inscribed in a rectilineal figure when the
>    respective angles of the inscribed figure lie on the respective sides of that in which
>    it is inscribed.
> 2. Similarly a figure is said to be circumscribed about a figure when the respective sides
>    of the circumscribed figure pass through the respective angles of that about which it
>    is circumscribed.
> 3. A rectilineal figure is said to be inscribed in a circle when each angle of the
>    inscribed figure lies on the circumference of the circle.
> 4. A rectilineal figure is said to be circumscribed about a circle, when each side of the
>    circumscribed figure touches the circumference of the circle.
> 5. Similarly a circle is said to be inscribed in a figure when the circumference of the
>    circle touches each side of the figure in which it is inscribed.
> 6. A circle is said to be circumscribed about a figure when the circumference of the
>    circle passes through each angle of the figure about which it is circumscribed.
> 7. A straight line is said to be fitted into a circle when its extremities are on the
>    circumference of the circle.

None of the words below is an assumption; each is a definition, proposed for
`Elements/Foundations/DefinitionsIV.lean` (section 8), and each joins
`Certificate/axioms.lock`'s vocabulary when a frozen statement reaches it. Their Lean is in
[`Statements.lean`](../reports/crew/scratch-IV/Statements.lean), with a docstring each.

| Euclid | Lean | Plain words | Used in |
|---|---|---|---|
| a rectilineal figure, by its corners in order | `Polygon ps`, for `ps : List Point` | at least three corners, no two the same, and for each side every other corner on one side of it | IV.6 to IV.16 |
| its sides | `Polygon.sides ps` | each corner with the next, the last with the first: `[A, B, C, D]` has AB, BC, CD, DA | the words below |
| its angles | `Polygon.cornerTriples ps` | each corner with its two neighbours: ABC, BCD, CDA, DAB, the corner in the middle | the words below |
| equilateral | `Polygon.Equilateral ps` | its sides all equal (`AllEqual` of their lengths) | IV.11 to IV.16 |
| equiangular | `Polygon.Equiangular ps` | its angles all equal | IV.11 to IV.16 |
| Def. 3, a figure inscribed in a circle | `Polygon.InscribedIn ps α` | each corner on the circle | IV.2, IV.6, IV.11, IV.15, IV.16 |
| Def. 4, a figure circumscribed about a circle | `Polygon.CircumscribedAbout ps α` | each side, produced, touches the circle (`Touches`, Def. III.2), at a point between its ends | IV.3, IV.7, IV.12 |
| Def. 5, a circle inscribed in a figure | `Circle.InscribedIn α ps` | Def. 4, read from the circle | IV.4, IV.8, IV.13 |
| Def. 6, a circle circumscribed about a figure | `Circle.CircumscribedAbout α ps` | Def. 3, read from the circle | IV.5, IV.9, IV.14 |
| the circumferences the sides cut off | `Polygon.arcs ps α` | for each side PQ, with the next corner R, the circumference on which the angle PRQ stands (`standing α P R Q`, Def. III.9), the one beyond PQ from the figure | IV.11, the bridges |
| all equal | `AllEqual xs` | any two magnitudes of the list are equal | the words above |
| Def. 7, a straight line fitted into a circle | no word: its two ends on the circle, `OnCircle C α ∧ OnCircle A α` | | IV.1, IV.10, IV.16 |
| Defs. 1 and 2, a figure in or about a figure | no word: no proposition of Book IV inscribes a figure in a figure | | |
| a triangle equiangular with a triangle | no word: the three angles, each equal to its fellow, named in order | | IV.2, IV.3 |
| a triangle, a square | Book I's `Triangle A B C` and `Square A B C D` | | IV.2 to IV.10 |

A triangle stays `Triangle A B C`, as in every earlier book; `Polygon [A, B, C]` says the
same, and Book Zero proves it (section 7).

## 4. The representations, and why

### 4.1 A figure is its corners, in order, and it is convex

Euclid's figures here are named by their corners, ABCDE, and the statements name them so:
`Polygon [A, B, C, D, E]`. A list of corners, rather than five separate points, lets one
word serve the triangle, the square, the pentagon, the hexagon and the fifteen-angled
figure, whose corners Heath does not letter, and lets the general companions (section 6)
speak of any number of sides. The library already reads lists of points this way: II.1's
points in order (`InOrder`) and stage 2's corners of a figure (`segments`, `triples`), whose
helpers `Polygon.sides` and `Polygon.cornerTriples` reuse.

`Polygon` asks that, for each side, every other corner lie on one side of it. That makes
the figure convex, with sides meeting only at their ends and no three corners in a row on
one straight line. Every figure of Book IV is one, so nothing Euclid draws is lost: a
figure inscribed in a circle that does not cross itself is convex, and so is every figure
he circumscribes. The condition keeps out what the corners alone would let in. Five points of a
circle, equally spaced and joined every other one, make a star whose five sides are equal
and whose five angles are equal; it is "equilateral and equiangular" corner by corner, but
it is not a figure "contained by straight lines" (Definition I.19), for its sides cross.
`Polygon` refuses it, so IV.11 cannot be met by a star, and IV.13 and IV.14 are not asked
to inscribe a circle in one. Naming that the given pentagon is a figure names what
Euclid's words presuppose, and is not a restriction ([FORMALIZATION.md](../FORMALIZATION.md),
section 2, "Hypotheses").

Stage 2's `Rectilineal` and `Apart` give a figure for its area, cut into triangles. No
statement of Book IV compares the areas of figures, so it needs neither; when Book XII
does, a lemma can show that a convex figure's triangles from one corner are a checked
division using `Fitted.fan`. A lemma invoking `Fitted.fan` belongs after I.45, where it
lives: its proof cites I.13. Book Zero keeps only facts proved from the foundations alone
([FORMALIZATION.md](../FORMALIZATION.md), section 6).

Two other ways were weighed. Separate points for each figure (`A B C D E : Point`) read
well for the pentagon, but give no word for a figure of fifteen sides, and none for the
general companions. A function from `Fin n` to points brings numbers into every statement,
where a list brings them only into IV.16's count (section 4.5).

### 4.2 Inscribed, circumscribed, and touching within the side

Definitions 3 and 6 say one thing, from the figure and from the circle: each corner on the
circle. Definitions 4 and 5 say one thing too: each side touches the circle. Lean has one
word for each pair, from the figure (`Polygon.InscribedIn`, `Polygon.CircumscribedAbout`),
and the circle's word is defined as it, read the other way (`Circle.InscribedIn`,
`Circle.CircumscribedAbout`), so that each statement reads as Heath's enunciation does:
"In a given triangle to inscribe a circle" concludes `Circle.InscribedIn EFG [A, B, C]`.

"Each side touches the circumference": a side is a finite straight line, and Definition
III.2's straight line touches when it meets the circle and, produced, does not cut it. So a
side touches when the straight line through it touches (`Touches`) and the point of contact
is on the side itself, between its ends. Without the second clause a circle touching the
sides produced would count. Heath, on IV.3, draws three pairs of parallel tangents, which
form eight triangles; of six of them, "the circle touches two of the sides in each
*produced*, i.e. the circle is an *escribed* circle to each of the six triangles" (vol. 2,
p. 85). Euclid's inscribed circle touches each side within it.

### 4.3 Equilateral and equiangular

Euclid never says "regular"; he says "equilateral and equiangular", and the statements say
it his way: `Polygon.Equilateral ps ∧ Polygon.Equiangular ps`. "Regular", in our own prose,
means a figure with both, and no Lean word says it. The angle at a corner is the one its
two sides there contain, `∠ P Q R` for the neighbours P and R of Q; for a convex figure it
is less than two right angles, as Euclid's are.

### 4.4 The circumferences an inscribed figure cuts off

Euclid divides the circle by circumferences, and Book III measures a circumference by twice
the angle standing on it (`circumference`, `standing`; [the Book III brief](0004-book-III.md),
"Circumferences"). For a figure inscribed in a circle, each side cuts off the
circumference beyond it, away from the figure; it is the one on which the angle at any
other corner stands, and Definition III.9 names it so: `standing α P R Q` for the side PQ
and a corner R. `Polygon.arcs ps α` lists them, one for each side, each named by the next
corner. Book Zero's `standing_congr` makes the choice of corner immaterial, since every
other corner is on one side of PQ. III.21, through `Circumference.standing`, identifies
that measure with twice the angle at the chosen corner. Stage 3's arcs measure the same
circumference: `standing α P R Q` is `Arc.measure ⟨α, P, Q, K⟩` for a point K beyond PQ
from R (`standing_eq_circumference`). `Polygon.arcs` is a list of measures, angles in Lean,
not of stage 3's `Arc` objects; the bridges of section 7 tie the two together, and to Book
III.

### 4.5 Counting: "fifteen-angled", "one-third of the circle"

IV.16's figure has fifteen corners, which Heath does not letter, and its proof counts:
"of the equal segments of which there are fifteen in the circle ABCD, there will be five
in the circumference ABC which is one-third of the circle, and there will be three in the
circumference AB which is one-fifth of the circle" (vol. 2, p. 110). The draft says "fifteen
corners" with the list's length, `ps.length = 15`, and "fifteen of the circumference e make
the circle" with `Magnitude.sum (List.replicate 15 e)`, the sum the foundations already
define (`Magnitudes.lean`), as the prototype does; IV.16's statement needs only the count.
[FORMALIZATION.md](../FORMALIZATION.md), section 2, says that no numbers appear in a
statement or a proof. Its reason is that magnitudes are compared and added, never measured
by numbers, and a count of corners or of equal parts measures nothing. This brief proposes
that the sentence say so: "No coordinates or real numbers appear, and no magnitude is a
number; a count, of corners or of equal parts, may be." The other way, fifteen named corners
(`P₁ … P₁₅`) and sums written out, keeps the letter of the rule and reads worse; it is open
question 3.

### 4.6 What else a statement says

- **Double, a third, a fifteenth.** "Double" is a sum, as I.20's two sides are: each angle
  at the base is `∠ B A D + ∠ B A D` (IV.10). A third of the circle is the circumference
  three of which make it, and so on.
- **The angles in correspondence.** "A triangle equiangular with a given triangle" names
  each angle with its fellow, in Heath's letters: in IV.2, ABC with DEF, ACB with DFE and
  BAC with EDF.
- **Names.** Points and circles take Heath's letters, as in every book. A circle Heath does
  not name takes a Greek letter (IV.8's, `α`), as System E's general circles do.

## 5. What a construction is given

III.25 was the pilot (brief 0005, stage 4; [FORMALIZATION.md](../FORMALIZATION.md),
section 4). Its first statement was handed the whole circle whose segment it was to
complete, so the answer was among its data; restated, its construction core receives the
segment only as the points of it, with the meeting fact Euclid reads off his figure, and a
separate theorem shows that the circle it finds is the circle the segment came from. Book
IV adopts the lesson as a rule for every problem:

1. **The theorem receives what the enunciation gives, in the form Euclid's construction
   reads it, and nothing that contains the answer.** It may also take, for every choice, a
   starting point the construction is free to choose, when its users need to fix it: a
   point of the circle to fit a straight line from (IV.1) or to put a corner at (IV.2,
   IV.11), a straight line to build on (IV.10). Such a choice is quantified over, so the
   problem as Euclid states it is recovered by choosing it; it is never a hypothesis that
   supplies what is unknown. A given circle is a
   `Circle`, and its centre, when the construction needs one, is found as Euclid finds it
   ("let the centre K of the circle ABC be taken [III. 1]"), by III.1, on brief 0008's
   rule that a centre exists. A given straight line is its two ends, as in I.3 (`D₁ D₂`,
   with `D₁ ≠ D₂`). A given triangle is its corners, with `Triangle`; a given square or
   pentagon its corners, with `Polygon` and the properties the enunciation names. A
   condition on the data is a hypothesis in Euclid's terms: IV.1's straight line "not
   greater than the diameter" is not greater than any diameter.
2. **The conclusion returns what the problem asks for, with the definitions that make it a
   solution, and the objects of the construction that later proofs cite.** IV.4 returns
   the circle with its centre and its points of contact; IV.5 the circle with its centre
   and where the centre falls; IV.11 the pentagon with the equal circumferences its sides
   cut off, which IV.12 and IV.16 use.
3. **Where the data, described in full, would contain the answer, the construction core is
   kept apart from its correctness**, as in III.25: the core receives the weaker
   description, and a theorem beside it identifies what the core found.
4. **Each problem is checked against the rule** before its statement is frozen: could the
   construction be given less, and does any hypothesis name something only the answer
   provides?

For Book IV the check finds no problem that needs the third clause:

| Proposition | Given | Read by the construction | Returns | Core kept apart? |
|---|---|---|---|---|
| IV.1 | a circle; a straight line, not greater than the diameter; and, for its users, the point of the circle to fit it from | the circle, the diameter from that point (its centre by III.1), the straight line's length | the other end of the fitted straight line | no: the answer is not among the data |
| IV.2, IV.3 | a circle; a triangle; and, for IV.2's users, the point of the circle for its first corner | the circle (its centre, in IV.3); the triangle's angles | the triangle, with its angles | no |
| IV.4, IV.5, IV.8, IV.9 | a triangle, a square | its corners and sides | the circle, its centre, its contact points or where its centre falls | no: a figure's circle is not part of the figure |
| IV.6, IV.7, IV.11, IV.12, IV.15, IV.16 | a circle | the circle, its centre and diameters | the figure | no |
| IV.10 | (any straight line, "set out") | the straight line AB | the triangle on it | no |
| IV.13, IV.14 | an equilateral and equiangular pentagon | its corners, sides and angles | the circle and its centre | no |

The rule is the convention brief 0005 asked this brief to carry into Book IV, and the first
prototype (section 9) tests it on IV.1.

## 6. The statements

Every statement below is in [`Statements.lean`](../reports/crew/scratch-IV/Statements.lean)
with `sorry`, under the docstring each will carry: Heath's enunciation, taken from the
scan's text and checked against the page image, all sixteen (`heath/IV/` is transcribed
and checked again in the ground step of section 11). Each is
a problem, an `∃` returning what it constructs ([FORMALIZATION.md](../FORMALIZATION.md),
section 2). Every statement is expected `full`; the notes say where a reading was chosen.

**IV.1.** Into a given circle to fit a straight line equal to a given straight line which
is not greater than the diameter of the circle.

```lean
theorem Prop1 {C D₁ D₂ : Point} {ABC : Circle} (hC : OnCircle C ABC) (hD : D₁ ≠ D₂)
    (hle : ∀ P Q E : Point, Centre E ABC → OnCircle P ABC → OnCircle Q ABC → Between P E Q →
      len D₁ D₂ ≤ len P Q) :
    ∃ A : Point, OnCircle A ABC ∧ len C A = len D₁ D₂
```

Plain words: given a circle ABC, a point C of it, and a straight line D₁D₂ no longer than
any diameter, there is a point A of the circle with CA equal to D₁D₂. The straight line is
fitted from a point of the circle that the user chooses, as Euclid's construction allows
(his diameter BC may be drawn from any point C), and as his own uses need: IV.10 fits BD
from the point B, and IV.16 fits fifteen straight lines "in contiguity", each from the end
of the last. Heath notes as much: "if a particular point be chosen as one extremity of the
chord to be 'fitted in,' there are two solutions" (vol. 2, p. 81). So the statement says
more than the enunciation, never less. Euclid's two cases, the diameter equal to D or
greater, are the two cases of the proof. That the circle EAF meets the circle ABC is left
tacit; the proof supplies it.

**IV.2.** In a given circle to inscribe a triangle equiangular with a given triangle.

```lean
theorem Prop2 {A D E F : Point} {ABC : Circle} (hA : OnCircle A ABC) (hDEF : Triangle D E F) :
    ∃ B C : Point, Triangle A B C ∧ Polygon.InscribedIn [A, B, C] ABC ∧
      ∠ B A C = ∠ E D F ∧ ∠ A B C = ∠ D E F ∧ ∠ A C B = ∠ D F E
```

Euclid's construction begins at the point A where GH touches the circle, and any point of
the circle will serve; so the statement takes A and inscribes the triangle with its corner
there, as IV.1 fits its straight line from a given point. IV.11 and IV.16 need that: IV.16
inscribes the triangle's side AC and the pentagon's side AB from one point A.

**IV.3.** About a given circle to circumscribe a triangle equiangular with a given
triangle.

```lean
theorem Prop3 {D E F : Point} (ABC : Circle) (hDEF : Triangle D E F) :
    ∃ L M N : Point, Triangle L M N ∧ Polygon.CircumscribedAbout [L, M, N] ABC ∧
      ∠ M L N = ∠ E D F ∧ ∠ L M N = ∠ D E F ∧ ∠ L N M = ∠ D F E
```

Heath's sides LAM, MBN, NCL touch at A, B, C, so the triangle is LMN in that order. "Euclid
leaves us to satisfy ourselves that the three tangents *will* meet and form a triangle"
(Heath, vol. 2, p. 84), which follows, Heath shows, from the angles AKB, BKC, CKA at the
centre, each less than two right angles; the proof supplies it so, as a helper.

**IV.4.** In a given triangle to inscribe a circle.

```lean
theorem Prop4 {A B C : Point} (hABC : Triangle A B C) :
    ∃ (EFG : Circle) (D E F G : Point), Centre D EFG ∧ Circle.InscribedIn EFG [A, B, C] ∧
      Between A E B ∧ Between B F C ∧ Between C G A ∧
      OnCircle E EFG ∧ OnCircle F EFG ∧ OnCircle G EFG
```

The circle comes with its centre D and its points of contact, "as FGE". That the two
bisectors meet, and that the feet of the perpendiculars fall within the sides, are left
tacit; the proof supplies both.

**IV.5.** About a given triangle to circumscribe a circle.

```lean
theorem Prop5 {A B C : Point} (hABC : Triangle A B C) :
    ∃ (ABC : Circle) (F : Point), Centre F ABC ∧ Circle.CircumscribedAbout ABC [A, B, C] ∧
      (SameSideOf F A B C → ∠ B A C < ∟) ∧ (Between B F C → ∠ B A C = ∟) ∧
      (OppositeSidesOf F A B C → ∟ < ∠ B A C)
```

The last three clauses are Euclid's addition after the construction, "And it is manifest
that, when the centre of the circle falls within the triangle, the angle BAC, being in a
segment greater than the semicircle, is less than a right angle", and so on for the centre
on BC and outside the triangle [III. 31]. Heath notes that it "has no heading … in the best
MSS.; it is an explanation like that which is contained in the penultimate paragraph of
III. 25" (vol. 2, p. 90), and III.25's explanation is a clause of its statement; so is this
one. Two readings are named. "Within the triangle" is said as Euclid's reason gives it, the
centre on A's side of BC, where the segment BAC is greater than a semicircle: that is
weaker than within, so the clause says more. "Outside the triangle" is read as Euclid's
third figure draws it, beyond BC: a centre outside the triangle beyond AB, where the angle
at C is obtuse, leaves BAC acute, and the sentence read word for word would be false
there. The record will say so. Simson's observation that "Euclid does not prove that DF, EF
will meet" (Heath, vol. 2, p. 90) is answered by a helper.

**IV.6.** In a given circle to inscribe a square.

```lean
theorem Prop6 (ABCD : Circle) :
    ∃ A B C D : Point, Polygon [A, B, C, D] ∧ Polygon.InscribedIn [A, B, C, D] ABCD ∧
      Square A B C D
```

**IV.7.** About a given circle to circumscribe a square.

```lean
theorem Prop7 (ABCD : Circle) :
    ∃ F G H K : Point, Polygon [F, G, H, K] ∧ Polygon.CircumscribedAbout [F, G, H, K] ABCD ∧
      Square F G H K
```

**IV.8.** In a given square to inscribe a circle.

```lean
theorem Prop8 {A B C D : Point} (hABCD : Polygon [A, B, C, D]) (hsq : Square A B C D) :
    ∃ (α : Circle) (G : Point), Centre G α ∧ Circle.InscribedIn α [A, B, C, D]
```

**IV.9.** About a given square to circumscribe a circle.

```lean
theorem Prop9 {A B C D : Point} (hABCD : Polygon [A, B, C, D]) (hsq : Square A B C D) :
    ∃ (ABCD : Circle) (E : Point), Centre E ABCD ∧ Circle.CircumscribedAbout ABCD [A, B, C, D] ∧
      Between A E C ∧ Between B E D
```

Book I's `Square` says four equal sides and four right angles; `Polygon [A, B, C, D]` names
that the square is a figure, which IV.8 and IV.9 read off it (open question 9).

**IV.10.** To construct an isosceles triangle having each of the angles at the base double
of the remaining one.

```lean
theorem Prop10 {A B : Point} (hAB : A ≠ B) :
    ∃ D : Point, Triangle A B D ∧ len A B = len A D ∧
      ∠ A B D = ∠ B A D + ∠ B A D ∧ ∠ A D B = ∠ B A D + ∠ B A D
```

"Let any straight line AB be set out": the triangle is built on any straight line AB, so
the statement takes AB, which is more than one triangle somewhere. That B is outside the
circle ACD, which III.37 needs, is left tacit; the proof supplies it.

**IV.11.** In a given circle to inscribe an equilateral and equiangular pentagon.

```lean
theorem Prop11 {A : Point} {ABCDE : Circle} (hA : OnCircle A ABCDE) :
    ∃ B C D E : Point, Polygon [A, B, C, D, E] ∧
      Polygon.InscribedIn [A, B, C, D, E] ABCDE ∧
      Polygon.Equilateral [A, B, C, D, E] ∧ Polygon.Equiangular [A, B, C, D, E] ∧
      AllEqual (Polygon.arcs [A, B, C, D, E] ABCDE)
```

The pentagon has its corner A at a given point of the circle, as IV.2's triangle has, by
which Euclid inscribes the triangle ACD; IV.16 needs it. The last clause is a step of
Euclid's proof, "therefore the five circumferences AB, BC, CD, DE, EA are equal to one
another", returned because IV.12 cites it ("so that the circumferences AB, BC, CD, DE, EA
are equal; [IV. 11]", vol. 2, p. 102) and IV.16 counts by it. His proof of the equal angles
adds circumferences ("let BCD be added to each") by `Circumference.add`, corner by corner,
as he does; it does not cite the bridge of section 7 that would do every corner at once.

**IV.12.** About a given circle to circumscribe an equilateral and equiangular pentagon.

```lean
theorem Prop12 (ABCDE : Circle) :
    ∃ G H K L M : Point, Polygon [G, H, K, L, M] ∧
      Polygon.CircumscribedAbout [G, H, K, L, M] ABCDE ∧
      Polygon.Equilateral [G, H, K, L, M] ∧ Polygon.Equiangular [G, H, K, L, M]
```

**IV.13.** In a given pentagon, which is equilateral and equiangular, to inscribe a circle.

```lean
theorem Prop13 {A B C D E : Point} (hABCDE : Polygon [A, B, C, D, E])
    (heqs : Polygon.Equilateral [A, B, C, D, E]) (heqa : Polygon.Equiangular [A, B, C, D, E]) :
    ∃ (GHKLM : Circle) (F : Point), Centre F GHKLM ∧
      Circle.InscribedIn GHKLM [A, B, C, D, E]
```

**IV.14.** About a given pentagon, which is equilateral and equiangular, to circumscribe a
circle.

```lean
theorem Prop14 {A B C D E : Point} (hABCDE : Polygon [A, B, C, D, E])
    (heqs : Polygon.Equilateral [A, B, C, D, E]) (heqa : Polygon.Equiangular [A, B, C, D, E]) :
    ∃ (ABCDE : Circle) (F : Point), Centre F ABCDE ∧
      Circle.CircumscribedAbout ABCDE [A, B, C, D, E]
```

**IV.15.** In a given circle to inscribe an equilateral and equiangular hexagon.

```lean
theorem Prop15 (ABCDEF : Circle) :
    ∃ A B C D E F : Point, Polygon [A, B, C, D, E, F] ∧
      Polygon.InscribedIn [A, B, C, D, E, F] ABCDEF ∧
      Polygon.Equilateral [A, B, C, D, E, F] ∧ Polygon.Equiangular [A, B, C, D, E, F]
```

**IV.15, Porism.** "From this it is manifest that the side of the hexagon is equal to the
radius of the circle." Two more sentences follow before Heath's "Q. E. F.": "if through the
points of division on the circle we draw tangents to the circle, there will be
circumscribed about the circle an equilateral and equiangular hexagon", and "we can both
inscribe a circle in a given hexagon and circumscribe one about it" (vol. 2, p. 109). Heath
agrees with Heiberg that this is the one porism Proclus knew in Book IV. A porism is a claim
([FORMALIZATION.md](../FORMALIZATION.md), section 2), so all three are its clauses:

```lean
theorem Prop15.porism :
    (∀ (α : Circle) (O A B C D E F : Point), Centre O α →
      Polygon [A, B, C, D, E, F] → Polygon.InscribedIn [A, B, C, D, E, F] α →
      Polygon.Equilateral [A, B, C, D, E, F] → Polygon.Equiangular [A, B, C, D, E, F] →
      len A B = len O A) ∧
    (∀ (α : Circle) (A B C D E F : Point), Polygon [A, B, C, D, E, F] →
      Polygon.InscribedIn [A, B, C, D, E, F] α →
      Polygon.Equilateral [A, B, C, D, E, F] → Polygon.Equiangular [A, B, C, D, E, F] →
      ∃ G H K L M N : Point, Polygon [G, H, K, L, M, N] ∧
        Polygon.CircumscribedAbout [G, H, K, L, M, N] α ∧
        (∀ P ∈ [A, B, C, D, E, F], ∃ s ∈ Polygon.sides [G, H, K, L, M, N], Between s.1 P s.2) ∧
        Polygon.Equilateral [G, H, K, L, M, N] ∧ Polygon.Equiangular [G, H, K, L, M, N]) ∧
    (∀ A B C D E F : Point, Polygon [A, B, C, D, E, F] →
      Polygon.Equilateral [A, B, C, D, E, F] → Polygon.Equiangular [A, B, C, D, E, F] →
      (∃ (α : Circle) (O : Point), Centre O α ∧ Circle.InscribedIn α [A, B, C, D, E, F]) ∧
      (∃ (β : Circle) (O : Point), Centre O β ∧
        Circle.CircumscribedAbout β [A, B, C, D, E, F]))
```

The first clause is said of every equilateral and equiangular hexagon in a circle, not
only the one IV.15 draws: "the side of the hexagon" is any such hexagon's. Its proof needs
the bridges (the six circumferences are equal and make up the circle), more than "from this
it is manifest"; the record will say so (open question 6). The second and third clauses are
the general companions below, for six sides.

**IV.16.** In a given circle to inscribe a fifteen-angled figure which shall be both
equilateral and equiangular.

```lean
theorem Prop16 (ABCD : Circle) :
    ∃ ps : List Point, ps.length = 15 ∧ Polygon ps ∧ Polygon.InscribedIn ps ABCD ∧
      Polygon.Equilateral ps ∧ Polygon.Equiangular ps
```

Euclid's last step, "If therefore we join BE, EC and fit into the circle ABCD straight
lines equal to them and in contiguity, a fifteen-angled figure which is both equilateral
and equiangular will have been inscribed in it", leaves to the reader that fifteen such
straight lines close up and make a figure. Two helpers, before IV.16 in its file, supply
what he leaves tacit. `Prop16.within`: of two circumferences cut off from one point A of
the circle on one side of the diameter through A, the less ends within the greater, so that
the side AB of the pentagon falls within the circumference AC of the triangle and the
circumferences AB and BC make up AC (`Circumference.add`); this is the subtraction "in the
remainder BC there will be two of the equal segments", with the count of the prototype
`fifteenth`. And `Prop16.contiguity`, in `Statements.lean`: if n of a circumference PKQ
make the whole circle, n straight lines equal to PQ, fitted from P each from the end of the
last (IV.1), close up into an equilateral and equiangular figure whose first side is PQ.
Both are IV.16's task's to state exactly and to prove, and both cite only Book III, IV.1,
IV.2 and IV.11. His two further
paragraphs, as for the hexagon, say that a fifteen-angled figure is circumscribed about a
circle, and that a circle is inscribed in and circumscribed about a given one. They come
before his last "Q. E. F." and are not a porism; a companion states them, the general
companions for fifteen sides, and the record declares them carried by it:

```lean
theorem Prop16.further :
    (∀ (α : Circle) (ps : List Point), ps.length = 15 → Polygon ps →
      Polygon.InscribedIn ps α → Polygon.Equilateral ps → Polygon.Equiangular ps →
      ∃ qs : List Point, qs.length = 15 ∧ Polygon qs ∧ Polygon.CircumscribedAbout qs α ∧
        (∀ P ∈ ps, ∃ s ∈ Polygon.sides qs, Between s.1 P s.2) ∧
        Polygon.Equilateral qs ∧ Polygon.Equiangular qs) ∧
    (∀ ps : List Point, ps.length = 15 → Polygon ps → Polygon.Equilateral ps →
      Polygon.Equiangular ps →
      (∃ (α : Circle) (O : Point), Centre O α ∧ Circle.InscribedIn α ps) ∧
      (∃ (β : Circle) (O : Point), Centre O β ∧ Circle.CircumscribedAbout β ps))
```

**The general companions.** Euclid's "in like manner as in the case of the pentagon" (IV.15
Por., IV.16) asserts IV.12, IV.13 and IV.14 again for six and fifteen sides. "De Morgan
remarks that IV. 12, 13, 14 supply the place of the following: *Having given a regular
polygon of any number of sides inscribed in a circle, to describe the same about the
circle; and, having given the polygon, to inscribe and circumscribe a circle.* For the
method can be applied generally, as indeed Euclid practically says in the Porism to IV. 15
about the regular hexagon and in the remark appended to IV. 16 about the regular
fifteen-angled figure." (Heath, vol. 2, p. 104.) Said once, for any number of sides, they
serve both, and every later book that needs a regular figure:

```lean
theorem Prop12.general {ps : List Point} {α : Circle} (hps : Polygon ps)
    (hin : Polygon.InscribedIn ps α) (heqs : Polygon.Equilateral ps)
    (heqa : Polygon.Equiangular ps) :
    ∃ qs : List Point, qs.length = ps.length ∧ Polygon qs ∧ Polygon.CircumscribedAbout qs α ∧
      (∀ P ∈ ps, ∃ s ∈ Polygon.sides qs, Between s.1 P s.2) ∧
      Polygon.Equilateral qs ∧ Polygon.Equiangular qs

theorem Prop13.general {ps : List Point} (hps : Polygon ps) (heqs : Polygon.Equilateral ps)
    (heqa : Polygon.Equiangular ps) :
    ∃ (α : Circle) (O : Point), Centre O α ∧ Circle.InscribedIn α ps

theorem Prop14.general {ps : List Point} (hps : Polygon ps) (heqs : Polygon.Equilateral ps)
    (heqa : Polygon.Equiangular ps) :
    ∃ (α : Circle) (O : Point), Centre O α ∧ Circle.CircumscribedAbout α ps
```

Each is a companion, as FORMALIZATION, section 2, defines one: approved as a statement with
`sorry` before anyone proves it, listed in `Elements/Companions.lean`, certified and shown
on its page. Each follows Euclid's argument for the pentagon, a side or a corner at a time,
along the given figure, by induction over its corners in order; taking a corner away, as
the bridge `Polygon.arcs_sum` does, would not serve here, for the figure left is no longer
equilateral.

## 7. The bridges

A definition chooses a meaning; a bridge theorem shows that it agrees with what Euclid's
words need ([FORMALIZATION.md](../FORMALIZATION.md), section 3). These are Book IV's, each
in the scratch file with `sorry`, and the first proved as a prototype too (section 9):

| Bridge | Says | From | Home |
|---|---|---|---|
| `Polygon.arcs_sum` | the circumferences an inscribed figure's sides cut off make up the whole circle, four right angles | `Circumference.add`, `Circumference.whole` (III.20 to III.22) | Book IV's ground |
| `Polygon.equilateral_iff_arcs` | an inscribed figure is equilateral exactly when its sides cut off equal circumferences | III.28, III.29, and `Polygon.arcs_sum` (with equal sides, each circumference is less than a semicircle) | Book IV's ground |
| `Polygon.equiangular_of_arcs` | an inscribed figure whose sides cut off equal circumferences is equiangular | III.27 and `Circumference.add`: each angle stands on the circumferences of the sides it does not touch | Book IV's ground |
| `Polygon.arcs_measure` | each circumference of `Polygon.arcs` is stage 3's `Arc.measure` of the arc on that side, away from the figure, and no other corner is on that arc: the corners are in order round the circle | `standing_eq_circumference`, `OnArc`; no proposition | Book Zero |
| `Polygon.triangle_iff` | `Polygon [A, B, C]` exactly when `Triangle A B C` | none | Book Zero |

**28 October 2026 (#474).** Since [the decision of that day](../decisions/2026-10-28-iii27-iii29-swap.md),
III.27 and III.29 take circumferences that coincide (`Arc.Congruent`), and their measure forms
are the companions `Prop27.of_measure` and `Prop29.of_measure`. The bridges above compare
circumferences by measure, so where they cite III.27 and III.29 they mean those companions.

The first three tie the new words to Book III's circumferences; the fourth ties them to
stage 3's arcs, so that a reader of `Arc` and a reader of `Polygon.arcs` meet one
circumference. That an equiangular inscribed figure need not be equilateral (a rectangle)
is why the second runs both ways and the third one way only.

**Where they sit.** Each cites Book III alone, so each can stand before IV.1, and IV.16,
the porism and the general companions cite them. The main theorems of IV.11 and IV.15 do
not: Euclid proves their equal angles step by step, and a helper that did every corner at
once would conceal his argument ([FORMALIZATION.md](../FORMALIZATION.md), section 5,
"Helpers"). IV.16's last step, which he leaves to the reader, is where they belong.

## 8. Homes and owners

| Home | What goes in it | Place in the order | Owner |
|---|---|---|---|
| `Elements/Foundations/DefinitionsIV.lean` | the words of section 3, each with its docstring; they join `Certificate/axioms.lock` with the first frozen statement that reaches them, by `check_fidelity.py --write-lock` and a decisions entry | after `DefinitionsIII.lean` | the coordinator |
| `Elements/Figure/Polygons.lean` | Book Zero: the list facts about `Polygon.sides` and `Polygon.cornerTriples`, `Polygon.triangle_iff`, a figure's corners read from any corner (rotation), `Polygon.arcs_measure` | Book Zero, after `OnCircles.lean`; cites no proposition | the owner of Book Zero named in the wave's orders |
| `Elements/BookIII/Circumferences.lean` | `Circumference.add`, from stage 3 | already its home (brief 0006) | stage 3's move ([#25]) |
| `Elements/BookIV/Arcs.lean` | the three bridges that cite Book III, with the corner-deletion and separation lemmas of `Polygon.arcs_sum`'s proof and the addition of neighbouring circumferences (section 9) | Book IV's ground, after Book III, before IV.1 | Book IV's ground task |
| `Elements/BookIV/PropNN.lean` | each proposition, its helpers before it, its porism (IV.15) and companions (IV.12, IV.13, IV.14, IV.16) after it | one file each | each proposition's task |
| `Elements/Companions.lean` | the four companions' entries | | the integrator |
| `heath/IV/` | Heath's text and the definitions, from the scans: vol. 2, pp. 78–111, the Internet Archive's `thirteenbookseu00heibgoog`, leaves n90 to n123 (page N is leaf N + 12) | | the transcribers |
| `scripts/heath.py`, `scripts/scaffold_book.py`, `scripts/check_fidelity.py`, `scripts/render.py`, `Certificate/Facts.lean` | Book IV taught: `heath.BOOKS` gains `"IV": 16`; the porism of IV.15; `[IV. Def. 5]` and `[III. 16, Por.]` read; `BOOK_IV` templates and `GROUNDWORK` for `Elements.BookIV.Arcs`; `FIRST_EUCLIDEAN` 1 for Book IV, as for Books II and III; the pages and the certificate's list of books | protected paths: a tooling pull request of its own, with a decisions entry naming each file | the scripts' owner named in the orders |
| `review/IV/NN.toml` | each record at the stage `exceptions`, written with its statement | | the statement owner |
| `mishnah/IV/`, `figures/IV/`, Book IV's introduction | the commentary and the figures | after the proofs | the edition contributors |

## 9. The prototypes

WORKFLOW, section 2: "Before a fleet sails on a new kind of object, one hard statement is
proved by hand." Book IV has five new foundations, and each has its prototype in
[`docs/reports/crew/scratch-IV/`](../reports/crew/scratch-IV/). Each prototype file repeats
the words of section 3 byte for byte. Until brief 0008's rule lands, a prototype whose
construction needs the circle's centre takes it as a hypothesis (`∃ O : Point, Centre O α`),
which the final statement drops.

| Foundation | Prototype | File | State |
|---|---|---|---|
| what a construction is given (section 5) | IV.1, Euclid's construction under his sentences | `PrototypeIV1.lean` | proved: Euclid's two cases under his twelve sentences; helpers for the diameter and for the meeting of the circles EAF and ABC, which he leaves tacit |
| a figure by its corners, inscribed in a circle (`Polygon`, Defs. 3 and 6) | IV.6: the hard part every inscribing proof meets is proving `Polygon` for the figure it builds | `PrototypeIV6.lean` | proved: Euclid's route under his twenty sentences; `Prop6.polygon_of_cross` proves `Polygon` for four corners whose diagonals cross, a shared step for every quadrilateral of Book IV |
| a figure circumscribed, a circle inscribed (Defs. 4 and 5: touching within each side) | IV.4 | `PrototypeIV4.lean` | proved: Euclid's route under his eighteen sentences, by I.9, I.12, I.26, Postulate 3 and III.16's porism; helpers for the bisectors meeting within the triangle, each half-angle acute, and each point of contact within its side, the step Definition IV.4's second clause asks for |
| the circle divided (`Polygon.arcs`, the bridges) | `Polygon.arcs_sum`, for any number of sides | `PrototypeArcs.lean` | proved for any number of corners, by taking away one corner at a time. A second sailor, working independently, reported a complete proof too; the shorter was kept, and only it was checked here. Its corner-deletion and separation lemmas, and the addition of neighbouring circumferences, belong in Book IV's supporting module, `Elements/BookIV/Arcs.lean`; Book Zero keeps only facts proved from the foundations alone. The deletion and separation argument takes a point of a chord within the circle by III.2 (`BookIII.Prop2.within`, `BookIII.Prop2.triangle`), put in place of Circle 2 in review; it rests on Circle 2 still through stage 3's staged `Circumference.add` alone |
| counting parts of the circle (IV.16) | `fifteenth`: if three of AC and five of AB make the circle, and BC, the rest, is bisected at E, fifteen of BE make it | `PrototypeIV16.lean` | proved; it is arithmetic of magnitudes only |
| (recommended by the challenge) straight lines fitted in contiguity close up | `Prop16.contiguity`, IV.16's last step | to be written | not yet done: the next geometric prototype, before the fleet sails; the arithmetic above does not show the fitting, the order or the closure |

Approved by the coordinator, the prototypes' proofs may be kept in `Staging/` until their
statements' homes exist (WORKFLOW, section 2, "What proofs `Staging/` may hold").

## 10. Books I to III's rules, in Book IV

- **Postulate 5.** Every proposition of Book IV comes after I.29, so any may rest on it.
- **Superposition** stays with I.4 and I.8.
- **Circles 2 and 3.** No proof of the edition rests on them since [#60], and none of Book IV
  will: a point between two points on or within a circle is within it by III.2
  (`BookIII.Prop2.within`, with `Prop2.triangle`, `Prop2.oppositeSide` and
  `Prop2.sameSide`), never by the rule, nor by the Book Zero lemmas that still call it.
- **Citing.** A Book IV proof cites `BookI.PropN`, `BookII.PropN`, `BookIII.PropN` and
  `BookIII.Prop16.porism`; a bare `Prop1` in a Book IV file means IV.1.
- **The overlaps.** No rule of the foundations is expected to state a proposition of Book
  IV; the catalogue's check is run on each record as Books I to III's were.
- **Exceptions expected.** None restricted and none in part. The readings named in section
  6 go into the records' notes: IV.5's "within" and "outside" the triangle, IV.15's porism
  said of every regular hexagon, IV.16's count and its further claims in a companion.

## 11. The order of work

1. **This brief challenged** by readers who did not write it, as Book III's statements were
   and brief 0008 was (two challengers, each finding answered in an appendix); then
   revised, approved by the coordinator, and frozen. The owner decides the open questions
   that are foundation decisions (1 to 3).
2. **The gate.** The owner's: Books I, II and III each at 95 or more. Then the consolidation
   release ([#38]), with brief 0008's rule and stage 3 in the edition, and brief 0010's
   pass if approved, so that Book IV is scaffolded in the notation it keeps.
3. **The prototypes approved**, and kept in `Staging/` if the coordinator wishes.
4. **The ground**, each a pull request of its own: `heath/IV/` transcribed and checked
   against the page images; the scripts taught Book IV (protected paths, a decisions entry,
   a security review); `DefinitionsIV.lean` with the lock; Book Zero's `Polygons.lean`;
   Book IV's `Arcs.lean`, the bridges proved.
5. **The statements scaffolded** with `sorry` in `Elements/BookIV/` (`scaffold_book.py`),
   each with its record at `exceptions`; checked against this brief; then proofs assigned.
6. **The fleet**, best of two, the hardest first: IV.16 and the general companions, then
   IV.11 to IV.14, then the rest. Close-out, one voice, records `full`, read-through and
   acceptance, as WORKFLOW, section 10, sets out for every book.

## 12. Open questions

Each is the owner's where it is a foundation decision (1 to 3), and the coordinator's
otherwise; the recommendation is the brief's.

1. **The words.** `Polygon` and the words of section 3, with these names, in
   `DefinitionsIV.lean`? (A name other than `Polygon`, such as `Figure`, would serve;
   `Rectilineal` is stage 2's.)
2. **Convex.** `Polygon` convex, as every Book IV figure is (recommended), or a word for a
   figure that does not cross itself, convex or not, with convexity proved where needed?
3. **Counting.** FORMALIZATION's "no numbers" sentence amended to allow a count of corners
   or of equal parts (`ps.length = 15`, `List.replicate 15 e`), never a magnitude
   (recommended); or fifteen named corners in IV.16 and sums written out?
4. **IV.11's equal circumferences** returned in its statement, for IV.12 and IV.16
   (recommended)?
5. **IV.5's addition** in its statement, with "within" read as the centre on A's side of BC
   and "outside" as beyond BC (recommended)?
6. **IV.15's porism** said of every equilateral and equiangular hexagon in a circle
   (recommended), or of the hexagon IV.15 constructs?
7. **The general companions** of IV.12, IV.13 and IV.14, for any number of sides, carrying
   IV.15's porism and IV.16's further claims (recommended)?
8. **The arc's field order** (brief 0010, question 3) decides how `Polygon.arcs_measure`
   writes stage 3's arc; it should be settled first.
9. **The given square.** IV.8 and IV.9 take `Polygon [A, B, C, D]` beside Book I's
   `Square A B C D` (recommended), or Book Zero proves that every `Square` is a `Polygon`
   and the hypothesis goes?
10. **Prototypes in `Staging/`**, once approved, or kept in the scratch folder until the
    ground lands?

## Appendix: what was checked

- `lake env lean` on [`Statements.lean`](../reports/crew/scratch-IV/Statements.lean), at
  `89c5da4`, with `Staging` built: the words and the twenty-seven statements (sixteen
  propositions, the porism, four companions, five bridges and IV.16's helper
  `Prop16.contiguity`) elaborate, each with its `sorry` and no other message. That
  `Polygon.sides`, `Polygon.cornerTriples` and `Polygon.arcs` compute as their docstrings
  say was checked by `rfl` on four and five corners.
- Each prototype by `lake env lean` at `89c5da4`, with no error and no warning, and
  `#print axioms` on its theorem: no `sorryAx`, and no axiom outside the lock. The
  prototypes of IV.4, IV.6 and the circle divided rest on superposition through the
  propositions they cite (I.4, I.8 and those after), as every proof that cites them does.
  The circle divided rests on Circle 2 (`inside_of_between`) too, through the staged
  `Circumference.add` alone, which takes Book Zero's `exists_onCircle_oppositeSidesOf`
  where III.2's `Prop2.oppositeSide` would serve; the independent review of 67a4be5 put
  III.2 in place of Circle 2 in the prototype's own steps, and found that remaining path.
  No proof of the edition has rested on Circle 2 since [#60], so the bridge waits for
  `Circumference.add` to reach `Elements/` without it (stage 3's move, [#25]).
- Heath's definitions (p. 78), the sixteen enunciations, the order of each figure's corners
  in his figures, and every passage of his quoted here (pp. 81, 83, 84, 85, 90, 101, 102, 104,
  109, 110), against the page images of the scan.

## Appendix: the challenge of 19 October

Astra read the brief and its scratch Lean at `1c56974`, and the changes made while it read,
ran every scratch file and the prototypes' `#print axioms`, read each statement back in
plain words (all full, "the mathematical statement, not completion of its proof"), and
returned the brief for correction before freezing. Each finding, and what was done:

| Finding | Severity | Done |
|---|---|---|
| `Prop12.general`'s prose promised tangents at the given figure's corners, its conclusion did not; so too IV.15's porism and IV.16's further claims | material (found during the reading) | each conclusion now says that every corner of the given figure is the point of contact of a side |
| IV.10 fits BD from the point B, and IV.16 fits straight lines in contiguity, but IV.1 returned some chord, not one from a given point | material (during the reading) | IV.1 takes the point C and returns A |
| `Prop16.further` and two bridges were promised but not declared | material (during the reading) | declared in `Statements.lean` |
| The closing step's conclusion did not make the figure start from the given chord PQ | material | it returns `P :: Q :: rest`; it is now `Prop16.contiguity`, a helper of IV.16 that cites IV.1, not a bridge before IV.1 |
| IV.16 needs the triangle's side AC and the pentagon's side AB from one point A, with B within the circumference AC, and IV.2 and IV.11 returned figures placed anywhere | material | IV.2 and IV.11 take the point A for a corner; the helper `Prop16.within` gives the order of the circumferences |
| "Exactly what the enunciation gives" contradicted IV.1's and IV.10's chosen starting points | editorial | section 5, rule 1, allows a starting point quantified over, never a hypothesis that supplies the unknown |
| "Book IV has no areas" is too broad: IV.10 and IV.12 use II.11's and I.47's squares | editorial | corrected |
| (notes) `Polygon.arcs` is a list of measures, not of `Arc`s; the general companions should go round the given figure, not take corners away; `Prop16.contiguity` should be the next geometric prototype | | sections 4.4, 6 and 9 |

[issue #97]: https://github.com/jackChallis/stoicheia/issues/97
[#69]: https://github.com/jackChallis/stoicheia/issues/69
[#25]: https://github.com/jackChallis/stoicheia/issues/25
[#38]: https://github.com/jackChallis/stoicheia/issues/38
[#60]: https://github.com/jackChallis/stoicheia/issues/60
