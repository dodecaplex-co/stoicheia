# Jev audit: fresh replacement adjudication C

Reviewer: **OpenAI gpt-6-astra replacement C**

Source revision: **39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3**

This is a fresh replacement because the original output was unavailable. It is an
independent reading of the assigned questions and the pinned sources, not a recovery
or endorsement of that unavailable output. The audit summary, Jev answer JSONL,
earlier adjudications and the questions' `expected` fields were not read.

The question file was accessed only through projections of `id`, `state` and
`question`. Source paths and line numbers below refer to the revision above, read
with `git show`. Heath's complete enunciations and proofs were read from its
`heath/` files. Scope is judged with the attached companions and the disclosed
representations. Representation verdicts concern the conditional connections
stated by the supplied declarations, not a new kernel check.

All seven assigned Euclid figures were rendered from the pinned SVG bytes at
800-pixel width and visually inspected. Rendering used a pipe to `rsvg-convert`
and returned images in memory, without creating additional files. The figure
verdicts concern the illustrated stage, incidence, order, sides and the stated
reductio exceptions; schematic lengths were not treated as measurements.
Historical scan attribution and quotation accuracy were not newly audited.

## Statement scope

### 09-I.4-scope

Verdict: **fully**. Checked `heath/I/04.md`, its enunciation and setting-out;
`Elements/BookI/Prop04.lean:23`; `Elements/Foundations/Definitions.lean:46`;
and `review/I/04.toml` `[statement]`. The hypotheses give two triangles, the two
corresponding equal sides and their included equal angles. The conclusion keeps
all four claims: equal bases, equal triangle areas, and both pairs of remaining
angles. Noncollinearity is the meaning of triangle, not an extra case restriction.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.7-scope

Verdict: **fully**. Checked `heath/I/07.md`; `Elements/BookI/Prop07.lean:256`;
`Elements/Foundations/Phrases.lean:24`; and `review/I/07.toml` `[statement]`.
`SameSideOf C D A B` supplies a genuine base and the same-side condition. Equality
of the distances from both endpoints concludes `C = D`, precisely ruling out the
other meeting point forbidden by the enunciation. No particular position of D
inside or outside the first triangle is assumed.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.10-scope

Verdict: **fully**. Checked `heath/I/10.md`; `Elements/BookI/Prop10.lean:22`;
and `review/I/10.toml` `[statement]`. For every nonzero given finite line AB the
theorem returns D strictly between its endpoints with AD equal to DB. Both the
construction and the fact that it bisects the given line are explicit.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.13-scope

Verdict: **fully**. Checked `heath/I/13.md`; `Elements/BookI/Prop13.lean:99`
and its explanation at line 111; `Elements/Foundations/Definitions.lean:27`;
and `review/I/13.toml` `[statement]`. The two adjacent angles always sum to
`∟ + ∟`. This covers the enunciation's disjunction: when they are individually
right they also have that sum. Between C, B, D and A off CD express the
straight line set up on another that makes these two angles.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.16-scope

Verdict: **fully**. Checked `heath/I/16.md`;
`Elements/BookI/Prop16.lean:61`; and `review/I/16.toml` `[statement]`.
The side BC is produced through C to D, and the conclusion gives both strict
inequalities: CBA and BAC are each less than exterior angle ACD. Universal point
parameters allow any triangle and the corresponding relabelling of its side.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.19-scope

Verdict: **fully**. Checked `heath/I/19.md`;
`Elements/BookI/Prop19.lean:25`; and `review/I/19.toml` `[statement]`.
The greater angle ABC is compared with BCA, and the conclusion compares their
opposite sides in the required direction, AB less than AC. No placement or
additional angle restriction is imposed.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.22-scope

Verdict: **fully**. Checked `heath/I/22.md`;
`Elements/BookI/Prop22.lean:121`, including the nonzero deductions at line 130;
`Elements/Foundations/Phrases.lean:24` and `:33`; and
`review/I/22.toml` `[statement]`. The three strict triangle inequalities are
the condition in Heath's enunciation and setting-out. G on ray FE and K on P's
side supply a noncollinear triangle KFG with all three required side lengths.
The selected corner, ray and side strengthen the requested construction; they
exclude no admissible triple of given lengths.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.25-scope

Verdict: **fully**. Checked `heath/I/25.md`;
`Elements/BookI/Prop25.lean:26`; and `review/I/25.toml` `[statement]`.
Two corresponding sides are equal and BC is greater than EF; the conclusion
is exactly that their included angle BAC is greater than EDF. Triangle
hypotheses only state the objects the text already gives.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.28-scope

Verdict: **fully**. Checked `heath/I/28.md`;
`Elements/BookI/Prop28.lean:21`; `Elements/Foundations/Phrases.lean:41`;
and `review/I/28.toml` `[statement]`. The hypothesis is a disjunction of the
two tests in Heath: exterior/interior angle equality, or the sum of the
same-side interior angles being two right angles. The point orders and side
condition identify those angles and the transversal, and either test gives
AB parallel to CD.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.31-scope

Verdict: **fully**. Checked `heath/I/31.md`;
`Elements/BookI/Prop31.lean:27`, including its comment at line 30;
`Elements/Foundations/Definitions.lean:76`; and `review/I/31.toml`
`[statement]` and opening qualification. E and F determine a parallel to BC
through A because A is between them. A off BC is the presupposition of a
distinct, nonmeeting parallel through A. The enunciation asks for existence,
not uniqueness.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.34-scope

Verdict: **fully**. Checked `heath/I/34.md`;
`Elements/BookI/Prop34.lean:20` and `:100`; and `review/I/34.toml`
`[statement]`. The conclusion contains both pairs of opposite equal sides,
both pairs of opposite equal angles, and equality of the areas ABC and DCB
cut by the diameter BC of ACDB. `Prop34.bisect` also states the equivalent
double-area form described by the record.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.37-scope

Verdict: **fully**. Checked `heath/I/37.md`;
`Elements/BookI/Prop37.lean:27`; and `review/I/37.toml` `[statement]`.
Both triangles have the same base BC, their vertices lie on one of two
parallel lines and their base on the other, and their areas are concluded
equal. Using whole lines allows A and D to coincide, as the note says;
it does not omit distinct-vertex configurations.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.40-scope

Verdict: **fully**. Checked `heath/I/40.md`;
`Elements/BookI/Prop40.lean:27`, `:84` and `:129`; and
`review/I/40.toml` `[statement]`, including its companion list.
The main theorem has end-to-end bases BC, CE. `Prop40.general` allows the
four base endpoints anywhere on one line, assumes equal bases, equal areas
and same-side vertices, and returns a parallel containing both vertices,
including coincident vertices. `Prop40.join` supplies the named join when
the vertices differ. Together the declarations remove the main theorem's
placement restriction.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.43-scope

Verdict: **fully**. Checked `heath/I/43.md`, especially the two smaller
parallelograms' diameters AK and KC; `Elements/BookI/Prop43.lean:73`;
`Elements/Foundations/Phrases.lean:48`; and `review/I/43.toml`
`[statement]`. Under the disclosed reading, the parallelograms about AC meet
at K and leave the two complements EBGK and HKFD. Their areas are precisely
the conclusion. The note openly distinguishes Proclus's further arrangements;
the theorem does not purport to cover them.

Consequence: **record confirmed**. Confidence: **high**.

### 09-I.46-scope

Verdict: **fully**. Checked `heath/I/46.md`;
`Elements/BookI/Prop46.lean:30`; `Elements/Foundations/Definitions.lean:69`;
and `review/I/46.toml` `[statement]`. The output is a drawn square ADEB
on the given nonzero AB, with D and E on the side selected by any off-line
point P. The `Square` predicate explicitly requires four equal sides and
four right angles. Choosing a side strengthens the construction.

Consequence: **record confirmed**. Confidence: **high**.

### 09-II.1-scope

Verdict: **fully**. Checked `heath/II/01.md`;
`Elements/BookII/Prop01.lean:33`, `:169` and `:254`;
`Elements/Foundations/Phrases.lean:61`, `:74` and `:80`; and
`review/II/01.toml` `[statement]` and `[representation]`.
The main theorem uses three pieces; `Prop1.general` quantifies over an
arbitrary ordered list and sums the rectangles over all consecutive
segments. Its induction includes the no-cut case. Allowing a zero uncut
line adds cases and is disclosed, rather than restricting “any number.”

Consequence: **record confirmed**. Confidence: **high**.

### 09-II.4-scope

Verdict: **fully**. Checked `heath/II/04.md`, including its source note
that the 1908 text has no appended porism;
`Elements/BookII/Prop04.lean:29`; `Elements/Foundations/DefinitionsII.lean:58`
and `:63`; and `review/II/04.toml` `[statement]`.
For any internal cut C, the square on AB equals both segment squares and
two copies of their rectangle. There is no special ratio or midpoint
condition, and no supplied porism left out.

Consequence: **record confirmed**. Confidence: **high**.

### 09-II.7-scope

Verdict: **fully**. Checked `heath/II/07.md`;
`Elements/BookII/Prop07.lean:30`; and `review/II/07.toml` `[statement]`.
For an arbitrary cut C, the square on AB plus that on BC equals twice the
rectangle AB, BC plus the square on CA. This is every term of the
enunciation, with no restriction on the relative sizes of the segments.

Consequence: **record confirmed**. Confidence: **high**.

### 09-II.12-scope

Verdict: **fully**. Checked `heath/II/12.md`;
`Elements/BookII/Prop12.lean:23`, its deduction `hCAD` at line 50 and the
area calculation at line 65; and `review/II/12.toml` `[statement]`.
For every obtuse triangle with its perpendicular foot on CA, the theorem
states the square on BC as the two adjacent-side squares plus twice
rectangle CA, AD. The supplied foot is construction data; its exterior
position is derived, not an added restriction on the triangle.

Consequence: **record confirmed**. Confidence: **high**.

## Representations and commentary

### 11-I.34-representation

Verdict: **bridge stated**. Checked `heath/I/34.md`;
`Elements/Foundations/Phrases.lean:48` and `:53`;
`Elements/Figure/Parallelograms.lean:189` and `:200`;
`Elements/BookI/Prop34.lean:100`; and `review/I/34.toml` `[statement]`.
Opposite-side parallels define the parallelogram, and `quadArea` sums its
two triangles. `Parallelogram.cross` gives an interior meeting of the
diameters, `quadArea_rotate` identifies the two diagonal sums, and
`Prop34.bisect` identifies the whole with twice a half. Each bridge has
the required parallelogram premise.

Consequence: **record confirmed**. Confidence: **high**.

### 11-I.37-representation

Verdict: **bridge stated**. Checked `heath/I/37.md`;
`Elements/BookI/Prop37.lean:37` and `:46`;
`Elements/BookI/Prop34.lean:100`;
`Elements/Figure/Parallelograms.lean:189` and `:200`;
`Elements/Foundations/Phrases.lean:48` and `:53`; and
`review/I/37.toml` `[statement]` and `[review.items]`.
The supplied bridges identify a parallelogram's area independently of
the chosen diameter and express either half as a triangle. These are
the conditional connections needed for the drawn EBCA and DBCF of
Heath's proof. They remain valid when the two original triangle vertices
coincide; no bridge requires those vertices to differ.

Consequence: **record confirmed**. Confidence: **high**.

### 12-I.40-commentary

Verdict: **agrees**. Checked `mishnah/I/40.md:5` and `:7`;
`heath/I/40.md`; `Elements/BookI/Prop40.lean:44`, `:53`, `:68`,
`:84` and `:120`; `Elements/BookI/Prop38.lean:27`; and
`review/I/40.toml` `[statement]` and `[route]`.
The main/companion distinction is accurate. I.38 permits a shared base
endpoint and coincident upper vertices. The main proof's F lies on CD,
its equality of areas proves F = D directly, and the general proof
repeats this with G on ED. This matches the recorded modified route.
The modern paragraph uses the main theorem's end-to-end equal bases
and same-side, distinct vertices. Historical claims and quotations
are outside this row's question.

Consequence: **record confirmed**. Confidence: **high**.

### 11-I.43-representation

Verdict: **bridge stated**. Checked `heath/I/43.md`;
`Elements/Foundations/Phrases.lean:48` and `:53`;
`Elements/Figure/Parallelograms.lean:189` and `:200`;
`Elements/BookI/Prop34.lean:100`; `Elements/BookI/Prop43.lean:73`;
and `review/I/43.toml` `[statement]` and `[review.items]`.
The supplied parallelogram and diagonal-area declarations give the
conditional connection for the named four-sided areas under the
meeting-at-K convention. `quadArea E B G K` and `quadArea H K F D`
name the two complements by their ordered corners. The source also
provides the actual remainder decomposition in `Prop43.cut` at line 20
and uses it at lines 104–111; the verdict does not confuse this extra
proof check with the question's test of supplied bridge signatures.

Consequence: **record confirmed**. Confidence: **high**.

### 11-I.46-representation

Verdict: **bridge stated**. Checked `heath/I/46.md`;
`Elements/Foundations/Definitions.lean:69`;
`Elements/Foundations/Phrases.lean:48` and `:53`;
`Elements/Figure/Parallelograms.lean:189` and `:200`;
`Elements/BookI/Prop34.lean:100`;
`Elements/BookI/Prop46.lean:30` and `:96`; and
`review/I/46.toml` `[statement]` and `[review.items]`.
The square definition supplies the equilateral and right-angled
connection directly. The output places both far corners on one side
of AB. `Prop46.square_eq` explicitly connects squares on equal sides
to equal areas with the same-side premises retained; the supplied
parallelogram bridges explain the diagonal-area representation.

Consequence: **record confirmed**. Confidence: **high**.

### 11-II.9-representation

Verdict: **bridge stated**. Checked `heath/II/09.md`;
`Elements/Foundations/DefinitionsII.lean:44`, `:50`, `:58` and `:63`;
`Elements/BookII/Rectangles.lean:67`, `:85`, `:98`, `:106` and `:113`;
`Elements/BookII/Prop09.lean:33`; and `review/II/09.toml` `[statement]`
and `[review.items]`. `Rectangle.contained` and `Rectangle.eq_rect`
connect the chosen area to any qualifying drawn rectangle.
`Square.eq_sq` retains its parallelogram premise, while
`Square.described` supplies both that premise and equality with `sq`
for an I.46 square on a selected side. These are adequate conditional
connections for the square areas in II.9; the choice definition alone
is not used as evidence.

Consequence: **record confirmed**. Confidence: **high**.

## Figures

### 13-I.6-figure

Verdict: **agrees**. Checked and rendered `figures/I/06.svg`; read
`heath/I/06.md`; `Elements/BookI/Prop06.lean:57`; and
`review/I/06.toml` `[figure]` and `[review.items]`. D lies strictly
between A and B, DB is highlighted, DC is joined, and the triangle DBC
is the contained part of ABC. The caption explicitly identifies the
supposed greater AB and its supposed cut DB equal to AC. That
incompatible metric supposition is the reductio stage, not a claim
that the picture realizes all the equalities simultaneously. No
additional incidence or order error is present.

Consequence: **record confirmed**. Confidence: **high**.

### 13-I.26-figure

Verdict: **agrees**. Checked and rendered `figures/I/26.svg`; read
`heath/I/26.md`; `Elements/BookI/Prop26.lean:22`; and
`review/I/26.toml` `[figure]` and `[review.items]`. G lies between
B and A and is joined to C; H lies between B and C and is joined
to A. The triangle labels A/B/C and D/E/F correspond correctly.
The caption expressly separates the two supposed inequalities and
says both stages appear in one drawing. Thus G and H are not being
asserted as one simultaneously realizable metric construction.

Consequence: **record confirmed**. Confidence: **high**.

### 13-I.33-figure

Verdict: **agrees**. Checked and rendered `figures/I/33.svg`; read
`heath/I/33.md`; `Elements/BookI/Prop33.lean:20`; and
`review/I/33.toml` `[review.items]`. AB and CD are the equal
horizontal sides, with A and C at the right ends, B and D at the
left ends. AC and BD join the endpoints in the same directions and
are parallel. BC is the common interior join; B and D are on the
same side of AC, as the Lean hypothesis requires.

Consequence: **record confirmed**. Confidence: **high**.

### 13-I.40-figure

Verdict: **agrees**. Checked and rendered `figures/I/40.svg`; read
`heath/I/40.md`; `Elements/BookI/Prop40.lean:27`; and
`review/I/40.toml` `[figure]` and `[review.items]`. B, C, E lie
in that order on equal adjacent bases. F is strictly between C and
D, AF is parallel to BE, FE is joined, and A and D are on the same
side of BE. The greater drawn area of DCE than ABC is precisely
the incompatibility expressly identified by the caption's impossible
equal-area supposition. AD's slope and AF's level placement agree
with the caption's description of this drawing.

Consequence: **record confirmed**. Confidence: **high**.

### 13-I.46-figure

Verdict: **agrees**. Checked and rendered `figures/I/46.svg`; read
`heath/I/46.md`; `Elements/BookI/Prop46.lean:30`, including the
construction at line 35; and `review/I/46.toml` `[review.items]`.
AC is perpendicular to AB, D is on ray AC between A and C,
ADEB is the square on AB, DE is parallel to AB and BE to AD.
Both far corners lie on the same side of AB. The statement does
not require C to occur in the returned output.

Consequence: **record confirmed**. Confidence: **high**.

### 13-II.3-figure

Verdict: **agrees**. Checked and rendered `figures/II/03.svg`; read
`heath/II/03.md`; `Elements/BookII/Prop03.lean:27`; and
`review/II/03.toml` `[review.items]`. C lies between A and B;
CDEB is the square on CB. ED is extended through D to F, with
AF parallel to CD and BE. The whole rectangle ABEF is divided
into ACDF and CDEB, matching the two summands of the theorem.
The letters identify the same corners as the proof.

Consequence: **record confirmed**. Confidence: **high**.

### 13-II.12-figure

Verdict: **agrees**. Checked and rendered `figures/II/12.svg`; read
`heath/II/12.md`; `Elements/BookII/Prop12.lean:23` and its
exterior-foot deduction at line 50; and `review/II/12.toml`
`[statement]` and `[review.items]`. BAC is obtuse, C, A, D
are collinear with A between C and D, and BD meets that line
at a right angle at D. BC is the opposite side emphasized in
the drawing. AD is the exterior portion used in the excess
rectangle, not an internal cut.

Consequence: **record confirmed**. Confidence: **high**.

## Handback

Status: ready for review. Coverage: all **32** assigned rows, with no omissions.
The verdicts confirm the relevant record claims within the questions' scope;
this is not a general signoff on each proposition.

Changed file: `docs/reports/acceptance/jev/adjudication-replacement-astra-c.md`
only. No Lean declaration, review record, generated page or foundation changed.
No record entries are proposed, and no records were made stale.

Dependencies: the pinned Heath transcriptions, Lean sources, definitions,
review records and SVGs cited above. No pending proof dependency was introduced.

Checks: source inspection at
`39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3`; seven pinned SVGs rendered and
inspected; assigned-ID completeness and whitespace checked on this evidence
file. No broad tests, Lean builds, kernel replay, transcription comparison
against scan images or review stamping were run.

Open items: none within this assignment. The evidence file is left uncommitted
for the integrator.
