# Jev audit: fresh replacement adjudication B

Reviewer: OpenAI gpt-6-astra replacement B.

Source revision: `39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3`.

This is a fresh, independent replacement because the original adjudicator output was
unavailable. It does not reconstruct or claim to recover that output. The audit summary,
the Jev answer JSONL, the expected-answer fields and earlier adjudication outputs were
not consulted.

The audit JSONL was used only for the assigned rows' IDs, state and questions. Source
files cited below were read with `git show` at the exact revision above. All line numbers
and declaration names refer to that revision, not the current worktree. Each verdict
uses its row's own option language. The consequences concern the corresponding scope,
representation, commentary or figure claim; they are not a general approval of the
proposition.

All 33 assigned rows are included: 20 scope, five representation, one commentary and
seven figure rows. The full Heath enunciation and proof were read for every proposition
reviewed. All seven SVGs were also rendered at width 800 through `rsvg-convert` and
visually inspected, using pipes without creating image files.

## Scope

### 09-I.3-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/03.md`, `Elements/BookI/Prop03.lean:21` and
`review/I/03.toml` `[statement]`. Heath asks for a part of the greater line equal to
the less. `Prop3` takes the strict length inequality and distinct ends of the lesser
line, and returns E strictly between A and B with AE equal to that lesser line.
Distinct ends express a given finite straight line, not a pictured restriction.

### 09-I.6-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/06.md`, `Elements/BookI/Prop06.lean:57` and
`review/I/06.toml` `[statement]`. For any triangle ABC, the hypothesis equates
ABC and ACB; the conclusion equates their opposite sides AC and AB. There is no
ordering assumption on those sides. The proof explicitly treats either side as greater.

### 09-I.9-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/09.md`, `Elements/BookI/Prop09.lean:145` and
`review/I/09.toml` `[statement]`. The triangle hypothesis expresses noncollinear
arms of the given rectilineal angle. The returned F lies on C's side of AB and B's
side of AC, and both equality of the two angles and their sum equalling BAC are
conclusions. The record accurately describes the internal bisector.

### 09-I.12-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/12.md`, `Elements/BookI/Prop12.lean:26` and
`review/I/12.toml` `[statement]`. AB names a whole line and C is off it.
The theorem returns H on that line and makes CHP right for every other point P
on it. It does not restrict the foot to the finite interval AB, so the infinite-line
construction has its required coverage.

### 09-I.15-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/15.md`, `Elements/BookI/Prop15.lean:44`,
`Elements/BookI/Prop15.lean:101` and `review/I/15.toml`. The main theorem
gives both vertical-angle equalities for two crossing straight lines.
`Prop15.porism` separately makes all four angles together equal to four right
angles, covering the supplied bracketed porism as well.

### 09-I.18-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/18.md`, `Elements/BookI/Prop18.lean:24` and
`review/I/18.toml` `[statement]`. AB less than AC yields BCA less than ABC,
the corresponding opposite angles. The universally quantified triangle and its
arbitrary letters cover any selected unequal pair of sides.

### 09-I.21-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/21.md`, `Elements/BookI/Prop21.lean:55`,
`Elements/Foundations/Phrases.lean:37` and `review/I/21.toml`.
`InsideTriangle D A B C` states all three required same-side conditions.
The conclusion includes both BD + DC less than BA + AC and BAC less than BDC.
The record explains this meaning of “within”; neither conclusion is omitted.

### 09-I.24-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/24.md`, `Elements/BookI/Prop24.lean:88` and
`review/I/24.toml` `[statement]`. The two corresponding side equalities and
strict inequality between their included angles imply the required strict base
inequality. No placement of the auxiliary G or F is a theorem hypothesis; the
record's case note and `Prop24.cases` account for the proof's placements.

### 09-I.27-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/27.md`, `Elements/BookI/Prop27.lean:25`,
`Elements/Foundations/Phrases.lean:28` and `review/I/27.toml`.
E and F lie on the respective lines, and A and D are opposite across EF,
which makes AEF and EFD alternate rather than arbitrary equal angles.
Their equality gives parallel AB and CD. The betweenness data name the arms
of the crossing lines; they impose no extra shape on the lines.

### 09-I.30-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/30.md`, `Elements/BookI/Prop30.lean:75`,
`Elements/Foundations/Definitions.lean:76` and `review/I/30.toml`.
The statement takes both parallels to EF and concludes that AB and CD are
parallel. `hC` distinguishes the two lines being compared; this is consistent
with Euclid's two straight lines and with the definition of parallel as distinct
nonmeeting lines. It does not require EF to lie between them. The proof treats
that separate placement through `Prop30.unique`.

### 09-I.33-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/33.md`, `Elements/BookI/Prop33.lean:20` and
`review/I/33.toml`. The given sides are equal and parallel.
`SameSideOf B D A C` chooses the endpoints joined in the same directions.
The result contains both equality and parallelism of AC and BD, precisely the
two conclusions of the enunciation.

### 09-I.36-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/36.md`, `Elements/BookI/Prop36.lean:19` and
`review/I/36.toml`. Both objects are parallelograms, their bases are equal, all
four upper corners lie on one line and all four base corners on another.
The parallelogram hypotheses ensure those lines are parallel. There is no
separation or endpoint-order restriction on the bases; the conclusion equates
the two `quadArea` values.

### 09-I.39-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/39.md`, `Elements/BookI/Prop39.lean:20` and
`review/I/39.toml` `[statement]`. Equal triangles ABC and DBC share BC and
lie on the same side. The conclusion is AD parallel to BC. The distinct-apex
hypothesis expresses the two triangles and the line AD which Heath joins;
the record states that interpretation explicitly. It excludes no placement of
two distinct triangles on the given base.

### 09-I.42-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/42.md`, `Elements/BookI/Prop42.lean:23` and
`review/I/42.toml`. For any triangle and given nonstraight rectilineal angle,
the theorem returns a parallelogram whose CEF angle equals the given angle
and whose area equals the triangle. E's location on BC and F's side are
additional properties of the output, not restrictions on the input.

### 09-I.45-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/45.md`, `Elements/BookI/Prop45.lean:63`, `:327`, `:341`,
`:865`, `Elements/Foundations/Phrases.lean:196`, `:220` and
`review/I/45.toml` `[statement]` and `[representation]`.
The main theorem takes two triangles, but `Prop45.apart` takes an arbitrary
figure supplied with nonoverlapping triangles and constructs the required
parallelogram in the given angle. `figure` and `fan` cover the stated fitted
and fan forms. This is full in the disclosed representation: no theorem of
triangulation or independence from the chosen dissection is being claimed.

### 09-I.48-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/48.md`, `Elements/BookI/Prop48.lean:26`,
`Elements/BookI/Prop46.lean:96` and `review/I/48.toml`.
The theorem assumes the square on BC equals those on BA and AC together,
and concludes BAC is right. Each same-side condition says the far corners
of one square lie together on one side of its base. None chooses that side
relative to the triangle; `Prop46.square_eq` also gives equality for squares
described on equal sides. The record's either-side statement is accurate.

### 09-II.3-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/03.md`, `Elements/BookII/Prop03.lean:27`,
`Elements/Foundations/DefinitionsII.lean:58` and `review/II/03.toml`.
For any cut C between A and B the conclusion is the rectangle AB, BC equal
to the rectangle AC, CB and the square on BC. Selecting the other segment
is the same universally quantified statement with A and B exchanged.

### 09-II.6-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/06.md`, `Elements/BookII/Prop06.lean:26` and
`review/II/06.toml`. C bisects AB, D extends it beyond B, and the result is
`rect A D D B + sq C B = sq C D`. This is the whole plus added line,
the added line, and the half exactly as in Heath. Exchanging A and B covers
extension at the other end, as the record says.

### 09-II.10-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/10.md`, `Elements/BookII/Prop10.lean:36` and
`review/II/10.toml`. The midpoint and extension hypotheses give A, C, B, D
in order. The equality contains both squares AD and DB and two copies of
the sum of squares AC and CD. “Double” therefore applies to both required
areas, and an extension at the other end is covered by exchanging endpoints.

### 09-II.14-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/14.md`, `Elements/BookII/Prop14.lean:55`, `:324`,
`:334`, `:364`, `:397` and `review/II/14.toml`.
The main theorem returns a side for two triangles; the companions include
`Prop14.apart` for arbitrary supplied dissections and `Prop14.square`,
which returns all four square corners, a square, a parallelogram and equality
to the given figure's area. Thus the construction output and generality are
both supplied under the disclosed dissection convention.

## Representation

### 11-I.36-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/36.md`, `Elements/BookI/Prop36.lean:19`,
`Elements/Foundations/Phrases.lean:48`, `:53`,
`Elements/Figure/Parallelograms.lean:189`, `:200`,
`Elements/BookI/Prop34.lean:100` and `review/I/36.toml`.
The definition gives opposite parallel sides. `Parallelogram.cross` connects
its two diameters to a real interior crossing, `quadArea_rotate` makes the
area independent of which diameter is used, and `Prop34.bisect` equates it
to twice one triangular half. Each bridge takes precisely a parallelogram,
as both objects in I.36 are.

### 11-I.42-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/42.md`, `Elements/BookI/Prop42.lean:23`,
`Elements/Foundations/Phrases.lean:48`, `:53`,
`Elements/Figure/Parallelograms.lean:189`, `:200`,
`Elements/BookI/Prop34.lean:100` and `review/I/42.toml`.
The output is explicitly a parallelogram. The supplied crossing,
diameter-independence and bisection signatures therefore connect its
`quadArea` to the two triangular pieces of Euclid's parallelogram.
No arbitrary rectangle choice or undisclosed geometric premise is involved.

### 11-I.45-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/45.md`, `Elements/Foundations/Phrases.lean:183`, `:196`,
`:207`, `:220`, `:235`, `Elements/Figure/Rectilineal.lean:35`, `:56`,
`:79`, `:85`, `Elements/BookI/Prop45.lean:709`, and
`review/I/45.toml` `[representation]`; the parallelogram bridges are those
in the preceding row. `Apart` directly includes nonoverlap; `Fitted` has
geometric gluing premises, and `inside_pairwise` proves nonoverlap.
`toApart` and `area_toApart` preserve the pieces and their sum.
`Fitted.fan` states the connection under the triangle, opposite-side and
less-than-four-right-angles premises. The absent general triangulation,
dissection-independence and fan-boundary theorems are expressly outside
the disclosed claim.

### 11-I.48-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/48.md`, `Elements/BookI/Prop48.lean:26`,
`Elements/Foundations/Definitions.lean:69`,
`Elements/Foundations/Phrases.lean:53`,
`Elements/BookI/Prop46.lean:96`, `Elements/BookI/Prop34.lean:100`,
`Elements/Figure/Parallelograms.lean:189`, `:200` and
`review/I/48.toml`. `Square` gives equal sides and four right angles.
`Prop46.square_eq` identifies the areas of squares described on equal
straight lines under their same-side premises, the conditions the I.48
statement supplies for its squares. The parallelogram bridges give the
meaning of the area sum. No orientation relative to the triangle is required.

### 11-II.14-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/14.md`, `Elements/Foundations/DefinitionsII.lean:44`,
`:50`, `:58`, `:63`, `Elements/BookII/Rectangles.lean:67`, `:85`, `:98`,
`:106`, `:113`, `Elements/BookII/Prop14.lean:364`,
`Elements/Figure/Rectilineal.lean:56`, `:79`, `:85`,
`Elements/BookI/Prop45.lean:709` and `review/II/14.toml`.
`Rectangle.contained` and `eq_rect` connect the choice-defined rectangle
area to an actual rectangle with the specified side lengths.
`Square.eq_sq` connects a square that is a parallelogram to `sq`;
`Square.described` supplies both for a square built on a specified side.
The dissection bridges preserve the stated figure convention, while
`Prop14.square` supplies the drawn square. The necessary connections are
stated with their hypotheses, not inferred from the choice definition alone.

## Commentary

### 12-I.38-commentary

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/38.md`, `mishnah/I/38.md`,
`Elements/BookI/Prop38.lean`, `Elements/BookI/Prop37.lean:53` and
`review/I/38.toml`. The proof constructs GBCA and DEFH through
`Prop31.parallelogram`, equates them by I.36, applies I.34's bisection to
AB and DF, and uses `Magnitude.eq_of_add_self_eq` for the halves.
These are the commentary's mathematical steps. Its opening describes the
set-apart arrangement, without asserting that the theorem requires it;
the statement and record allow coincident vertices. Quotation accuracy,
historical attribution and voice were outside this row's question.

## Figures

### 13-I.21-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/21.md`, `Elements/BookI/Prop21.lean:34`, `:55`,
`figures/I/21.svg` and `review/I/21.toml` `[review.items]`.
The rendered D is strictly inside ABC. BD continues through D to E on AC,
with B, D, E in that order and E between A and C. The joins DC and the
marked angles BAC, CEB and BDC match the successive comparisons. The
row has no additional caption claim.

### 13-I.29-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/29.md`, `Elements/BookI/Prop29.lean:30`,
`figures/I/29.svg` and `review/I/29.toml` `[figure]`.
AB and CD are parallel; the transversal has E, G, H, F in order.
B and D lie on the same side of it. The three marked sectors are AGH,
GHD and EGB, the equal angles identified by the caption, not their
supplements. The rendered arrangement satisfies the theorem's incidence data.

### 13-I.39-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/39.md`, `Elements/BookI/Prop39.lean`,
`figures/I/39.svg` and `review/I/39.toml` `[figure]`.
E lies strictly between B and D, AE is parallel to BC, and EC is joined.
A and D are on the same side of BC and AD is not parallel to BC in
this supposed configuration. The caption specifically identifies the
incompatibility between these placements and the assumed equal triangle
areas. That is exactly the reductio exception the question allows;
the remaining incidence and side relationships agree.

### 13-I.45-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/45.md`, `Elements/BookI/Prop45.lean:63`,
especially the H-on-D explanation at line 74, `figures/I/45.svg` and
`review/I/45.toml` `[figure]`.
DB divides ABCD into the two triangles on opposite sides. K is between
B and D, H labels the same point as D, K-H-M and F-G-L are straight,
and KFGH and HGLM join to KFLM. The marked angle at K agrees with
the given angle E. The caption accurately discloses the coincident H and D
and the resulting overlap with the original figure.

### 13-I.48-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/48.md`, `Elements/BookI/Prop48.lean:26`,
`figures/I/48.svg` and `review/I/48.toml` `[review.items]`.
AD is perpendicular to AC, equal to AB and across AC from B.
DC is joined, and the right angle shown at BAC is the conclusion.
The drawing is consistent with the equal-square premise. The squares
themselves need not be drawn: Heath's illustrated comparison is between
the two triangles. There is no caption asserting an additional case.

### 13-II.10-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/10.md`, `Elements/BookII/Prop10.lean:36`,
`figures/II/10.svg` and `review/II/10.toml` `[review.items]`.
A, C, B, D occur in order with AC equal to CB. CE is perpendicular
and equal to either half. EF is parallel to AD, FD to CE; EB and FD,
produced beyond B and D, meet at G. AG is joined. The rendered
right-angle and equal-leg arrangements support the proof's triangles.

### 13-II.14-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/14.md`, `Elements/BookII/Prop14.lean:55`,
`figures/II/14.svg` and `review/II/14.toml` `[figure]`.
The figure A is a quadrilateral that can be divided into the two triangles
of the main statement. BE is greater than ED; B, G, E, F lie in order,
G bisects BF, and EF equals ED. DE is produced through E to H on the
semicircle, with GH joined. These are precisely the caption's stated case
and Heath's construction. The undrawn diagonal of A is not a conflicting
claim about its division.

## Handback

Status: ready for review.

Changed file: this replacement evidence file only. No statements, proofs, figures,
review records, stamps or generated edition files were changed. Coverage and route:
all 33 assigned questions independently adjudicated at the source revision named
above; all 33 relevant record claims confirmed, within the qualifications stated
per row. Proposed record changes: none. Records made stale: none.

Dependencies: the pinned Heath, Lean, SVG, commentary and review sources cited above.
No pending proof dependency was assessed or introduced.

Checks: source reads with `git show` and semantic comparisons at
`39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3`; seven pinned SVGs rendered
with `rsvg-convert -w 800` and visually inspected; assigned-row count checked.
No Lean build, broad tests, transcription scan audit or review stamping was run,
and none is claimed as a pass.

Open items: none within the assigned rows. This file is uncommitted for the integrator.
