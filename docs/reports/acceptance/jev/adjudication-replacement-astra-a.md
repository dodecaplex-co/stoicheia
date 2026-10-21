# Jev audit: replacement adjudication A

Reviewer: **OpenAI gpt-6-astra replacement A**

Source revision: **39ae65c21c6b8188c0fa53bf91b6fde3ce3b11a3**

This is a fresh replacement review because the original adjudication output was
unavailable. It does not reconstruct or attribute verdicts to the unavailable
review. The 33 assigned rows were assessed independently from their questions,
Heath, the formal declarations and relevant bridge declarations, and the pinned
figures and review records. The audit summary, expected answers, Jev answer JSONL
and earlier adjudication outputs were not consulted.

Every source path and line reference below denotes the source revision above,
read with `git show`, not the working tree's current version. All seven assigned
SVGs were rendered from that revision through `rsvg-convert -w 700` and visually
inspected; the images were passed through stdout without creating image files.
The scope judgments use the questions' stated representation conventions.
Representation judgments concern the supplied conditional bridge declarations,
not a fresh kernel check or a proof that every invocation satisfies its premises.

Result: **32 record confirmations and one record defect**, the figure of I.14.
All 33 assigned rows appear below.

## Statement scope

### 09-I.2-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/02.md:4` and its complete construction;
`Elements/BookI/Prop02.lean:18`; `review/I/02.toml:2`.
The theorem returns an endpoint L with AL equal to the given nonzero BC for
arbitrary A. Lines 22–23 explicitly handle A = B by returning C. No separation
condition on the given point is imposed, agreeing with the record's note.

### 09-I.5-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/05.md:4`, especially the two conclusions at line 10;
`Elements/BookI/Prop05.lean:19`; `review/I/05.toml:2`.
The conclusion contains both the base-angle and under-base equalities. The
produced points express the second clause's setting and do not exclude an
isosceles triangle: `Elements/BookI/Helpers.lean:27` constructs them when deriving
the unconditional base equality. Allowing equilateral triangles strengthens the
claim, as the record's representation note says.

### 09-I.8-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/08.md:4` and the setting-out at lines 6–8;
`Elements/BookI/Prop08.lean:24`; `review/I/08.toml:2`.
Two noncollinear triangles and all three corresponding side equalities imply
exactly the equality of the contained angles BAC and EDF. No orientation,
placement or side-of-line condition is imposed on the original triangles.

### 09-I.11-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/11.md:4`; `Elements/BookI/Prop11.lean:25`, including
lines 39–47 and 100–105; `review/I/11.toml:2`.
C is any point on the whole line AB, including an endpoint. The returned F is
off AB and makes a right angle with every other point of AB. Q chooses the
construction's side; it excludes no given line or point. An off-line choice
exists by `Elements/Figure/Rectangles.lean:39` (`exists_off_line`).

### 09-I.14-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/14.md:4` and lines 6–8;
`Elements/BookI/Prop14.lean:26`; `review/I/14.toml:2`.
`OppositeSidesOf C D A B` records the two arms lying on opposite sides of AB;
the angle-sum premise is the one in the enunciation. `Between C B D` gives the
required straight continuation through B. The separate figure defect below
does not change this statement's coverage.

### 09-I.17-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/17.md:4` and its final two pairs at line 24;
`Elements/BookI/Prop17.lean:25`; `review/I/17.toml:2`.
The three conjuncts cover each pair of a triangle's angles, each strictly less
than two right angles. Thus the quantifier “taken together in any manner” is
preserved, not limited to the first pair of the proof.

### 09-I.20-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/20.md:4` and the three comparisons at lines 10–14;
`Elements/BookI/Prop20.lean:25`; `review/I/20.toml:2`.
For an arbitrary triangle the conclusion gives BC < BA + AC,
AC < AB + BC and AB < BC + CA. These are all three choices of the
remaining side; no additional configuration hypothesis appears.

### 09-I.23-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/23.md:4` and the construction at lines 6–22;
`Elements/BookI/Prop23.lean:31`; `review/I/23.toml:2`.
The theorem constructs FAG at the prescribed point A, with G on the prescribed
ray AB, and with its magnitude equal to DCE. `Triangle D C E` expresses a
proper rectilineal angle. P chooses either side for F rather than restricting
the given angle or line; `Elements/Figure/Rectangles.lean:39` supplies an
off-line point when no side has been specified.

### 09-I.26-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/26.md:4`, both cases in its proof;
`Elements/BookI/Prop26.lean:22`; `review/I/26.toml:1`.
The disjunction admits the side adjoining the two equal angles or a side
opposite one of them. Exchanging B with C and E with F supplies the other
opposite-side naming. The conclusion includes every remaining side and the
remaining angle, with the already given side equality also retained.

### 09-I.29-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/29.md:4` and the three named conclusions at line 8;
`Elements/BookI/Prop29.lean:30`; `review/I/29.toml:2`.
The conclusion contains the alternate-angle equality, the exterior/interior
equality, and the same-side interior sum. The betweenness and same-side
hypotheses select the rays carrying those named angles at the two
intersections; they impose no special angle or separation on the parallel
lines and transversal.

### 09-I.32-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/32.md:4` and lines 6–8;
`Elements/BookI/Prop32.lean:48`; `review/I/32.toml:2`.
For any triangle with BC extended through C to D, the two conjuncts give the
exterior-angle equality and the sum of all three interior angles. Relabelling
the arbitrary vertices permits any side to be the produced side.

### 09-I.35-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/35.md:4`; `Elements/BookI/Prop35.lean:172` and its
case completion at lines 251–283; `review/I/35.toml:2`.
Both parallelograms share BC, and their far sides lie on one line, which their
parallelogram hypotheses make parallel to BC. No order of A, D, E, F is
assumed in the theorem. The proof includes overlap, coincident ends and the
reverse direction, so Heath's separated pictured arrangement is not a
restriction on the result.

### 09-I.38-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/38.md:5`; `Elements/BookI/Prop38.lean:27`;
`review/I/38.toml:2`.
The two triangles have equal bases on the same line and vertices on the same
parallel line. Their areas are equated without ordering the bases or requiring
distinct vertices A and D. The record's explicit allowance of a shared
vertex matches the quantified line formulation.

### 09-I.41-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/41.md:4`; `Elements/BookI/Prop41.lean:19` and
lines 23–35; `review/I/41.toml:2`.
E may be any point on AD. Since AD is parallel to BC in the given
parallelogram, the proof obtains a genuine triangle EBC and the same
parallels without an extra assumption. The conclusion is precisely twice
the triangle's area; E = A and E = D remain admitted.

### 09-I.44-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/44.md:4`, including the requested application at lines 6
and 24; `Elements/BookI/Prop44.lean:87`; `review/I/44.toml:2`.
The output is a parallelogram ABML on the entire given AB, with angle ABM
equal to the given angle and area equal to the given triangle. The chosen
side P adds a controllable output property. It excludes no valid input
triangle, rectilineal angle or nonzero AB.

### 09-I.47-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/47.md:5` and lines 7–33;
`Elements/BookI/Prop47.lean:110`; `review/I/47.toml:2`;
`Elements/BookI/Prop46.lean:30` and `:96`.
Every right triangle is admitted. The chosen representatives are outward
squares, as in the proof; I.46 constructs such squares and the supplied
`Prop46.square_eq` equates squares on equal sides regardless of which
half-plane each occupies. Thus the statement covers the square areas of the
enunciation in the stated representation, including inward representatives
by that bridge. The record explains this choice accurately.

### 09-II.2-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/02.md:4`, clarified by its setting-out at line 8;
`Elements/BookII/Prop02.lean:26`; `review/II/02.toml:1`.
For any internal cut C of AB, the sum of the rectangles AB × BC and
BA × AC equals the square on AB. The two summands preserve Heath's
“both of the segments”; no equal-cut or ordering restriction is added.

### 09-II.5-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/05.md:4`; `Elements/BookII/Prop05.lean:25` and
lines 158–175; `review/II/05.toml:1`.
C bisects AB and D is any other internal cut, on either side of C. Excluding
D = C expresses “unequal segments.” The conclusion gives the rectangle on
AD, DB plus the square on CD equal to the square on the half CB. The proof
explicitly exchanges A and B for the other order.

### 09-II.8-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/08.md:5`, especially lines 9–13 and 79–81;
`Elements/BookII/Prop08.lean:45`; `review/II/08.toml:1`.
The result holds for every internal cut C and every extension D for which
B lies between A and D and BD = CB. AD therefore represents the whole
and the chosen segment on one straight line. Four copies of the rectangle,
plus the remaining segment's square, are all present.

### 09-II.13-scope

Verdict: **fully**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/13.md:4`; `Elements/BookII/Prop13.lean:47`,
especially the internal-foot proof at lines 59–82;
`review/II/13.toml:1`.
All triangles acute at all three vertices satisfy the assumptions, which
require only B and C acute. The perpendicular is given and its foot is
proved strictly within BC. The equation states the exact twice-rectangle
deficit. Dropping acuteness at A strengthens rather than restricts the
enunciation; the record does not claim the wider scholiast's reading.

## Representation bridges

The common parallelogram declarations were checked directly:
`Elements/Foundations/Phrases.lean:48` defines the two pairs of parallel
sides, and `:53` defines `quadArea` by a diagonal's two triangles;
`Elements/Figure/Parallelograms.lean:189` states that the diagonals cross,
and `:200` states invariance under changing the diagonal;
`Elements/BookI/Prop34.lean:100` states the equal-half area formula.
Each is among the supplied definitions or bridge signatures in the
corresponding Book I representation rows.

### 11-I.35-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/35.md:6`, `Elements/BookI/Prop35.lean:172`,
`review/I/35.toml`, and the common declarations above.
The represented objects are the two parallelograms themselves. Their
`Parallelogram` hypotheses meet the premises of the crossing and
diagonal-invariance bridges, so `quadArea` measures the same figure
whichever diameter is used. The area comparison is not based on an
unjustified arbitrary dissection.

### 11-I.38-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/38.md:11`, `Elements/BookI/Prop38.lean:38`,
`review/I/38.toml`, and the common declarations above.
Although the final statement compares triangles, the proof represents
GBCA and DEFH as parallelograms. Lines 47–54 use
`Parallelogram.quadArea_rotate` and `Prop34.bisect` to identify their
areas as doubles of ABC and FED, exactly the half-parallelogram connection
in Heath's lines 15–17. Hence this row does require, and supplies, a bridge.

### 11-I.41-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/41.md:10`, `Elements/BookI/Prop41.lean:19`,
`review/I/41.toml`, and the common declarations above.
`quadArea` names ABCD's two triangles along AC. The supplied
`Prop34.bisect`, used at line 38, identifies this as twice ABC;
the given parallelogram meets its premise. The crossing and invariance
declarations support the geometrical area interpretation.

### 11-I.44-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/44.md:18`, `Elements/BookI/Prop44.lean:87`,
`review/I/44.toml`, and the common declarations above.
The output includes `Parallelogram A B M L`, rather than only an
unconstrained sum of triangles. That is the premise under which the
supplied crossing, equal-halves and diagonal-invariance declarations
connect `quadArea A B M L` to the applied parallelogram LB.

### 11-I.47-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/I/47.md:11`, `Elements/BookI/Prop47.lean:110`,
`review/I/47.toml`, the common declarations above,
`Elements/Foundations/Definitions.lean:69`, and
`Elements/BookI/Prop46.lean:96`.
`Square` gives equal sides and four right angles. The supplied
`Prop46.square_eq` states equality of the areas of squares on equal
sides, requiring their far corners to lie together on one side of each
base; it does not require the two squares to occupy the same half-plane.
These are the conditional connections needed for the outward squares and
the record's claim about inward squares.

### 11-II.10-representation

Verdict: **bridge stated**. Consequence: **record confirmed**. Confidence: **high**.

Checked `heath/II/10.md:9`, `Elements/BookII/Prop10.lean:36`,
`review/II/10.toml:74`,
`Elements/Foundations/DefinitionsII.lean:44`, `:50`, `:58`, `:63`,
and `Elements/BookII/Rectangles.lean:67`, `:85`, `:98`, `:106`, `:113`.
`rect` is a choice of area, but `Rectangle.contained` and `eq_rect`
identify any given rectangle with that choice under the relevant side
equalities. `Square.eq_sq` connects a square which is a parallelogram to
`sq`, while `Square.described` supplies both facts for the square drawn
on a chosen side. The bridges state the needed conditional connections;
the choice definition is not being accepted by itself.

## Figures

### 13-I.14-figure

Verdict: **disagrees**. Consequence: **record defect**. Confidence: **high**.

Checked the rendered `figures/I/14.svg`, particularly lines 8–18;
`heath/I/14.md:10`; `Elements/BookI/Prop14.lean:37`, especially
the constructed `Between C B E` at line 42; and
`review/I/14.toml:31`, including `figures = "pass"` at line 47.
The drawing places C, B and D on the horizontal line and E above it.
The reductio instead keeps C, B and E straight and supposes BD is not
that continuation. The caption correctly admits that drawn C, B, E
are not straight, but also describes the reversed incidence as the
illustrated supposition. This is an ordinary incidence error, not just
the necessarily unrealizable angle equality in a reductio. Disclosure
does not make it agree under the question's explicit criterion.

Required correction: draw C–B–E straight with BD a distinct ray in
the stated relative order, and explain the impossible angle equality
in the caption. The figure pass in the record requires reconsideration.

### 13-I.27-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked the rendered `figures/I/27.svg:4`;
`heath/I/27.md:10`; `Elements/BookI/Prop27.lean:25`;
`review/I/27.toml:26`.
The orders are A–E–B–G and C–F–D–G, with EF crossing the two
lines and A, D on opposite sides of EF. G is the meeting in the
direction B, D required by this reductio stage. The caption specifically
identifies the displayed unequal alternate angles as the incompatible
equality being supposed. No additional incidence error is present.

### 13-I.34-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked the rendered `figures/I/34.svg:4`;
`heath/I/34.md:6`; `Elements/BookI/Prop34.lean:20`;
`review/I/34.toml:29`.
The boundary order is A–C–D–B, with AB parallel to CD and AC
parallel to BD. BC is the drawn diameter, separating ABC and DCB.
The letters and the two triangular halves match both the setting-out
and `Parallelogram A C D B`; there is no conflicting caption.

### 13-I.42-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked the rendered `figures/I/42.svg:4`;
`heath/I/42.md:8`; `Elements/BookI/Prop42.lean:23`;
`review/I/42.toml:43`.
E bisects BC, A–F–G are collinear in that order, EF is parallel
to CG, and FG is parallel to EC. F and A stand on the same side
of BC. The separately drawn given angle D matches CEF. The caption's
case, A beyond F on FG produced, is accurately shown.

### 13-I.47-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked the rendered `figures/I/47.svg:4`;
`heath/I/47.md:11` through its second half at line 29;
`Elements/BookI/Prop47.lean:110`; `review/I/47.toml:58`.
ABC is right at A and all three squares have the specified boundary
orders and stand outward. G–A–C and B–A–H are straight;
AL is parallel to BD and CE and meets DE at L. The joined AD,
FC, AE and BK correspond to the two equal-triangle arguments.
No conflicting caption or misplaced point was found.

### 13-II.7-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked the rendered `figures/II/07.svg:5`;
`heath/II/07.md:10`; `Elements/BookII/Prop07.lean:30`;
`review/II/07.toml:34` and `:45`.
ADEB is the large square, C lies between A and B, and the diameter
DB meets CN and HF at G. C–G–N and H–G–F have the required
orders. CGBF is the small square CF, also named BG; DHGN is
the square DG. KLM marks the gnomon rather than extra vertices,
matching the proof's decomposition.

### 13-II.13-figure

Verdict: **agrees**. Consequence: **record confirmed**. Confidence: **high**.

Checked the rendered `figures/II/13.svg:4`;
`heath/II/13.md:6`; `Elements/BookII/Prop13.lean:47`;
`review/II/13.toml:24`.
The order is B–D–C, AD is perpendicular to BC, and all three
angles of ABC are acute. Thus the image satisfies the Lean's acute
B and C assumptions and also the caption's specifically stated acute
case at A. Its highlighted side AC is the side named in the deficit.

## Handback

Status: ready for integration as replacement evidence.

Changed file: this report only; no declarations, review records, audit inputs
or generated edition files were changed. Coverage: 20 scope rows, six
representation rows and seven figure rows, all at the source revision above.
No route or statement contract was changed.

Proposed record action: correct and re-review the I.14 figure and its figure
note before retaining its figure pass. Other assigned claims are confirmed
within the questions' stated scope. Records made stale: none. New or changed
dependencies: none.

Checks: source reads and semantic comparisons at the pinned revision; seven
pinned SVGs rendered and visually inspected; report row count and identifier
uniqueness checked after writing. No broad tests, Lean builds, fidelity checks
or review stamps were run. This report does not claim those checks passed.

Open item: the owner of `figures/I/14.svg` and `review/I/14.toml` must resolve
the named figure defect. The correction is outside this report's ownership.
