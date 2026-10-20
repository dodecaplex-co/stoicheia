# Brief 0013: rectilineal figures given by their outlines

*19 October 2026. A draft for the owner's approval. Nothing is frozen, and nothing in `Elements/`, the foundations, the lock or the review records changes with this draft.*

This brief proposes the missing ground beneath I.45 and II.14: a figure described by its boundary, a proved division into triangles covering exactly its region, and a proof that every such division gives the same area. The constructions then apply to that area.

The proposal follows [WORKFLOW, section 2](../WORKFLOW.md), and [FORMALIZATION, sections 2, 3, 6 and 7](../FORMALIZATION.md). The accompanying statements belong in `Staging/Figures/`. Their geometric proofs await approval. The derivations already written test the interfaces and remain conditional on the statements containing `sorry`.

Base: main at `39ae65c`. The statements were drafted by two first mates, one for the
statements and one for the proof route, merged under the coordinator's rulings, and
challenged once by a reader who wrote none of them (appendix). The probe of 19 October
and the prototype proofs of section 8 are evidence for the route, not approval of it; the
checks in section 10 belong to the revision delivered.

## 1. The figures admitted

Heath's definitions, quoted from [the repository transcription](../../heath/I/front.md)
(vol. 1, pp. 153–155), are:

> 13. A boundary is that which is an extremity of anything.

> 14. A figure is that which is contained by any boundary or boundaries.

> 19. Rectilineal figures are those which are contained by straight lines, trilateral figures being those contained by three, quadrilateral those contained by four, and multilateral those contained by more than four straight lines.

> 20. Of trilateral figures, an equilateral triangle is that which has its three sides equal, an isosceles triangle that which has two of its sides alone equal, and a scalene triangle that which has its three sides unequal.

> 21. Further, of trilateral figures, a right-angled triangle is that which has a right angle, an obtuse-angled triangle that which has an obtuse angle, and an acute-angled triangle that which has its three angles acute.

> 22. Of quadrilateral figures, a square is that which is both equilateral and right-angled; an oblong that which is right-angled but not equilateral; a rhombus that which is equilateral but not right-angled; and a rhomboid that which has its opposite sides and angles equal to one another but is neither equilateral nor right-angled. And let quadrilaterals other than these be called trapezia.

> 23. Parallel straight lines are straight lines which, being in the same plane and being produced indefinitely in both directions, do not meet one another in either direction.

These quotations were checked against the repository transcription, not against the page images during this task.

Definition I.13 gives the word the outline formalises: a boundary is an extremity, here
the finite straight lines that end the figure. Definitions I.20 to I.22 classify triangles
and quadrilaterals. They do not impose convexity on every multilateral figure. Definition I.23 concerns whole straight lines; the sides bounding a figure are finite straight lines.

**The proposed domain is a nonempty bounded rectilineal region with finitely many boundary sides, described by finitely many simple closed contours.** Concave figures, holes, separate pieces and isolated contacts at corners are admitted. Infinite boundaries, zero-area appendages and a crossing traversal treated as a single simple contour are excluded.

The outline contains no division or proof that a division exists.

### Corners and simplicity

Each contour is a list of distinct vertices in cyclic order, with at least three vertices. Consecutive vertices determine its finite sides, including the last joined to the first.

Different sides of one contour meet only at a common endpoint. Because the vertices are distinct, such sides are neighbours in the cyclic list. A repeated closing vertex is not stored.

A true corner is a meeting of sides that do not lie on one straight line. The input may also contain redundant collinear vertices. `loop_normalise` must remove those vertices while preserving both boundary and region. This accommodates subdivisions introduced where another boundary meets a side.

Either direction round a contour is allowed, and any vertex may come first. `loop_reverse` and `loop_rotate` state the required invariance.

### Holes, nesting and separate pieces

The outline is a finite family of contours. Their interiors are either disjoint or nested. They have no shared side and do not cross transversely.

Ordinary holes have boundaries disjoint from the outer boundary and from one another. To preserve the edition's existing scope, isolated contacts are also admitted: a corner may meet another corner or the interior of another contour's side. The formal condition requires every intersection of two boundaries to be a listed vertex of at least one of them. Together with nesting or disjoint interiors, this excludes shared segments and transverse crossings.

Maximal contours give the outer boundaries of separate pieces. A contour immediately inside one of them bounds a hole. A further contour inside that hole encloses an island. Nesting may continue to any finite depth.

This retains the reading adopted in brief 0006 on 18 October. Excluding holes would restrict the enunciation under that reading. Excluding separate pieces or corner contacts would also narrow what `Apart` currently admits. The proposed theorem `apart_has_outline` makes preservation of that existing domain an explicit obligation.

An internal edge shared by two triangles is not an outline edge. Extracting an outline from an `Apart` must split partial shared edges and remove internal edges before tracing its contours.

## 2. The region comes from the outline

For a point off one contour, take a ray whose supporting straight line avoids every vertex. Count the sides that its ray crosses in their interiors. The point lies inside when that count is odd. Points on finite boundary sides are included separately.

The definition uses incidence, betweenness, rays and finite lists. Natural numbers count sides and crossings; they never measure a length, angle or area.

Three obligations accompany the definition:

1. `good_ray_exists`: every point off the boundary admits such a ray.
2. `crossing_parity_independent`: all good rays from that point give the same parity.
3. `loop_inside_iff`: any chosen good ray therefore decides the defined interior.

The existential ray in `loopInside` is not a substitute for the second theorem.

For several contours, a point off every boundary is inside the figure when it lies inside an odd number of contours. Every boundary point is included. Thus one outer contour with unnested holes gives the outer closed region with the holes' strict interiors removed. `region_with_holes` states this equality, including the boundary cases.

Further bridges make the interpretation accountable:

- `triangle_region` agrees with the existing `OnOrInsideTriangle`.
- `convex_loop_region` proves simplicity and identifies the loop region with
  `ConvexRegion` for every strictly convex `ConvexOutline`.
- `convex_supporting_side` identifies a strictly convex figure's finite side
  on its supporting line, using `ConvexRegion`.
- `outline_bounded` proves boundedness.
- `outline_boundary` identifies the supplied contours with the boundary of the region, using triangular neighbourhoods.
- `same_boundary_region` proves that different valid descriptions of the same boundary give the same region.
- `outline_normalise` removes redundant vertices throughout a family of contours.

The ray rule is recommended because its choices and exceptional cases can be stated with existing synthetic vocabulary. Its cost is substantial: finite avoidance, parity changes at vertices, local separation and boundary cases all require proof.

Parity of triangles from a reference point would instead require independence from that point and careful treatment of points on the auxiliary segments. It would also place triangles in the definition whose purpose is to precede division. A connectivity definition would require polygonal paths, an exterior component and a polygonal separation theorem before membership could be used. Neither alternative removes the difficult separation work.

## 3. Divisions

`Covers R.pieces X` means that X lies on or inside one triangle of `R : Apart`.
`Covers` takes a list of triangles, and
`Divides (U : Point → Prop) (R : Apart)` says that their closed union is exactly U.
For an outline F the contract is `Divides F.region R`:

```text
Covers R.pieces X if and only if F.region X, for every point X.
```

The two directions exclude both triangles reaching outside the figure and points of
it left uncovered. `Apart` already requires nondegenerate triangles, at least one
triangle, and pairwise disjoint interiors.

- `division_exists` supplies an `Apart` division for every outline.
- `convex_fan` returns an `Apart` whose pieces are exactly `fan cs`, dividing
  `ConvexRegion cs`. Its derivation uses `fan_triangle`, `fan_apart` and
  `fan_covers` from `ConvexCover.lean`; the length condition supplies nonemptiness.
- `apart_has_outline` says every previously admitted `Apart` has an outline with
  exactly its closed coverage.

`ConvexOutline` is strict, so every triangle of its unfiltered `fan` is
nondegenerate. General loops permit redundant collinear corners and have a separate
normalisation theorem. No filtered fan or weaker convex predicate is introduced.

The existing checked fan has a further bridge, `BookI.Staging.Prop45.fan_boundary`. It connects its exact stated corner list to the region covered by its exact triangle list. Since that bridge may use `Fitted.fan`, whose proof cites I.13, its home is beside I.45, not in Book Zero.

## 4. Content and the figure's area

The central theorem does not mention outlines:

```lean
theorem Apart.area_eq_of_same_region (R S : Apart)
    (h : ∀ X : Point, Covers R.pieces X ↔ Covers S.pieces X) :
    R.area = S.area
```

It compares arbitrary supplied divisions covering the same points. Their triangle counts may differ. They may contain extra vertices, vertices inside the figure, and edges ending partway along other edges. Connectivity, convexity and the absence of holes are not hypotheses.

`Outline.area` selects an area realised by a division, using `Classical.epsilon`:

```lean
noncomputable def Outline.area (F : Outline) : Area :=
  Classical.epsilon fun a : Area => ∃ R : Apart, Divides F.region R ∧ R.area = a
```

Its definition depends only on the outline, but that observation alone does not establish the intended meaning. `division_exists` supplies a witness, and `Apart.area_eq_of_same_region` supplies uniqueness. Together they yield:

- `divisions_equal`: two divisions of one outline have equal sums.
- `area_eq`: every division gives the selected area.
- `area_congr`: equal regions have equal areas.
- `area_of_same_boundary`: equal boundaries have equal areas.
- `convex_fan_area`: the explicit convex fan computes that area.

The selected area is not presented as established until those dependencies are proved. No subtraction of hole areas is needed. The triangles covering the filled region supply an ordinary sum of existing triangle magnitudes.

### The classical debt

David Hilbert's theory of content is a generous guide to this work: it separates
subdivision from independence of subdivision, precisely the distinction we need.
We gratefully follow that classical argument, adapted to our triangle magnitudes.

[Brief 0006, "The tacit step"](0006-statements.md#the-tacit-step-for-the-gap-catalogues)
records the reference: *Grundlagen der Geometrie* (1899), chapter IV; in
E. J. Townsend's translation, [*The Foundations of Geometry*](https://www.gutenberg.org/ebooks/17384)
(1902), chapter IV, section 20, theorem 29 and the following definition.
It also records Hilbert's acknowledgement in section 18 of Gérard's thesis (1892)
and *Géométrie plane* (1898), F. Schur's work in the proceedings of the Dorpat
naturalists' society (1892) and his *Lehrbuch der analytischen Geometrie* (1898),
and an article by O. Stolz in the *Monatshefte für Mathematik und Physik* (1894).
These debts belong with the eventual account too. This attribution follows the
checked account in brief 0006; this task has not rechecked the historical pages.

Hilbert proves independence for the measure he develops from his foundations.
Here the theorem must concern the existing primitive `△ A B C`, with System E's
area rules and the magnitude laws already in the library. Historical credit
identifies the argument and supplies no Lean premise.

## 5. I.45, II.14 and their existing forms

**Recommendation: retain the main theorems and add prominently displayed outline companions.**

This follows FORMALIZATION, section 2, which keeps Euclid's worked configuration under his sentences and places the general statement beside it.

The current `BookI.Prop45` takes two triangles, ABD and DBC, without requiring their interiors to be disjoint. Its conclusion is a parallelogram equal to their sum. The current `BookII.Prop14` likewise returns a side whose square equals a two-triangle sum. Both remain true even when the triangles overlap. Neither is, by itself, a theorem about their union.

The proposed general statements are:

| Staged declaration | Input | Conclusion | Certificate name |
|---|---|---|---|
| `Elements.BookI.Staging.Prop45.outline` | an `Outline` and a nondegenerate given rectilineal angle | a parallelogram in that angle, equal to the outline's area | `I.45 outline` |
| `Elements.BookII.Staging.Prop14.outline` | an `Outline` | a drawn square, also a parallelogram, equal to the outline's area | `II.14 outline` |
| `Elements.BookII.Staging.Prop14.outline_side` | an `Outline` | a side whose square equals that area | `II.14 outline_side` |

Their proofs obtain a division, apply the existing construction and use `area_eq`. I.45 still constructs one triangle's parallelogram and applies each subsequent one. II.14 still constructs a rectangle and then its equal square.

No `two_triangles` corollaries are staged under the recommended policy: they
would duplicate the unchanged main theorems' types. If the alternative policy below
is chosen, `Prop45.two_triangles` and `Prop14.two_triangles` would retain those exact
contracts, with `type_of%` checks against the old statements. They would follow
from the sum constructions, including overlapping triangles, without pretending
that an unchecked sum is the area of their union.

The existing `append`, `sum`, `apart`, `figure`, `fan`, `rectangle` and `square` declarations retain their types and meanings. In particular, `Prop45.figure` continues to take `Rectilineal`; it is not silently reassigned to `Outline`.

For the reviewers' statement objection to be answered, the outline companion must be displayed as the statement carrying the whole enunciation, with its certificate and its proved dependencies. It must not be hidden behind a full-scope label attached to the unchanged two-triangle theorem. The record must distinguish the two.

If the owner instead wants `Prop45` and `Prop14` themselves to take outlines, that requires a separate frozen-statement correction and a decision about the placement of Heath's sentences. The alternative would need the `two_triangles` forms described above to preserve
the old contracts; this draft recommends the existing companion policy.

### Consumers inspected

No existing declaration changes type in this proposal, so there are no breaking declaration consumers.

The plan identifies these consumers and representation accounts for reconciliation:

| Files | Required attention when the proved work moves |
|---|---|
| `Elements/BookI/Prop45.lean` | new companions and fan bridge; distinguish old sum statements from outline statements |
| `Elements/BookII/Prop14.lean` | new companions; its main proof calls `BookI.Prop45`, and its sum construction calls `BookI.Prop45.sum` |
| `Elements/Companions.lean` | retain existing entries and register the approved new companions |
| `Elements/Foundations/Phrases.lean` | update the account of the old representations without changing their definitions |
| `Elements/Figure/Rectilineal.lean` | reconcile explanatory references with the new bridges |
| `review/I/45.toml`, `review/II/14.toml` | scope, companions, representation and passage notes |
| `review/terms.toml` | disposition of the representation tag |
| `mishnah/I/45.md`, `mishnah/II/14.md` | explain the proved boundary and content results |
| `book/I/45.md`, `book/II/14.md`, `book/names.md` | regenerate from the integrated sources |

The first mate reports no other direct mathematical consumer of either main
theorem outside these proposition files. The companions registry imports both.
The coordinator must repeat the consumer search at promotion.

The book briefs, FORMALIZATION's representation table, brief 0006's status account, the two gap catalogues, and generated certificate and programme summaries also need reconciliation. Historical reports should remain historical, with a pointer to the completed repair where appropriate.

## 6. What may be proved before approval

Before approval, WORKFLOW, section 2, permits interface derivations and explicitly approved prototypes.

The accompanying text contains these interface derivations:

- `loop_inside_iff` from ray independence.
- `divisions_equal`, `area_eq`, `area_congr`, `area_of_same_boundary` and `convex_fan_area` from the staged bridges.
- The outline construction companions from division existence, content and the existing constructions.
- `convex_fan` from the existing convex fan interfaces.

A derivation depending on a stub proves no completed geometric result.

The own proofs of ray existence and invariance, boundary identification,
normalisation, arrangement and cell selection, general division, extraction of
outlines, content and the checked fan's boundary bridge wait for approval. Prototype proofs
of the first lemmas of the route (section 8) are on the branch `lean/figures-staging`,
stacked on this brief: proved in `Staging/Figures/` so that the route could be tried
before the statements are frozen. WORKFLOW, section 2, lets `Staging/` hold the proofs of a
prototype only once the coordinator has approved it, so those proofs land only with that
approval (decision 6); the brief and its statements can land without them.

No proof task includes permission to add an axiom, change a frozen statement or weaken a check.

## 7. Homes and owners

All figure words and facts use `Elements.Figures` now and on promotion.
Only the book companions use `Elements.BookI.Staging` or `Elements.BookII.Staging`;
they lose `Staging` on promotion. Staged copies and obsolete checks are removed
in the same change, so no declaration is duplicated.

Each proposed home below requires approval; names of future files are proposals, not
links. No staged fact cites a proposition of the *Elements*: the prototype's one use of I.21
(the straight line from a corner through a point inside a triangle meets the opposite
side) was replaced by `inside_through`, from the crossbar, so Book Zero can hold them.

| Staged file or group | Eventual home | Writer responsible on promotion |
|---|---|---|
| `Convex.lean`, `Loops.lean`; definitions in `Avoid.lean`, `Cells.lean`, `Content.lean`, `OutlineArea.lean` | `Elements/Foundations/Figures.lean` | coordinator |
| `Sums.lean` | `Elements/Figure/Sums.lean` | assigned sums contributor |
| `Closed.lean`, `Avoid.lean` theorems | approved Book Zero modules | assigned finite-geometry contributor |
| `ConvexCover.lean`, `ConvexArea.lean`, and the prototype's `ConvexFacts.lean` and `ConvexAreaHelpers.lean`; convex precursors in `Arrangement.lean` | approved Book Zero convex modules | one writer per file, named by coordinator |
| `Cells.lean`, `Content.lean` theorems, and the prototype's `ExtHelpers.lean` and `CutHelpers.lean` | approved Book Zero cells and content modules | cut and content contributors, with separate files |
| `Outline.lean` | `Elements/Figure/Outlines.lean` | outline contributor |
| `Arrangement.lean`, except the optional diagonal route | `Elements/Figure/Arrangements.lean` | arrangement contributor |
| optional D5 to D7 in `Arrangement.lean` | approved shared Book I module after the latest cited proposition | diagonal contributor |
| `Division.lean`, `OutlineArea.lean` theorems | `Elements/Figure/Divisions.lean` | division contributor |
| `BookI.lean` | `Elements/BookI/Prop45.lean` | I.45 contributor |
| `BookII.lean` | `Elements/BookII/Prop14.lean` | II.14 contributor |

The new words are `SimpleLoop`, `ReducedLoop`, `GoodRay`, `RayCrosses`,
`crossingCount`, `loopBoundary`, `loopInside`, `loopRegion`, `CompatibleLoops`,
`Outline` and its fields, `Outline.boundary`, `Outline.depth`, `Outline.inside`,
`Outline.region`, `singleOutline`, `RegionBoundary` and `Outline.area`.
They join `sides`, `ClosedSide`, `Half`, `ConvexOutline`, `ConvexRegion`, `fan`,
`Covers`, `fanSum`, the cells and `Divides`, staged here too, with no competing
definitions.

The reachable vocabulary and generated auxiliaries join `Certificate/axioms.lock` through the existing lock procedure, with a decisions entry when approved statements use them. The axioms remain unchanged. Any required model and lock synchronisation follows the existing checks.

Book Zero imports no proposition. In particular, it does not call `Fitted.fan`, II.14's area-positivity helper or I.21. The checked fan bridge stays beside I.45.

The integrator owns `Elements/Companions.lean` and generated output. An independent reviewer owns the renewed semantic reviews. The edition contributor owns the assigned commentary and gap-account changes. The approved orders must give each file exactly one writer.

The proposed vocabulary does not replace brief 0012's convex `Polygon`. Any sharing with that draft needs an agreed interface; this work does not depend on Book IV.

### Records and tags

This draft changes only new staging files and this brief. It makes no production
review record stale and stamps none.

Moving the work into the two proposition files makes `review/I/45.toml` and `review/II/14.toml` stale. Their owners must review and stamp the integrated revision. Any additional consumer whose statement or Lean file changes is listed separately.

While existence, coverage or content remains unproved, retain `figure-with-dissection` as a limitation of the delivered edition. The recommended interim record correction is:

```toml
scope = "restricted"
short = "figures supplied with a checked division into triangles"
hypotheses = [
  "A division into non-overlapping triangles is supplied with the figure (`Apart` or `Rectilineal`); existence from an outline is not yet proved."
]
```

That correction revises the earlier full-scope decision and needs approval; this draft does not make it.
The interim correction also reconciles both records' statement and representation
notes, the corresponding book-brief coverage claims (`docs/briefs/book-I.md`,
`docs/briefs/book-II.md`) and the displayed page explanations at the same revision:
claims that the supplied-division companions carry full coverage are replaced by the
statement that they construct the required figure for a supplied checked division, with
outline coverage and independence of division unproved. A suitable `[statement].note`:

```toml
note = "The construction equals a supplied triangle sum; outline coverage and independence of division remain unproved."
```

After the complete repair, the proposed records say `scope = "full"` through the outline companions. Remove `figure-with-dissection` as a page-wide limitation, while retaining its registry entry for historical uses and explaining the older supplied-division interfaces. Retain an accurate note that the main theorems are two-triangle sum statements. II.14's `side-not-square` note can remain explicitly attached to its main and side forms; the outline companion returns the drawn square.

The construction route remains `euclid`, with the supporting boundary and content theory described separately. Proposed passage notes identify division existence and area independence as proved support for the whole-figure step. The figures must be reviewed against the final account.

## 8. The proof route

The recommended route is convex-cut induction for content, ray parity for loop
regions, and a finite arrangement of side lines for general division. All geometric
operations and inductions are finite. Lean 4.35 core supplies the list and natural
number machinery; this package has neither Mathlib nor Batteries. Natural numbers
count corners, crossings and tiles. They do not measure geometry.

### Evidence already available

The probe of 19 October has two Lean files, kept unbuilt as scratch proofs (WORKFLOW,
section 2) in [`docs/reports/crew/scratch-figures/`](../reports/crew/scratch-figures/):
`BoundaryBridge.lean` and `FanArea.lean`. It proves the closed-triangle
half-plane bridge, exact coverage of a strictly convex quadrilateral by its two
fan triangles, and `fanArea_rotate`, which moves the fan across one edge under
explicit separation hypotheses, for a list of arbitrary finite length. The first
mates report rechecking both files and finding no `sorryAx`, Postulate 5 or
superposition in their printed dependencies. Those are their checks, not new
checks performed in this delivery. The library's `quadArea_rotate_of_cross` is
already proved.

On 19 October the route's first lemmas were proved as a prototype, on the branch
`lean/figures-staging`, stacked on this brief, two sailors to each hard lemma and the
better proof kept. On that branch each of the following is proved in `Staging/Figures/`
with no `sorry` in its dependency closure, no new axiom, and neither Postulate 5 nor
superposition among the axioms `#print axioms` reports (22 theorems); in the brief's
own statements they stay `sorry`:

- A1, `Sums.lean`: `sum_perm`, `sum_flatMap`, `sum_exchange`, `sum_filter_ne_zero`;
- A2 and A4, `Closed.lean`: `closed_triangle_sides`, `area_cut_closed`,
  `triangle_cut_cover`;
- A3, `Avoid.lean`: `triangle_point_avoiding`, `small_triangle`;
- B1 to B4, `ConvexCover.lean` and `ConvexArea.lean`, with their shared facts in
  `ConvexFacts.lean`: `ConvexOutline.rotate`, `ConvexOutline.reverse`,
  `convexRegion_rotate`, `fan_triangle`, `fan_apart`, `fan_covers` (the boundary bridge
  for every strictly convex outline), `fanSum_rotate` and `fanSum_reverse` (the fan has
  one sum from every corner, either way round); and so the derivation `convex_fan`;
- B0, B5 and B6, `Cells.lean` with `ExtHelpers.lean` and `CutHelpers.lean`:
  `triangle_cell`, `fan_insert_between`, `boundary_fan_sum`, `convex_extreme_iff` and
  `convex_area_ext` (a cell's area depends only on its region);
- and C1, `convex_cut`, in every case but one, resting on one new staged lemma: a line
  that misses the cell, touches it at a corner or runs along a side, and the area of every
  genuine cut, are proved; the construction of a genuine cut's two pieces (corner to
  corner, corner to side, side to side), their convexity, the clipping conditions and
  exact coverage are the statement `convex_cut_pieces`, with `sorry`.

None of them cites a proposition: an early version used I.21 for the straight line from a
corner through a point inside a triangle, and now cites `inside_through`, proved from the
crossbar. `small_triangle` uses `exists_off_line`, with its circles. Several helper lemmas
of the cut restate facts proved elsewhere in the prototype under the names its proof uses,
and are proved by citing them; promotion keeps one name for each. None of this decides the hard lemmas still due:
the genuine cut, tiling, content, ray parity, exact cell selection and extraction of
outlines.

### Content: compare the three routes

| Route | Construction | Principal work | Content effort |
|---|---|---|---:|
| (a) Hilbert's transversals | Draw lines from a triangle corner through subdivision vertices, then compare common refinements. | Order the transversals and account for all bands and partial shared sides. | 25–45 sailor-days; 4,000–7,000 retained lines |
| (b) Convex cuts, recommended | Give each convex cell its fan sum, prove one cut additive, then induct on its original tiles. | Convex extensionality, all cut positions and the induction on tiles. | 30–50 sailor-days; 4,500–8,000 retained lines |
| (c) Signed boundary sums | Form formal differences of magnitudes, orient triangles, subdivide edges and cancel the internal boundary. | Orientation and signed-area identities in every configuration; boundary cancellation. | 40–70 sailor-days; 6,000–10,000 retained lines |

These are the route first mate's estimates, before duplicate attempts and independent
review. Route (b) shares its cutting machinery with general division. Route (a)
remains attractive if content is commissioned separately. Route (c) is possible in
core Lean: pairs of magnitudes represent formal differences, identified when their
cross sums agree. Cancellation makes this a well-defined quotient. That arithmetic
would not settle its geometric obligations, and no such quotient is proposed here.

For route (b):

1. A strictly convex cell has candidate area `fanSum`. Prove exact fan coverage,
   rotation and reversal from the supporting sides. Derive the separation
   hypotheses of the probe, rather than asking callers to supply them.
2. Prove `convex_area_ext` before content. Its extreme points recover the corners,
   and its boundary recovers their cyclic order up to reversal and rotation.
   Finite avoidance and small triangular neighbourhoods upgrade agreement off
   finitely many lines to equality of the closed convex regions. Content cannot
   be used to justify this step, since it will depend on it.
3. Prove `convex_cut`. A line may miss the cell, touch a vertex, coincide with a
   supporting side, join two vertices, meet a vertex and another side, or cross
   two sides. For a genuine cut, insert its two boundary intersections and measure
   from one of them. The fan splits along the two boundary chains. The first step
   from an inserted side point is collinear, so it uses `area_cut_closed`, not the
   strict flip lemma. Endpoint cases use zero triangle area.
4. Prove `convex_tiles_area` by strong induction on the number of original tiles
   within the current branch. Cut the cell and all tiles by the supporting lines
   of one chosen tile Q. The branch inside all those half-planes is Q. Each other
   branch loses Q and contains at most one convex descendant of every remaining
   original tile. Counting all fragments across all branches would not decrease;
   that is not the induction. The empty case contradicts finite avoidance, and
   the singleton case is convex extensionality.
5. For two `Apart` divisions, choose one matrix of intersection cells, indexed by
   their triangles. A row tiles its triangle, and a column tiles its triangle.
   Interior disjointness comes from the two `Apart` hypotheses. Use the same
   chosen intersection in both calculations, so no second matching argument is
   hidden. `sum_exchange` equates the row and column totals.

An intersection can be a segment or a point. Internally `Cell` is an optional
convex cell: `none` has no interior and area zero. `AgreeOff` allows its closed
region to differ on finitely many lines. `Clips` and `Intersection` specify exact
interiors as well as this weaker closed comparison. The finite-avoidance argument
justifies ignoring such pieces for area. In contrast, `convex_cut` preserves the
exact union of its two retained closed pieces, and `Divides` always requires
exact closed coverage. Boundary points are never discarded from the final figure.

The area calculation uses `area_cut` from `Tacit.area_add_of_between`, triangle
rotation and exchange, degenerate and collinear zero area, and addition and
cancellation of magnitudes. The available primitive area rules also include
`area_congruent`, `on_line_of_area_eq_zero` and `between_of_area_add`.
The proposed content route does not plan to use `area_congruent` or
`between_of_area_add`; positivity can use `Triangle.area_pos`, whose zero test is
`on_line_of_area_eq_zero`. These are proposed dependencies, not a future
certificate. No missing area axiom has been identified, and none is authorised.

### Ray parity and the region

A good ray avoids every corner on its whole supporting line. Existence comes from
avoiding the finitely many lines joining its origin to the corners. The plan's
`SimpleLoop` has no extra noncollinearity field: that consequence must be obtained
from its length, distinctness and nonintersection conditions when a frame is needed.
It must not become a supplied triangulation or a new validity assumption.

For parity independence, first show that a segment in general position crosses a
triangle boundary oddly exactly when its endpoints have different membership.
Sum endpoint contributions around a closed chain, where they cancel modulo two.
A formal fan from an auxiliary point splits that chain into triangles whose
internal edges occur twice. This is parity bookkeeping for a chain, not an assumed
geometric division of the polygon. An enclosing convex cell provides a path outside
the outline joining remote ends of two rays. Avoidance discharges all exceptional
positions, including an origin on an extension of a side.

Then prove triangle interpretation, rotation, reversal and normalisation.
Removing a redundant corner is justified only when it lies between its neighbours;
a reversal is not removed as if it were a straight-through corner. Local crossing
behaviour identifies the contour sides with `RegionBoundary`, proves boundedness
and shows that equal boundaries give equal regions. The family depth counts all
loops and gives holes and islands without making any orientation privileged.

### The arrangement and general division

`convex_enclosure` gives a convex enclosure of finitely many input points containing a
noncollinear triple. It asserts neither a minimal hull nor that the enclosure's corners
come from the input.
`outline_enclosure` puts the whole region strictly inside a convex cell. The parity and
division routes use convex enclosures, through `convex_enclosure` and
`outline_enclosure`. The stronger enclosing-triangle statement `outline_bounded` is a
separate Euclidean corollary: without Postulate 5 it can fail (in the Klein model of the
hyperbolic plane a large quadrilateral has more area than any triangle, so no triangle
encloses it), so its proof must account for Postulate 5, and it is not a prerequisite of
parity, cell selection or division existence. `outline_side_lines` lists exactly the supporting
lines of the contour sides. Repeated `convex_cut` gives `convex_arrangement`: a
nonempty list of cells, exact closed coverage of the enclosure, disjoint cores and
no core crossing a side line.

`outline_cell_constant` makes the filling parity constant on each cell core.
`outline_cells_cover` selects precisely the cells with a core point inside the
figure, and states exact closed coverage by the selected sublist. This is the
hard boundary step. Near an ordinary side there is a filled side. At a corner,
including multiple contacts, incident sides divide a sufficiently small triangular
neighbourhood into sectors; parity identifies filled sectors. Every included
boundary point must lie in a selected closed cell. Conversely, no selected cell
may reach a hole's interior or the exterior. Equality merely off the side lines
would not prove this contract.

Fan-triangulate the selected cells and concatenate their lists. Prove that triangle
interiors lie in their cell cores, so disjoint cell cores give disjoint triangles.
This yields `division_exists` for the full family, and therefore for a single
loop. `region_with_holes` connects the general depth convention to the familiar
outer-region-minus-strict-hole-interiors description, without subtraction of areas.

D5 to D7 retain the route's optional diagonal statements. An extreme corner gives
a candidate ear; an obstructing corner calls for a separate visibility argument.
An interior diagonal gives two shorter simple loops, exact union and finite-diagonal
intersection. Parity cancellation alone does not prove that their interiors are
disjoint. The suggested visibility proof may cite I.30 and I.31 and therefore
belongs after them in Book I, before I.45. These statements are staged, but this
optional proof route is not needed for the arrangement route's acceptance.

For `apart_has_outline`, split all triangle sides at intersections and endpoints,
including partial shared sides. Retain elementary intervals with filled cells on
exactly one side. Filled and empty sectors alternate at each remaining boundary
vertex. Trace the finite boundary graph, splitting its closed walks into compatible
simple loops. Removing internal intervals and handling multiple corner contacts
are proof obligations. This theorem is needed to retain the old domain; content
itself does not depend on it.

### Lemma ledger and dependency order

All paths in this ledger are under `Staging/Figures/`. "Staged" means that an
explicit contract exists with `sorry` where its own proof is due. "Derivation"
means a checked interface derivation whose geometric dependencies remain pending.
A1 to A4, B0 to B6 and C1 to C4 are staged in the files named below. The reported
convex prototype has the separate approval status described above.

The `small_triangle` contract in `Avoid.lean` omits the route draft's
extra triangle-frame hypothesis. Its proof builds the frame: finite avoidance,
incidence, order and side rules, and, with no frame supplied, `exists_point` and
`exists_off_line`, which add the latter's circle and magnitude dependencies,
Postulate 3 among them. No frame hypothesis or axiom is needed. The D1 and D3 names are the plan's
`good_ray_exists` and `crossing_parity_independent`, with no duplicate regular-ray
aliases. D9 uses the plan's general `Outline`, replacing separate holed and family
interfaces. Its enclosure, side-line and cell-selection statements make explicit
the intermediate obligations the route described in prose.

| ID | Lemmas or contract | Dependencies | File and present status |
|---|---|---|---|
| A1 | `sum_perm`, `sum_flatMap`, `sum_exchange`, zero-term filtering | magnitude laws | `Sums.lean`, staged; proved on `lean/figures-staging` |
| A2 | `closed_triangle_sides` | incidence, order, sides, Pasch | `Closed.lean`, staged; proved on `lean/figures-staging`, from the probe |
| A3 | `triangle_point_avoiding`, `small_triangle` | finite choice, incidence and order; `exists_off_line` for the frame | `Avoid.lean`, staged; proved on `lean/figures-staging` |
| A4 | `area_cut_closed`, `triangle_cut_cover` | existing area cut, zero area, Pasch | `Closed.lean`, staged; proved on `lean/figures-staging` |
| B0 | `triangle_cell` | A2, singleton sum | `Cells.lean`, staged; proved on `lean/figures-staging` |
| B1 | `convex_diagonal_separates` | supporting sides and incidence | `Arrangement.lean`, staged; its substance is proved in `ConvexFacts.lean` (`ear_opposite`, `cut_convex`) |
| B2 | `convex_diagonal_split` | A2, B1 | `Arrangement.lean`, staged; the fan's induction proves its substance |
| B3 | `fan_triangle`, `fan_apart`, `fan_covers`; `convex_fan` | B0, B2 | `ConvexCover.lean`, staged; proved on `lean/figures-staging`; `Division.lean`, derivation, resting there on no stub |
| B4 | `fanSum_rotate`, `fanSum_reverse`, `fanSum_rotateLeft` | B1, probe flips and sums | `ConvexArea.lean`, staged; proved on `lean/figures-staging`; `fanSum_rotateLeft` in `Arrangement.lean`, staged |
| B5 | `fan_insert_between`, `boundary_fan_sum` | A4, B1, B4 | `Cells.lean`, staged; proved on `lean/figures-staging` |
| B6 | `convex_extreme_iff`, `convex_area_ext` | A2, A3, B2 to B4 | `Cells.lean`, staged; proved on `lean/figures-staging`, citing no content |
| C1 | `convex_cut`, `convex_cut_pieces` | A2 to A4, B1 to B5 | `Cells.lean`; `convex_cut` staged; proved on `lean/figures-staging` from `convex_cut_pieces`, staged |
| C2 | `convex_tiles_area` | A1, A3, B6, C1 | `Cells.lean`, staged |
| C3 | `convex_intersection` | C1 | `Cells.lean`, staged |
| C4 | `Apart.area_eq_of_same_region`, `triangle_division_area` | A1, B0, C2, C3 | `Content.lean`, staged |
| D1 | `good_ray_exists`, the route's regular-ray lemma | A3, a frame derived from simplicity | `Outline.lean`, staged |
| D2 | `convex_enclosure` | B1, B2 | `Arrangement.lean`, staged |
| D3 | `crossing_parity_independent` | A2, A3, D1, D2 | `Outline.lean`, staged; `loop_inside_iff` derived |
| D4 | `triangle_region`, `loop_reverse`, `loop_rotate`, `loop_normalise`, `single_region` | A2, D1, D3 | `Outline.lean`, staged |
| D4 bridges | `convex_loop_region`, `convex_supporting_side`, `outline_bounded`, `outline_boundary`, `same_boundary_region`, `outline_normalise`, `region_with_holes` | convex geometry, A3, D3, D4 and local separation | `Outline.lean`, staged |
| D5 | `simple_diagonal` | A3, D2 to D4, visibility | `Arrangement.lean`, staged, optional route |
| D6 | `simple_diagonal_partition` | A3, D3, D4, local side argument | `Arrangement.lean`, staged, optional route |
| D7 | `simple_triangulation` | D4 to D6, or D9 | `Arrangement.lean`, staged, optional direct proof |
| D8 | `convex_arrangement` | C1 | `Arrangement.lean`, staged |
| D9 | `outline_enclosure`, `outline_side_lines`, `outline_cell_constant`, `outline_cells_cover`; `division_exists` | A3, B3, D2 to D4, D8, boundedness and local separation | `Arrangement.lean` and `Division.lean`, staged |
| D10 | `apart_has_outline` | A3, B1, D8, finite boundary graph | `Division.lean`, staged |
| E1 | `Outline.area`, `divisions_equal`, `area_eq`, `area_congr`, `area_of_same_boundary`, `convex_fan_area` | C4, D9; boundary and convex bridges where used | `OutlineArea.lean`, definition and derivations |
| E2 | `Prop45.outline`, `Prop14.outline`, `Prop14.outline_side` | D9, E1, existing constructions | `BookI.lean`, `BookII.lean`, derivations |
| E2 bridge | `Prop45.fan_boundary` | existing `Fitted.fan`, D3, D4 and exact coverage | `BookI.lean`, staged |

The dependency spine, with the optional diagonal branch separate, is:

```text
A1 to A4 -> B0 to B5 -> B6 and C1 -> C2 and C3 -> C4
B1, B2 -> D2; A3 -> D1; A2, A3, D1, D2 -> D3 -> D4
C1 -> D8; B3, D2 to D4, D8, local separation -> D9
A3, B1, D8, boundary bookkeeping -> D10
C4, D9 -> E1; E1, D9, existing constructions -> E2
D4 -> D5 and D6 -> D7 (optional)
```

This is a proof dependency plan, not the import graph of the present stub files.
For example, `Outline.lean` contains D3's contract before D2 is proved; it must not
import `Arrangement.lean` and create a cycle. At proof assignment the coordinator
must split the approved modules in dependency order. The extra B1, B2 and all-corner
B4 contracts are staged in `Arrangement.lean`, beside the arrangement that uses them. Their eventual home is with the convex facts, under one
writer. If a proof needs `Prop21.through`, it must reuse it in a Book I home; it
cannot silently duplicate that proposition inside Book Zero.

### Effort, calendar and risk

The route's estimate is **60–110 sailor-days and 9,000–16,000 retained lines** for
the full development, including the optional diagonal route and extraction of
legacy outlines. Duplicate attempts, independent review and integration are
additional. The earlier plan's 31–50 days did not budget the geometric obligations
at the route's level of detail; this brief adopts the more conservative estimate.
The optional diagonal branch alone was estimated at 10–17 sailor-days and need
not delay acceptance of a complete arrangement proof.

Those figures were written before any of the route was tried, and the first day
measured them. In about three and a half hours of crew time on 19 October the
prototype of section 8 was proved: A1 to A4, B0, B3 to B6 and most of C1, about 2,400
lines of Lean, against the route's allowance of some 20 to 35 sailor-days for the same
lemmas. Single sailors proved each group in under an hour. The one lemma not finished
in a sitting, the construction of a genuine cut's pieces, is of the kind still ahead:
case analysis of a configuration rather than a chain of known steps.

So the honest estimate of what remains is in working days of a crew of eight with
its model's capacity available, not in sailor-days:

| Remaining | Lemmas | Working days |
|---|---|---:|
| The genuine cut, intersections, tiling, content | C1's pieces, C3, C2, C4; B1, B2 and `fanSum_rotateLeft` restated from proved facts | 2 to 4 |
| Loops: rays, parity, invariance, convex and triangle bridges | D1, D3, D4 and its bridges | 3 to 5 |
| Enclosure, arrangement, exact cell selection, division | D2, D8, D9, `division_exists` | 3 to 5 |
| Boundary and normal forms; holes; boundedness (with Postulate 5) | `outline_boundary`, `same_boundary_region`, `outline_normalise`, `region_with_holes`, `outline_bounded` | 2 to 3 |
| Extraction of an outline from any `Apart`; the fan's bridge beside I.45 | D10, `Prop45.fan_boundary` | 3 to 5 |
| Promotion to `Elements/` after approval, records, pages, review | section 7 | 2 to 3 |

That is about **10 to 15 working days**, some in parallel, so **two to three weeks
of calendar time** once work can run; parity (D3), exact cell selection (D9) and
extraction (D10) carry the risk, and each could double its line. The proof crew's
capacity ran out on 19 October and returns on 26 October, so no proof work can run
before then unless it is restored. The optional
diagonal route (D5 to D7) is not counted. Freeze the interfaces of the risky lemmas
and try them first, before distributing the downstream proofs.

Challenge the contracts with a square read both ways, a concave L-shaped outline,
a square with a square hole, nested islands, disconnected components, corner-to-side
contacts, redundant collinear corners and partial shared triangle sides. An extra
interior vertex or a T-junction must not invalidate content. Empty, wholly collinear,
backtracking and crossing loops must fail validity. A failed obligation is reported
with its precise geometric inference; it is not repaired by adding an axiom or
quietly weakening the statement.

## 9. Decisions requested

1. **Domain.** Approve finite compatible simple loops, including concavity, holes,
   nested islands, separate pieces and isolated contacts at corners or against
   sides. Recommended: it retains the edition's declared reading and makes
   preservation of the `Apart` domain an explicit theorem, D10.
2. **Collinear corners.** Admit redundant straight-through corners in general loops
   and prove normalisation; keep `ConvexOutline` strict. Recommended: contacts and
   side subdivisions remain expressible without weakening the convex interfaces.
3. **Region.** Approve ray parity, the family depth convention and their independence,
   boundedness and boundary bridges. Recommended: finite counts use natural numbers
   while lengths, angles and areas remain magnitudes. Neither a division nor parity
   independence is supplied as a field of the outline.
4. **Companions.** Retain the current main statements and prominently display the
   outline companions as carrying the general claim. Recommended under the current
   policy. The alternative changes frozen main statements, relocates Heath's proof
   appropriately and needs exact old-type `two_triangles` corollaries. No such
   correction or duplicate corollary is made by this draft.
5. **Interim disclosure.** Approve the restricted-scope entries in section 7 and keep
   `figure-with-dissection` until all bridges are proved and reviewed. Recommended:
   the present constructions remain useful without a claim that an outline or a
   choice-independent area has already been formalised.
6. **Prototype approval.** The coordinator approves, or not, the prototype proofs of
   section 8 at the revision named in section 10, with their dependency checks, so
   that they may stay in `Staging/` (WORKFLOW, section 2). Recommended: they are the
   route's first wave, every one free of new axioms and all but `convex_cut` free of
   `sorry`; `convex_cut` rests on the one staged lemma `convex_cut_pieces`. Until then they
   stay on their branch, and the brief with its statements lands without them. Then
   authorise the next prototypes: the genuine cut, ray parity, and exact coverage for a
   concave figure and a figure with a hole. Approving this plan alone is not evidence
   that those proofs exist.
7. **Ownership.** Approve the homes in section 7, name one writer per file and split
   outline and arrangement dependencies before proofs begin. Recommended. Reconcile
   any shared vocabulary with brief 0012 without silently replacing its `Polygon`.
   The coordinator retains all foundation and lock decisions; the integrator owns
   registration and generated output.
8. **Acceptance.** Close issue #116 only after the whole boundary domain, exact
   division, arbitrary content and construction companions pass section 10.
   Recommended. The convex prototype is an intermediate result, and D5 to D7 are
   optional if the arrangement route proves the same public division contract.

## 10. Validation and acceptance

The delivery is two branches from main at `39ae65c`. `docs/brief-0013-figures` holds this
brief, the probe's scratch files and `Staging/Figures/` with every staged fact `sorry`
and only the derivations proved; `lean/figures-staging`, stacked on it, adds the
prototype proofs of section 8. Nothing else changes: no production Lean, Heath's text,
review record, lock, check or generated file. `lake build Staging` builds every file
under `Staging/` without the root importing them.

The same commands passed on the head of each branch, the commits that carry this text:

| Command | Outcome on both branches |
|---|---|
| `lake build` | Passed, 137 jobs. |
| `lake build Audit` | Passed, 139 jobs. |
| `lake build Staging` | Passed. Declarations of `Staging/Figures/` with their own `sorry`: 56 on the brief's branch (Outline 14, Arrangement 12, Cells 8, ConvexCover 6, Sums 4, Closed 3, Avoid 2, ConvexArea 2, Content 2, Division 2, BookI 1); 34 on the prototype's (Outline 14, Arrangement 12, Cells 3, Content 2, Division 2, BookI 1). |
| `lake env lean Certificate/Facts.lean` | Passed: 99 propositions, 3 porisms, 19 companions, 87 axioms; `facts.json` unchanged. |
| `python3 scripts/heath.py` | Passed. |
| `python3 scripts/check_fidelity.py` | Passed: 99 propositions, the lock, policies and 99 review records. |
| `python3 scripts/check_style.py` | Passed the hard rules, S1 to S21. |
| `python3 scripts/check_links.py` | Passed. |
| `python3 scripts/negative_tests.py` | Passed: every planted change caught. |
| `python3 -I tests/model/run.py --fast` | Passed. |
| `#print axioms`, prototype branch, the 22 theorems of section 8 | No `sorryAx`, Postulate 5 or superposition. `convex_cut`, the 23rd, reaches `sorryAx` only through `convex_cut_pieces`. |
| `lake env lean` on the two scratch files | Passed. |

Every lake or Lean command followed `export PATH=$HOME/.elan/bin:$PATH`. The seven quoted
definitions match `heath/I/front.md`. Elaboration with staged `sorry` is interface
evidence, not geometric completion; no independent semantic approval of the prototype
proofs, scan comparison or kernel replay is claimed.

After approval and proof, acceptance requires:

- every admitted outline has a nonempty division into nondegenerate triangles,
  with exact closed coverage and pairwise disjoint interiors;
- every previously admitted `Apart` has an outline with exactly its coverage;
- arbitrary `Apart` divisions with the same closed coverage have equal sums,
  including additional vertices and partial shared sides;
- `Outline.area` is the area of every such division, and equal boundaries give
  equal regions and equal areas;
- the outline companions construct the required parallelogram in the given angle
  and the drawn square, with the side form retained;
- the existing checked fan is connected to its exact corner list and triangle list;
- all promoted dependencies are free of `sorry`, with no new axiom, forbidden
  command, weakened check or later citation;
- the unchanged integrated validation pipeline passes at the delivered revision;
- independent review covers the domain and boundary cases in section 8, and
  confirms that the interpretation matches the edition's reading of Heath;
- pages, records, book briefs, representation accounts and generated certificates
  agree on the delivered scope and route.

The proof and edition work is complete only when those obligations are met.

## Appendix: the challenge of 19 October

A first mate who wrote none of the draft read it and every staged file as an adversarial
verifier, testing each definition against a square read both ways and from each corner,
an L-shaped hexagon, a square with a square hole, an island in the hole, two triangles
touching at a corner, a corner against another's side, a redundant collinear corner and
degenerate lists (empty, one or two points, all collinear, repeated corners,
backtracking, a bow-tie). It found no material defect: no definition vacuous on the valid
domain, no false staged statement. Its findings, and what was done:

| Finding | Done |
|---|---|
| `outline_bounded` (an enclosing triangle) can fail without Postulate 5 | Section 8 separates it from the convex enclosures the route uses |
| A3's dependencies omitted the frame of `small_triangle` | Stated in section 8's ledger; the proof builds the frame from `exists_off_line` |
| The interim restricted scope would leave full-coverage prose standing | Section 7 adds the notes, book briefs and pages to that correction |
| `simple_triangulation` does not promise original corners | `Arrangement.lean`'s description says so |
| Raw words (`ConvexRegion`, `fan`, `ReducedLoop`, `RayCrosses`, `ClosedSide`, `Half`) needed their guards in their docstrings | Docstrings amended |
| `convex_enclosure` is not a hull | Section 8 says so |
| `area_eq` needed no global division existence | Its proof now takes the given division as the witness |

Warm thanks to Astra, whose Codex readers wrote, proved and challenged this work.

