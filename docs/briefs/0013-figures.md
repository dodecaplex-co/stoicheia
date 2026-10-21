# Brief 0013: rectilineal figures given by their outlines

*19 October 2026, revised 21 October 2026. A draft for the owner's approval. The owner approved decisions 1 to 5 of section 9 on 20 October 2026 (the decisions page's entry of that day records the approval of this brief's decisions and quotes the fifth), and every staged statement is now proved in `Staging/Figures/`; promoting them into `Elements/` awaits the owner's approval. Nothing is frozen, and nothing in `Elements/`, the foundations, the lock or the review records changes with this draft.*

This brief proposes the missing ground beneath I.45 and II.14: a figure described by its boundary, a proved division into triangles covering exactly its region, and a proof that every such division gives the same area. The constructions then apply to that area.

The proposal follows [WORKFLOW, section 2](../WORKFLOW.md), and [FORMALIZATION, sections 2, 3, 6 and 7](../FORMALIZATION.md). The accompanying statements are staged in `Staging/Figures/`, and all of them are now proved there. On 20 October 2026 the coordinator assigned their proofs, in place, as an approved prototype (decision 6; WORKFLOW, section 2), and on 21 October every one was proved, with no new axiom and no statement changed. The derivations written first, which tested the interfaces, now rest on proved statements. Some proofs take another route than section 8 proposed; each departure is described in its Lean file and recorded in section 8, "The routes taken". What remains is the owner's approval to promote the statements and proofs into `Elements/` (section 7), and the edition work that follows it (section 10, "Progress, 21 October 2026").

Base of the draft of 19 October: main at `39ae65c`; this revision merges main at `756bdbae`.
Two agents drafted the statements and the proof route, one each;
the coordinator's rulings merged their drafts, and a reader who wrote none of them
challenged the result once (appendix). The probe of 19 October and the proofs of section 8
are evidence for the route, not approval of it. The table of section 10 belongs to the
revision of 19 October; its progress subsection gives the evidence of 21 October.

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

The existing checked fan has a further bridge, `BookI.Staging.Prop45.fan_boundary`. It connects its exact stated corner list to the region covered by its exact triangle list. Since that bridge uses `Fitted.fan`, whose proof cites I.13, its home is beside I.45, not in Book Zero.

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

Those dependencies are now proved in `Staging/` (section 10); the edition presents the selected area as established only once they are promoted. No subtraction of hole areas is needed. The triangles covering the filled region supply an ordinary sum of existing triangle magnitudes.

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

The drafter of the statements reports no other direct mathematical consumer of either main
theorem outside these proposition files. The companions registry imports both.
The coordinator must repeat the consumer search at promotion.

The book briefs, FORMALIZATION's representation table, brief 0006's status account, the two gap catalogues, and generated certificate and programme summaries also need reconciliation. Historical reports should remain historical, with a pointer to the completed repair where appropriate.

## 6. What may be proved before approval

Before approval, WORKFLOW, section 2, permits interface derivations and explicitly approved prototypes.

The accompanying text first contained these interface derivations:

- `loop_inside_iff` from ray independence.
- `divisions_equal`, `area_eq`, `area_congr`, `area_of_same_boundary` and `convex_fan_area` from the staged bridges.
- The outline construction companions from division existence, content and the existing constructions.
- `convex_fan` from the existing convex fan interfaces.

A derivation depending on a stub proves no completed geometric result. Each of these now
rests on proved statements alone.

The own proofs no longer wait. On 19 October the first lemmas of the route were proved as a
prototype, on the branch `lean/figures-staging`, stacked on this brief (section 8). On 20
October 2026 the coordinator assigned the proofs of every staged statement, in place in
`Staging/Figures/`, as a prototype the coordinator approved (decision 6; WORKFLOW, section
2), and on 21 October all were proved on that branch: ray existence and invariance,
boundary identification, normalisation, arrangement and cell selection, general division,
extraction of outlines, content, the optional diagonal route and the checked fan's
boundary bridge. WORKFLOW, section 2, lets them stay in `Staging/` as the proofs of an
approved prototype; they move into `Elements/` only when the owner approves their
promotion (section 7).

No proof task includes permission to add an axiom, change a frozen statement or weaken a check.

## 7. Homes and owners

All figure words and facts use `Elements.Figures` now and on promotion.
Only the book companions use `Elements.BookI.Staging` or `Elements.BookII.Staging`;
they lose `Staging` on promotion. Staged copies and obsolete checks are removed
in the same change, so no declaration is duplicated.

Each proposed home below requires approval; names of future files are proposals, not
links. Three groups of staged facts cite a proposition of the *Elements*, and each goes to a
Book I or Book II home: `outline_bounded` cites I.23, in `OutlineBound.lean`, and uses
Postulate 5; `Prop45.fan_boundary` cites `Fitted.fan`, whose proof cites I.13; and the
companions apply Euclid's I.45 and II.14 constructions. No other staged fact cites a
proposition, and none uses Postulate 5 or superposition: the prototype's one use of I.21
(the straight line from a corner through a point inside a triangle meets the opposite
side) was replaced by `inside_through`, from the crossbar, so Book Zero can hold them.
The proof of the optional diagonal route, too, cites no proposition (section 8, "The
routes taken"), so it may join the arrangement in Book Zero.

| Staged file or group | Eventual home | Writer responsible on promotion |
|---|---|---|
| `Convex.lean`, `Loops.lean`; definitions in `Avoid.lean`, `Cells.lean`, `Content.lean`, `OutlineArea.lean` | `Elements/Foundations/Figures.lean` | coordinator |
| `Sums.lean` | `Elements/Figure/Sums.lean` | assigned sums contributor |
| `Closed.lean`, `Avoid.lean` theorems | approved Book Zero modules | assigned finite-geometry contributor |
| `ConvexCover.lean`, `ConvexArea.lean`, and the prototype's `ConvexFacts.lean` and `ConvexAreaHelpers.lean`; convex precursors in `Arrangement.lean` | approved Book Zero convex modules | one writer per file, named by coordinator |
| `Cells.lean`, `Content.lean` theorems, the prototype's `ExtHelpers.lean` and `CutHelpers.lean`, and the helpers `CutPieces.lean`, `CellFacts.lean` and `ContentFacts.lean` | approved Book Zero cells and content modules | cut and content contributors, with separate files |
| `Outline.lean`, except `outline_bounded`, with the helpers `LoopFacts.lean`, `Parity.lean` and `OutlineFacts.lean` | `Elements/Figure/Outlines.lean` | outline contributor |
| `outline_bounded`, with `OutlineBound.lean` | proposed, for the owner's approval: a Book I module of its own after I.29, since its proof cites I.23 and uses Postulate 5; its place in the order is set here (FORMALIZATION, section 6) | outline contributor |
| `Arrangement.lean`, with the helpers `ArrangementFacts.lean` and `CoverFacts.lean` | `Elements/Figure/Arrangements.lean` | arrangement contributor |
| optional D5 to D7 in `Arrangement.lean`, with `Diagonal.lean` | proposed: Book Zero, beside the arrangement, since their proofs cite no proposition and use no Postulate 5 | diagonal contributor |
| `Division.lean`, `OutlineArea.lean` theorems, with the helpers `DivisionFacts.lean`, and `Extract.lean`, `ExtractEdges.lean`, `ExtractLists.lean` and `ExtractRay.lean` for `apart_has_outline` | `Elements/Figure/Divisions.lean` | division contributor |
| `BookI.lean`, with `FanBoundary.lean`, whose lemmas cite no proposition and could instead join Book Zero | `Elements/BookI/Prop45.lean` | I.45 contributor |
| `BookII.lean` | `Elements/BookII/Prop14.lean` | II.14 contributor |

The new words are `SimpleLoop`, `ReducedLoop`, `GoodRay`, `RayCrosses`,
`crossingCount`, `loopBoundary`, `loopInside`, `loopRegion`, `CompatibleLoops`,
`Outline` and its fields, `Outline.boundary`, `Outline.depth`, `Outline.inside`,
`Outline.region`, `singleOutline`, `RegionBoundary` and `Outline.area`.
They join `sides`, `ClosedSide`, `Half`, `ConvexOutline`, `ConvexRegion`, `fan`,
`Covers`, `fanSum`, the cells and `Divides`, staged here too, with no competing
definitions.

The reachable vocabulary and generated auxiliaries join `Certificate/axioms.lock` through the existing lock procedure, with a decisions entry when approved statements use them. The axioms remain unchanged. Any required model and lock synchronisation follows the existing checks.

Book Zero imports no proposition. In particular, it does not call `Fitted.fan`, II.14's area-positivity helper, I.21 or I.23. The checked fan bridge stays beside I.45, and `outline_bounded` goes to its Book I home. In `Staging/`, `Outline.lean` imports `OutlineBound.lean`, and so I.23, for `outline_bounded` alone; the promoted outline module drops that import when `outline_bounded` leaves it. No other staged theorem uses `outline_bounded`.

The integrator owns `Elements/Companions.lean` and generated output. An independent reviewer owns the renewed semantic reviews. The edition contributor owns the assigned commentary and gap-account changes. The approved orders must give each file exactly one writer.

The proposed vocabulary does not replace brief 0012's convex `Polygon`. Any sharing with that draft needs an agreed interface; this work does not depend on Book IV.

### Before promotion

These points are for the change that moves the work into `Elements/`, most of them raised
by the readers of the proofs; none is a defect of a statement:

- General lemmas about lists, sums and order sit in helper namespaces (`Extract`, `Diag`,
  `Parity`, `LoopFacts`, `Arr`, `Tiling`), and want shared homes.
- Some names want settling. `CoverFacts.cell_apart` and `CoverFacts.cells_apart` keep a
  point clear of the cells whose closed regions miss it; they do not keep cells apart.
  `Arr.tangent`, `Parity.parity_of_triangle` and `Extract.loc` are to be renamed or
  confirmed. `Diag.not_both` and `Diag.corner_off` repeat names of `Pieces`, and
  `Diag.count_split` one of `CellFacts`; `OutlineFacts.count_split` is a third
  `count_split`.
- `Diag.corner_boundary` duplicates `OutlineFacts.vertex_boundary`, statement and proof;
  promotion keeps one.
- The helper definitions `CoverFacts.corners`, `CoverFacts.joins` and `Diag.OnChain` are
  definitions outside the foundations: they go to the foundations' owner, the coordinator,
  or are inlined.
- `good_ray_exists` and `Parity.third_ray` repeat one avoidance construction, which wants
  one home.
- Some hypotheses go unused. `Pieces.side_third` carries one its proof does not use, and
  `lake build Staging` warns that the proofs of `convex_diagonal_separates` and
  `outline_cells_cover`, in `Arrangement.lean`, leave hypotheses of their statements unused:
  that both chains have a corner (the binders `hu` and `hv`), and that the cells' insides
  lie apart (`ha`). The statements keep them, since changing a statement needs approval.
- Notes in `Elements/` that say a figure's boundary, or its division into triangles, is not
  stated in Lean go stale when the bridges are promoted: in `Elements/BookI/Prop45.lean`,
  the docstring of `Fitted.fan`, the note on Euclid's and Byrne's division before it and the
  docstring of `Prop45.fan`; in `Elements/BookII/Prop14.lean`, the docstring of
  `Prop14.fan`; and in `Elements/Foundations/Phrases.lean`, the coordinator's, the docstring
  of `Apart`.

The Lean notes of `Staging/Figures/` were brought up to date with the proofs, so that none
says a proof is due, awaits approval or rests on stubs.

### Records and tags

This draft and its proofs change only this brief, files under `Staging/Figures/` and the
probe's two scratch files, with the decisions page's entry for them. They make no
production review record stale and stamp none.

Moving the work into the two proposition files makes `review/I/45.toml` and `review/II/14.toml` stale. Their owners must review and stamp the integrated revision. Any additional consumer whose statement or Lean file changes is listed separately.

Until the proved work is promoted into `Elements/` and its records reviewed, retain `figure-with-dissection` as a limitation of the delivered edition: proofs in `Staging/` are not the edition's. The interim record correction, which both records now carry, is:

```toml
scope = "restricted"
short = "figures supplied with a checked division into triangles"
hypotheses = [
  "A division into non-overlapping triangles is supplied with the figure (`Apart` or `Rectilineal`); existence from an outline is not yet proved."
]
```

That correction revised the earlier full-scope decision. The owner approved it on 20 October 2026 (decision 5; [the decisions page](0002-decisions.md#20-october-2026)); the record change was made on a branch of its own, not by this draft.
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
explicit separation hypotheses, for a list of arbitrary finite length. The two
drafters report rechecking both files and finding no `sorryAx`, Postulate 5 or
superposition in their printed dependencies. Those are their checks, not new
checks performed in this delivery. The library's `quadArea_rotate_of_cross` is
already proved.

This paragraph, its list and the next are the record of 19 October; what has changed since
follows them. On 19 October the route's first lemmas were proved as a prototype, on the
branch `lean/figures-staging`, stacked on this brief, with two independent attempts at each
hard lemma and the better proof kept. On that branch each of the following is proved in
`Staging/Figures/` with no `sorry` in its dependency closure, no new axiom, and neither
Postulate 5 nor superposition among the axioms `#print axioms` reports (22 theorems); in
the brief's own statements they stay `sorry`:

- A1, `Sums.lean`: `sum_perm`, `sum_flatMap`, `sum_exchange`, `sum_filter_ne_zero`;
- A2 and A4, `Closed.lean`: `closed_triangle_sides`, `area_cut_closed`,
  `triangle_cut_cover`;
- A3, `Avoid.lean`: `triangle_point_avoiding`, `small_triangle`;
- B3 and B4, `ConvexCover.lean` and `ConvexArea.lean`, with their shared facts in
  `ConvexFacts.lean`: `ConvexOutline.rotate`, `ConvexOutline.reverse`,
  `convexRegion_rotate`, `fan_triangle`, `fan_apart`, `fan_covers` (the boundary bridge
  for every strictly convex outline), `fanSum_rotate` and `fanSum_reverse` (the fan has
  one sum from every corner, either way round); and so the derivation `convex_fan`.
  B1 and B2 are not among them: the prototype proves their substance, but
  `convex_diagonal_separates`, `convex_diagonal_split` and B4's `fanSum_rotateLeft`, in
  `Arrangement.lean`, stay `sorry` on both branches;
- B0, B5 and B6, `Cells.lean` with `ExtHelpers.lean` and `CutHelpers.lean`:
  `triangle_cell`, `fan_insert_between`, `boundary_fan_sum`, `convex_extreme_iff` and
  `convex_area_ext` (a cell's area depends only on its region);
- and C1, `convex_cut`, in every case but one, resting on one new lemma of the prototype:
  a line that misses the cell, touches it at a corner or runs along a side, and the area
  of every genuine cut, are proved; the construction of a genuine cut's two pieces (corner
  to corner, corner to side, side to side), their convexity, the clipping conditions and
  exact coverage are the statement `convex_cut_pieces`, with `sorry`. That statement
  exists only on `lean/figures-staging`: it is not staged with this brief's statements,
  and is to be approved with the prototype (decision 6).

None of them cites a proposition: an early version used I.21 for the straight line from a
corner through a point inside a triangle, and now cites `inside_through`, proved from the
crossbar. `small_triangle` uses `exists_off_line`, with its circles. Several helper lemmas
of the cut restate facts proved elsewhere in the prototype under the names its proof uses,
and are proved by citing them; promotion keeps one name for each. None of this decides the hard lemmas still due:
the genuine cut, tiling, content, ray parity, exact cell selection and extraction of
outlines.

Those were proved on 21 October, with every other staged statement, `convex_cut_pieces`
among them, on the same branch (section 10, "Progress, 21 October 2026"). The routes they
took are below, under "The routes taken"; where a route departs from this section's, the
Lean file describes it where it happens.

### Content: compare the three routes

| Route | Construction | Principal work | Content effort |
|---|---|---|---:|
| (a) Hilbert's transversals | Draw lines from a triangle corner through subdivision vertices, then compare common refinements. | Order the transversals and account for all bands and partial shared sides. | 25–45 agent-days; 4,000–7,000 retained lines |
| (b) Convex cuts, recommended | Give each convex cell its fan sum, prove one cut additive, then induct on its original tiles. | Convex extensionality, all cut positions and the induction on tiles. | 30–50 agent-days; 4,500–8,000 retained lines |
| (c) Signed boundary sums | Form formal differences of magnitudes, orient triangles, subdivide edges and cancel the internal boundary. | Orientation and signed-area identities in every configuration; boundary cancellation. | 40–70 agent-days; 6,000–10,000 retained lines |

These are the estimates of the route's drafter, made on 19 October before duplicate
attempts and independent review. Route (b) was taken, and content is proved by it (C1 to
C4). Route (b) shares its cutting machinery with general division. Route (a)
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
positions, including an origin on an extension of a side. The proof compares the two rays
through the angle between them instead, with no fan and no enclosure (D3, under "The
routes taken").

Then prove triangle interpretation, rotation, reversal and normalisation.
Removing a redundant corner is justified only when it lies between its neighbours;
a reversal is not removed as if it were a straight-through corner. Local crossing
behaviour identifies the contour sides with `RegionBoundary`, proves boundedness
and shows that equal boundaries give equal regions. The family depth counts all
loops and gives holes and islands without making any orientation privileged. As proved,
boundedness comes from an enclosing triangle, and equal regions from counting one ray's
crossings as points of the boundary (both under "The routes taken").

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
parity, cell selection or division existence. Its proof uses Postulate 5 and cites I.23,
and no other staged theorem uses it. `outline_side_lines` lists exactly the supporting
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
would not prove this contract. The proof examines no sector: it slides from a boundary
point to an ordinary point of a side, and across it (D9, under "The routes taken").

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
optional proof route is not needed for the arrangement route's acceptance. The proof
found draws no parallel, cites neither I.30 nor I.31 and uses no Postulate 5 (D5, under
"The routes taken"), so that placement after I.31 no longer applies.

For `apart_has_outline`, split all triangle sides at intersections and endpoints,
including partial shared sides. Retain elementary intervals with filled cells on
exactly one side. Filled and empty sectors alternate at each remaining boundary
vertex. Trace the finite boundary graph, splitting its closed walks into compatible
simple loops. Removing internal intervals and handling multiple corner contacts
are proof obligations. This theorem is needed to retain the old domain; content
itself does not depend on it. The proof takes another route, through classes of linked
triangles, with no sector at a corner (D10, under "The routes taken").

### The routes taken

The proofs of 21 October follow this section's route, convex cuts for content, ray parity
for the region and an arrangement of side lines for division, with the departures below.
Each is described in its Lean file, where it happens, and each changes the proof alone: no
statement changed.

- **D3, `crossing_parity_independent`** (`Parity.lean`). Two good rays from X, through Q
  and R, are compared through the angle QXR whose boundary they are, not through a fan and
  the convex enclosure D2. A side of the outline crosses the two rays together an odd number
  of times exactly when one of its ends is within the angle and the other is not; round the
  closed outline those ends pair off. Rays on one straight line each compare with a third
  good ray off it (`Parity.third_ray`, which repeats D1's avoidance construction rather
  than citing D1). No enclosure is needed, so D3 rests on A3 and the frame of three corners
  that simplicity gives (`LoopFacts.simple_frame`), not on A2, D1 or D2, and `Outline.lean`
  does not import `Arrangement.lean`: the cycle this section warns of does not arise. The
  argument is the lemma `Parity.parity_independent`, which `crossing_parity_independent`
  applies.
- **D4, `triangle_region` and `convex_loop_region`** (`LoopFacts.lean`). From a point
  inside a convex outline a good ray crosses exactly one side, and from a point outside
  none or two (`LoopFacts.convex_count_inside`, `LoopFacts.convex_count_outside`), so
  these bridges follow from the counts, without D3. No other D4 lemma or bridge cites D3's
  statement either: `loop_normalise` and five bridges (`outline_bounded`,
  `outline_boundary`, `same_boundary_region`, `outline_normalise`, `region_with_holes`) rest
  on D3's argument through its lemma `Parity.parity_independent`, and `loop_reverse`,
  `loop_rotate`, `single_region` and `convex_supporting_side` use no parity of rays.
- **`same_boundary_region`** (`Outline.lean`, `OutlineFacts.lean`). Off the boundary, the
  depth has the parity of one good ray's crossings, and each crossing is a point of the
  boundary strictly within exactly one side of one contour, however the sides are
  subdivided; so two descriptions of one boundary count the same points
  (`OutlineFacts.depth_parity_eq`). The reason: no local crossing behaviour need be
  examined, and the proof does not need `outline_boundary`.
- **D9, `outline_cells_cover`** (`CoverFacts.lean`). A boundary point has filled points
  near it: slide along a side to a point strictly within it, at no corner of any contour,
  and cross that side by a short finite straight line, which changes one contour's inside
  and no other's (`CoverFacts.boundary_filled`). The reason: no sector at a corner need be
  examined, multiple contacts included.
- **D10, `apart_has_outline`** (`Extract.lean`, `ExtractEdges.lean`, `ExtractLists.lean`,
  `ExtractRay.lean`). The triangles' sides never cross (`Extract.no_cross`), so their
  corners cut them into elementary finite straight lines. Triangles along a common
  elementary line are linked, and the boundary lines of each class of linked triangles are
  even in number at every corner (`Extract.even_degree`); so they are the sides of finitely
  many simple closed walks (`Extract.cycles`), which are the contours. Each contour has one
  inside-status on the closed triangles of a class off it (`Extract.linked_status`), which
  makes the contours compatible (`Extract.compatible_of_status`); and the region follows
  from crossing counts, internal lines counted twice (`Extract.tri_parity`). The reason: no
  sector at a corner is examined, and since the sides never cross, the triangles' own
  corners are the only cuts needed. Its dependencies are A2, A3, B3, D1, D3, D4 and the
  cover facts of D9, not B1 and D8.
- **D5, `simple_diagonal`** (`Diagonal.lean`). Take an extreme corner V, with neighbours U
  and W. If no corner lies inside the triangle VUW or strictly between U and W, UW is the
  diagonal; otherwise the triangle is cut down from V until a corner X lies on the cutting
  line with no corner inside, and VX is the diagonal (`Diag.diagonal_exists`). The reason:
  no greatest-area triangle and no parallel are needed, so the proof cites neither I.30 nor
  I.31 and uses no Postulate 5, and the placement after I.31 no longer applies.
- **D6, `simple_diagonal_partition`** (`Diagonal.lean`). Crossing parity gives the loop's
  inside as the points inside exactly one piece (`Diag.inside_xor`); since parity alone
  does not keep the pieces apart, as this section warns, a separate argument does
  (`Diag.pieces_apart`).
- **D7, `simple_triangulation`** (`Arrangement.lean`). By the arrangement route of D9, as
  the ledger allows, not by repeated diagonals.
- **`outline_bounded`** (`OutlineBound.lean`). An enclosing triangle: the corners lie
  within an angle, and a straight line through a point within the angle meets both arms
  (`OutlineFacts.angle_triangle`), by Postulate 5, used twice, with the angle copied from
  one point to another by I.23 (`OutlineFacts.copy_angle`). The reason: the statement can
  fail without Postulate 5, and our foundations relate angles at two points only through
  superposition and Postulate 4, so the angle is copied by I.23, which reaches
  superposition only through I.4 and I.8. Of the staged facts outside `BookI.lean` and
  `BookII.lean`, it alone cites a proposition, by the coordinator's leave, and its home is
  therefore in Book I (section 7).
- **E2 bridge, `Prop45.fan_boundary`** (`FanBoundary.lean`). The fan's triangles are glued
  one at a time onto the first, OAB: each meets the earlier ones only along the side it is
  glued across (`FanBoundary.fitted_meet`, read from `Fitted`), so each keeps the outline
  simple and adds exactly its own points to the region, by crossing parity
  (`FanBoundary.fan_loop`). It cites `Fitted.fan` (I.13) and nothing later than I.45.
- **B2 and D2.** `convex_diagonal_split` rests on the corner-to-corner case of C1's pieces
  (`Pieces.form_corner_corner`), and `convex_enclosure` grows a convex outline one point at
  a time (`Arr.insert_point`), not from B1 and B2.

### Lemma ledger and dependency order

All paths in this ledger are under `Staging/Figures/`. "Staged" means that an
explicit contract was staged with this brief, with `sorry` where its own proof was due.
"Derivation" means a checked interface derivation from other staged statements.
A1 to A4, B0 to B6 and C1 to C4 are staged in the files named below. Every row is now
proved on `lean/figures-staging`, under the coordinator's assignment of 20 October, and no
`sorry` is left in `Staging/Figures/`. The Dependencies column gives the route proposed;
where the proof took another, the row says so, and "The routes taken" above gives the
departure and its reason. A proof rests on a row when it uses the row's statement or the
lemma that proves it: `crossing_parity_independent` (D3) applies `Parity.parity_independent`
and `convex_enclosure` (D2) applies `Arr.enclose_list`, and some proofs use those two lemmas
directly.

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
| A1 | `sum_perm`, `sum_flatMap`, `sum_exchange`, zero-term filtering | magnitude laws | `Sums.lean`, staged; proved |
| A2 | `closed_triangle_sides` | incidence, order, sides, Pasch | `Closed.lean`, staged; proved, from the probe |
| A3 | `triangle_point_avoiding`, `small_triangle` | finite choice, incidence and order; `exists_off_line` for the frame | `Avoid.lean`, staged; proved |
| A4 | `area_cut_closed`, `triangle_cut_cover` | existing area cut, zero area, Pasch | `Closed.lean`, staged; proved |
| B0 | `triangle_cell` | A2, singleton sum | `Cells.lean`, staged; proved |
| B1 | `convex_diagonal_separates` | supporting sides and incidence | `Arrangement.lean`, staged; proved from the prototype's ears (`Pieces.convex_sublist`, `ear_opposite`) |
| B2 | `convex_diagonal_split` | A2, B1 | `Arrangement.lean`, staged; proved from B1 and C1's corner-to-corner pieces (`Pieces.form_corner_corner`), not a fan induction of its own |
| B3 | `ConvexOutline.rotate`, `ConvexOutline.reverse`, `convexRegion_rotate`, `fan_triangle`, `fan_apart`, `fan_covers`; `convex_fan` | B0, B2 | `ConvexCover.lean`, staged; proved; `Division.lean`, derivation, resting on no stub |
| B4 | `fanSum_rotate`, `fanSum_reverse`, `fanSum_rotateLeft` | B1, probe flips and sums | `ConvexArea.lean`, staged; proved; `fanSum_rotateLeft` in `Arrangement.lean`, proved from `fanSum_rotate`, one corner at a time |
| B5 | `fan_insert_between`, `boundary_fan_sum` | A4, B1, B4 | `Cells.lean`, staged; proved |
| B6 | `convex_extreme_iff`, `convex_area_ext` | A2, A3, B2 to B4 | `Cells.lean`, staged; proved, citing no content |
| C1 | `convex_cut` | A2 to A4, B1 to B5 | `Cells.lean`, staged; proved, with the genuine cut's pieces, `convex_cut_pieces`, now proved too (`CutPieces.lean`) |
| C2 | `convex_tiles_area` | A1, A3, B6, C1 | `Cells.lean`, staged; proved, by induction on the tiles present in a branch (`Tiling`, `CellFacts.lean`) |
| C3 | `convex_intersection` | C1 | `Cells.lean`, staged; proved, by clipping one cell by the half-planes of the other's sides |
| C4 | `Apart.area_eq_of_same_region`, `triangle_division_area` | A1, B0, C2, C3 | `Content.lean`, staged; proved, by one table of common parts, chosen once (`ContentFacts.lean`) |
| D1 | `good_ray_exists`, the route's regular-ray lemma | A3, a frame derived from simplicity | `Outline.lean`, staged; proved (`LoopFacts.simple_frame`) |
| D2 | `convex_enclosure` | B1, B2 | `Arrangement.lean`, staged; proved by growing a convex outline one point at a time (`Arr.insert_point`), not from B1 and B2 |
| D3 | `crossing_parity_independent` | A2, A3, D1, D2 | `Outline.lean`, staged; proved through the angle between the two rays, resting on A3 and the simple frame, not on A2, D1 or D2 (departure, `Parity.lean`); `loop_inside_iff` derived |
| D4 | `triangle_region`, `loop_reverse`, `loop_rotate`, `loop_normalise`, `single_region` | A2, D1, D3 | `Outline.lean`, staged; proved, none citing D3's statement; `triangle_region` from the convex counts, without D3 (departure, `LoopFacts.lean`); `loop_normalise` through D3's lemma `Parity.parity_independent`; the other three with no parity of rays |
| D4 bridges | `convex_loop_region`, `convex_supporting_side`, `outline_bounded`, `outline_boundary`, `same_boundary_region`, `outline_normalise`, `region_with_holes` | convex geometry, A3, D3, D4 and local separation | `Outline.lean`, staged; proved (`OutlineFacts.lean`), none citing D3's statement; `convex_loop_region` from the convex counts, without D3 (departure), and `convex_supporting_side` with no parity of rays; the other five through D3's lemma `Parity.parity_independent`; `same_boundary_region` by counting a ray's crossings as points of the boundary (departure); `outline_bounded` by an enclosing triangle, with Postulate 5 and I.23 (departure, `OutlineBound.lean`) |
| D5 | `simple_diagonal` | A3, D2 to D4, visibility | `Arrangement.lean`, staged, optional route; proved from an extreme corner and a triangle cut down from it, with no parallel, resting on A2, A3, B3, D3, D2's lemma `Arr.enclose_list` and the cover facts of D9, not on D1 or D4 (departure, `Diagonal.lean`) |
| D6 | `simple_diagonal_partition` | A3, D3, D4, local side argument | `Arrangement.lean`, staged, optional route; proved by crossing parity and a separate argument that the pieces lie apart (`Diagonal.lean`), resting on A3, D1, D3, D4 (`loop_rotate`) and the cover facts of D9 |
| D7 | `simple_triangulation` | D4 to D6, or D9 | `Arrangement.lean`, staged; proved by D9 |
| D8 | `convex_arrangement` | C1 | `Arrangement.lean`, staged; proved (`Arr.cut_cells`) |
| D9 | `outline_enclosure`, `outline_side_lines`, `outline_cell_constant`, `outline_cells_cover`; `division_exists` | A3, B3, D2 to D4, D8, boundedness and local separation | `Arrangement.lean` and `Division.lean`, staged; proved, none citing D4, with `outline_enclosure` from D2 and not `outline_bounded`; `outline_cells_cover` by sliding to an ordinary point of a side, not by sectors at a corner (departure, `CoverFacts.lean`); `division_exists` by the selected cells' fans (`DivisionFacts.lean`) |
| D10 | `apart_has_outline` | A3, B1, D8, finite boundary graph | `Division.lean`, staged; proved by elementary lines and classes of linked triangles, resting on A2, A3, B3, D1, D3, D4 and the cover facts of D9, not on B1 and D8 (departure, `Extract.lean`, `ExtractEdges.lean`, `ExtractLists.lean`, `ExtractRay.lean`) |
| E1 | `Outline.area`, `divisions_equal`, `area_eq`, `area_congr`, `area_of_same_boundary`, `convex_fan_area` | C4, D9; boundary and convex bridges where used | `OutlineArea.lean`, definition and derivations, resting on no stub |
| E2 | `Prop45.outline`, `Prop14.outline`, `Prop14.outline_side` | D9, E1, existing constructions | `BookI.lean`, `BookII.lean`, derivations, resting on no stub |
| E2 bridge | `Prop45.fan_boundary` | existing `Fitted.fan`, D3, D4 and exact coverage | `BookI.lean`, staged; proved by gluing the fan's triangles one at a time (`FanBoundary.lean`) |

The dependency spine, with the optional diagonal branch separate, is:

```text
A1 to A4 -> B0 to B5 -> B6 and C1 -> C2 and C3 -> C4
B1, B2 -> D2; A3 -> D1; A2, A3, D1, D2 -> D3 -> D4
C1 -> D8; B3, D2 to D4, D8, local separation -> D9
A3, B1, D8, boundary bookkeeping -> D10
C4, D9 -> E1; E1, D9, existing constructions -> E2
D4 -> D5 and D6 -> D7 (optional)
```

As proved, the spine is:

```text
A1 to A4 -> B0 to B5 -> B6 and C1 -> C2 and C3 -> C4
B1, C1 -> B2; convex growth -> D2
A3, simple frame -> D1; A3, simple frame -> D3
A2, A3, B3, D1, convex counts -> triangle_region, convex_loop_region (without D3)
D3, through Parity.parity_independent -> loop_normalise and five D4 bridges
C1 -> D8; B3, D2, D3, D8, sliding across a side -> D9
A2, A3, B3, D1, D3, D4, cover facts of D9 -> D10
C4, D9 -> E1; E1, D9, existing constructions -> E2
Postulate 5, I.23 -> outline_bounded (used by no other staged theorem)
A2, A3, B3, D2, D3, cover facts of D9 -> D5
A3, D1, D3, D4, cover facts of D9 -> D6; D9 -> D7
```

This is a proof dependency plan, not the import graph of the staged files.
For example, `Outline.lean` held D3's contract before D2 was proved; it must not
import `Arrangement.lean` and create a cycle, and as proved it does not. At proof assignment the coordinator
must split the approved modules in dependency order. The extra B1, B2 and all-corner
B4 contracts are staged in `Arrangement.lean`, beside the arrangement that uses them. Their eventual home is with the convex facts, under one
writer. If a proof needs `Prop21.through`, it must reuse it in a Book I home; it
cannot silently duplicate that proposition inside Book Zero.

### Effort, calendar and risk

The route's estimate is **60–110 agent-days and 9,000–16,000 retained lines** for
the full development, including the optional diagonal route and extraction of
legacy outlines. Duplicate attempts, independent review and integration are
additional. The earlier plan's 31–50 days did not budget the geometric obligations
at the route's level of detail; this brief adopts the more conservative estimate.
The optional diagonal branch alone was estimated at 10–17 agent-days and need
not delay acceptance of a complete arrangement proof.

Those figures were written before any of the route was tried, and the first day
measured them. In about three and a half hours of working time on 19 October the
prototype of section 8 was proved: A1 to A4, B0, B3 to B6 and most of C1, about 2,400
lines of Lean, against the route's allowance of some 20 to 35 agent-days for the same
lemmas. Single agents proved each group in under an hour. The one lemma not finished
in a sitting, the construction of a genuine cut's pieces, is of the kind still ahead:
case analysis of a configuration rather than a chain of known steps.

So the honest estimate of 19 October of what remained was in working days of eight
agents with their model's capacity available, not in agent-days:

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
extraction (D10) carry the risk, and each could double its line. On 19 October the
proof agents' capacity had run out until 26 October. The optional
diagonal route (D5 to D7) is not counted. Freeze the interfaces of the risky lemmas
and try them first, before distributing the downstream proofs.

The work ran sooner. The coordinator assigned the remaining proofs on 20 October, and on
21 October every row of the table but the last was done, with the optional diagonal route
besides (section 10, "Progress, 21 October 2026"). Promotion, the last row, waits for the
owner's approval.

Challenge the contracts with a square read both ways, a concave L-shaped outline,
a square with a square hole, nested islands, disconnected components, corner-to-side
contacts, redundant collinear corners and partial shared triangle sides. An extra
interior vertex or a T-junction must not invalidate content. Empty, wholly collinear,
backtracking and crossing loops must fail validity. A failed obligation is reported
with its precise geometric inference; it is not repaired by adding an axiom or
quietly weakening the statement.

## 9. Decisions requested

The owner approved decisions 1 to 5 on 20 October 2026; the entry of that day on
[the decisions page](0002-decisions.md#20-october-2026) records the approval of this
brief's decisions and quotes decision 5. Decision 6 has been exercised,
and decisions 7 and 8 are open; the status of each follows it.

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
   `sorry`; `convex_cut` rests on one lemma, `convex_cut_pieces`, with `sorry`, which exists
   only on that branch and is not among the statements staged with this brief, so its
   statement is approved, or not, with the prototype. Until then they stay on their branch,
   and the brief with its statements lands without them. Then
   authorise the next prototypes: the genuine cut, ray parity, and exact coverage for a
   concave figure and a figure with a hole. Approving this plan alone is not evidence
   that those proofs exist.
   *Status, 21 October 2026: exercised.* On 20 October the coordinator assigned the
   proofs of every staged statement, in place in `Staging/Figures/`, as a prototype the
   coordinator approved (WORKFLOW, section 2), and on 21 October all were proved, the
   genuine cut's `convex_cut_pieces` among them (section 10, "Progress, 21 October
   2026"). They stay in `Staging/` until the owner approves their promotion.
7. **Ownership.** Approve the homes in section 7, name one writer per file and split
   outline and arrangement dependencies before proofs begin. Recommended. Reconcile
   any shared vocabulary with brief 0012 without silently replacing its `Polygon`.
   The coordinator retains all foundation and lock decisions; the integrator owns
   registration and generated output.
   *Status, 21 October 2026: open, for promotion.* The proofs are written, so the homes
   are now the homes of proved work. Section 7 adds two for approval: `outline_bounded`,
   with `OutlineBound.lean`, in a Book I module of its own after I.29, for its proof cites
   I.23 and uses Postulate 5; and the optional diagonal route in Book Zero, beside the
   arrangement, since its proof cites no proposition.
8. **Acceptance.** Close issue #116 only after the whole boundary domain, exact
   division, arbitrary content and construction companions pass section 10.
   Recommended. The convex prototype is an intermediate result, and D5 to D7 are
   optional if the arrangement route proves the same public division contract.
   *Status, 21 October 2026: open.* The proofs of section 10's obligations are written
   in `Staging/`, the optional D5 to D7 included; #116 stays open until they are promoted,
   reviewed and reflected in the pages, records and certificate (section 10, "Progress,
   21 October 2026").

## 10. Validation and acceptance

The delivery of 19 October was two branches from main at `39ae65c`. `docs/brief-0013-figures` held this
brief, the probe's scratch files and `Staging/Figures/` with every staged fact `sorry`
and only the derivations proved; `lean/figures-staging`, stacked on it, added the
prototype proofs of section 8, and now holds the proofs of every staged statement. Nothing else changes: no production Lean, Heath's text,
review record, lock, check or generated file. What `scripts/check_acceptance.py` reports
does change: it assigns the staged declarations of `Staging/Figures/BookI.lean` and
`BookII.lean` to I.45 and II.14, which then fail P10, and adds E6 entries for the other
files of `Staging/Figures/`, so this delivery holds the consolidation release of Books
I–III (stage 6 of [PROGRAM](../PROGRAM.md)) until the companions, and the rest of
`Staging/Figures/`, are promoted or retired. `lake build Staging` builds every file
under `Staging/` without the root importing them.

On 19 October the same commands passed on the head of each branch, the commits that then
carried this text. The table is the record of that revision; what has changed since is in
"Progress, 21 October 2026", below.

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

### Progress, 21 October 2026

**What is proved.** Every staged statement of `Staging/Figures/` is proved on
`lean/figures-staging`: the 66 theorems staged with this brief, in `Sums.lean`,
`Closed.lean`, `Avoid.lean`, `Cells.lean`, `ConvexCover.lean`, `ConvexArea.lean`,
`Content.lean`, `Outline.lean`, `Arrangement.lean`, `Division.lean`, `OutlineArea.lean`,
`BookI.lean` and `BookII.lean`, the optional diagonal route D5 to D7 and the bridge
`Prop45.fan_boundary` beside I.45 among them, and with them the prototype's
`convex_cut_pieces`. The derivations of section 6 rest on no stub. No statement or
definition changed, no axiom was added, and `Certificate/axioms.lock` is unchanged;
outside `Staging/Figures/`, only this brief, the probe's two scratch files and the
decisions page changed. The
proofs follow section 8's route, with the departures recorded there under "The routes
taken". Their helper lemmas are in files new on 21 October, `CutPieces.lean`,
`CellFacts.lean`, `ContentFacts.lean`, `LoopFacts.lean`, `Parity.lean`,
`OutlineFacts.lean`, `OutlineBound.lean`, `ArrangementFacts.lean`, `CoverFacts.lean`,
`DivisionFacts.lean`, `Diagonal.lean`, `Extract.lean`, `ExtractEdges.lean`,
`ExtractLists.lean`, `ExtractRay.lean` and `FanBoundary.lean`, beside the prototype's
`ConvexFacts.lean`, `ConvexAreaHelpers.lean`, `ExtHelpers.lean` and `CutHelpers.lean`;
section 7 gives each a home.

**How the evidence was gathered.** Each proof of 21 October was written by one writer and
read in full by an independent reader who wrote none of it. Nine readings covered the
proofs: the genuine cut's pieces (C1); the intersection, tiling and content (C2 to C4); the
loops and their parity (D1, D3, the D4 lemmas, `convex_loop_region` and
`convex_supporting_side`); the convex precursors and the arrangement (B1, B2, D2, D8); the
cell cover and division (D9); the diagonal route (D5 to D7); the extraction (D10); the
fan's bridge; and the bound, `outline_bounded`, with the four D4 bridges proved beside it
(`outline_boundary`, `same_boundary_region`, `outline_normalise`, `region_with_holes`).
Eight of them approved the proofs with minor findings. The reading of the bound found the
proofs correct and the statements untouched, and asked for changes: two module notes were
false, and have since been corrected, and the import of I.23 bears on the homes, which
section 7 records for the owner. A tenth reading, of the change that brought the Lean notes
up to date with the proofs, approved it with minor findings, which were applied. The
readings of the bound,
the fan's bridge, the diagonal route and the extraction are named in merge commits of
`lean/figures-staging` (`5a27ae5c`, `5fcddcd5`, `0d665982`, `0637a668`); the others are
recorded with the work, outside the repository. The readers' points that bear on promotion
are listed in section 7, "Before promotion". The prototype's proofs of 19 October have the
evidence that section 8 and this section's table of 19 October record for them.

At `b2c0580a`, the final Lean of these proofs, `lake build Staging` passes, with three
warnings, the unused binders of section 7; `#print axioms` reports `sorryAx` for none of
the 66 staged theorems, nor for `convex_cut_pieces`; and `grep -rn sorry Staging/Figures/`
finds nothing. The checks of [WORKFLOW, section 8](../WORKFLOW.md) are run on that revision
before the work lands; the branch that lands adds only documents to it.

**What the axioms show.** At `b2c0580a`, Postulate 5 and superposition appear in the
axioms of exactly five staged theorems:

- `outline_bounded`, which uses Postulate 5 twice, in `OutlineFacts.angle_triangle`, and
  reaches superposition only through its one citation of the *Elements*, I.23
  (`Elements.BookI.Prop23`), which reaches I.4 and I.8;
- `Prop45.fan_boundary`, superposition alone, through `Fitted.fan`, which rests on I.13;
- the three companions, `Prop45.outline`, `Prop14.outline` and `Prop14.outline_side`,
  through Euclid's own I.45 and II.14 constructions.

Every other staged theorem, `division_exists`, `area_eq` and `apart_has_outline` among
them, shows neither, and cites no proposition of the *Elements*. No other staged theorem
uses `outline_bounded`. So on promotion it must follow I.23 (FORMALIZATION, section 6);
section 7 proposes, for the owner's approval, a Book I module of its own after I.29, where
Euclid first uses Postulate 5.

**What these checks do not show.** Lean checks the formal derivations, and the readings
judged them against the statements and the route. Neither is the independent semantic
review of the promoted records and pages, the integrated validation pipeline at the
promoted revision, a scan comparison or a kernel replay; those come with promotion.

**What remains for #116.** The owner's approval to promote. Promotion moves the statements
and proofs from `Staging/Figures/` into `Elements/`, to the homes of section 7, with a
Book I module of its own after I.29 for `outline_bounded` and its citation of I.23, and
deletes the staged copies in the same change (WORKFLOW, section 2). The outline companions
become the edition's general claim for I.45 and II.14 (section 5). The records of I.45 and II.14
return from restricted (`figure-with-dissection`) to full, through the companions, once
reviewed (section 7, "Records and tags"); and the two `ALLOWED_LIMITS` entries for them in
`scripts/check_acceptance.py` go, with the two rows of
[ACCEPTANCE's table](../ACCEPTANCE.md#the-limitations-allowed). Until then I.45 and II.14
stay restricted, and the staged copies in `BookI.lean` and `BookII.lean` hold P10 for
them, so the release gate holds: the intended `blocks-release` state under #116.

Of the acceptance list above, the first six items are proved in `Staging/`, free of
`sorry` and with no new axiom. The rest come with promotion: no later citation in the
homes chosen, the unchanged integrated pipeline at the delivered revision, the independent
review of the domain, the boundary cases and the reading of Heath, and pages, records,
book briefs, representation accounts and certificates that agree.

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
