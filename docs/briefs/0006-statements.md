# Brief 0006: the statements of stages 2–4

*17 October 2026. This brief settles every new or changed statement of
[brief 0005](0005-astra-review.md)'s stages 2–4 before any proof work, as
[WORKFLOW.md](../WORKFLOW.md), section 2, requires. Each statement below was written with
`sorry` in the `Staging` library, compiled, read back in plain words, and challenged by
three readers who did not write it. Every finding that held has been applied; the
appendix lists them all. The brief is for the coordinator's approval. Once approved it is
frozen: others write against these statements, and a later change is a revision of this
brief (WORKFLOW, section 2, "Correcting a frozen brief"), never a quiet edit. The code
states what we formalized; where the code, this brief, a review record and a page
disagree, the disagreement is recorded and reconciled ([FORMALIZATION.md](../FORMALIZATION.md),
section 1).*

*Revised the same day, before approval: the owner revised decision 1, and I.45 and II.14
are now stated as Euclid and Byrne state them. `Rectilineal`, `Fitted` and the words and
facts only they used are withdrawn, and so are the companions `Prop45.sum` and
`Prop14.sum`; the appendix marks the findings the revision overtook. The revision was
challenged in turn: the wording of I.45 and II.14 is corrected, no statement changes, and
the scope recommended for their records is now `restricted` (open question 1).*

*Revised 18 October 2026, before approval: the companion `Prop24.circumference` is renamed
`Prop24.equalMeasure`, beside `Prop24.equalCircles`, because its short name shadowed the
definition `circumference` inside the namespace `Prop24`. The gap entries planned for I.45
and II.14 now name Gérard, F. Schur and O. Stolz as Hilbert's own note names them. No
statement changes.*

*Revised 18 October 2026, after Astra's answer to the questions on I.45 and II.14
([issue #51](https://github.com/jackChallis/stoicheia/issues/51); the question is
[issue #13](https://github.com/jackChallis/stoicheia/issues/13)). Astra would not sign off
"full" for the statements as they stood, for two independent reasons. First, the staged
hypotheses admitted triangles from A₀ that are not a division of the figure: the simple
pentagon with successive corners (0,0), (4,0), (4,4), (2,1), (0,4), in Astra's
coordinates, has area 10, and its three triangles from the first corner, each with its
corners off one straight line, are 8, 2 and 4, which make 14 (checked independently with
exact arithmetic). Second, some figures have no corner from which the straight lines to
the others divide them. Astra wrote: "Accepting a **supplied genuine dissection** is
defensible; the earlier roadmap proposed exactly that convention. It can avoid requiring
the construction theorem itself to find a triangulation. But the pieces must be connected
geometrically to the figure, and requiring a single-vertex fan narrows which figures are
covered." That answer endorsed the approach of a supplied dissection, subject to its
geometric obligations; it did not approve any new statement as full. The owner then called
for full on #13 (decision 1, as revised). So the statements of I.45 and II.14 change, and
no other proposition's does: Euclid's and Byrne's division from one corner stays the main
companion, now checked by the two conditions the limit under Conventions already named
(`Prop45.fan`, `Prop14.fan`); the gluing design withdrawn the day before is restored beside
it, for a figure with one boundary given with triangles fitted together in a suitable order
(`Rectilineal`, `Fitted`, `Prop45.figure`, `Prop14.general`, `Prop14.square`), with a new
word, `triples`, and the bridge `Fitted.fan`, which says that a checked fan is a fitted
figure, so the two companions agree; and the construction for any list of triangles is
restored (`Prop45.sum`, and `Prop14.sum` in a new form), from which today's I.45 and II.14
follow. The coverage proposed was full, by the companions together, under the tag
`figure-with-dissection`; open question 1 is answered, and a new open question 2 asks about
figures with a hole. The tag `figure-by-corners` and the recommendation `restricted` are
withdrawn, and the rows of the appendix that they overtook are marked.*

*Revised again 18 October 2026, after two readers challenged that revision: both would
accept `full` once open question 2 was closed. A square with a smaller square cut from its
middle is a given rectilineal figure in Euclid's words (Definition I.14: "contained by any
boundary or boundaries"), and gluing cannot make it. So I.45 and II.14 each gain a companion
for a figure given with triangles that lie apart, no point inside two of them (`Apart`,
`Apart.area`, `Prop45.apart`, `Prop14.apart`); `Prop45.figure` and `Prop14.general` are now
proved from them by `Fitted.inside_pairwise`, and `Prop14.square` takes the new form, so
that the square is drawn for a figure with a hole too. Open question 2 is closed by the
companions, and the tag's sentence "A figure with a hole is not taken" goes. The wording
changes too: the main theorems' two triangles stay unchecked, and the records keep a
representation note saying so; the brief and the fan docstrings say that the construction
does not use the fan's two conditions (overtaken by the next revision, in which the fan
companions conclude that the fan fits, which needs them), and that the polygon the fan's
triangles make is a reading, not a Lean statement.*

*Revised and frozen 18 October 2026. Astra's second answer (on
[issue #13](https://github.com/jackChallis/stoicheia/issues/13), read-only, at `b48640c`) is
the challenge of the final statements, those of `b48640c` onward. It accepts `full` for
I.45 and II.14 "under the explicitly stated convention that the figure comes with a checked
finite dissection", names `Prop45.apart` and `Prop14.square` as "the decisive companions",
and found "no geometric defect requiring their statements to change"; the conditional
approval of `full` is that answer's, not the first. Its wording corrections are all applied
(the appendix): `Fitted` is described as the form for a figure with one boundary, its
triangles fitted in a suitable order, and "any division" belongs to `Apart`. One statement
changes with them, at the coordinator's direction and after Astra's answer: `Prop45.fan`
and `Prop14.fan` now conclude, besides the parallelogram (the square), that the fan's
triangles are a fitted figure, proved through `Fitted.fan`, so that the fan's two
conditions do logical work. That change only adds a conclusion, and Lean checks it from
`Fitted.fan`; Astra did not read it. The coordinator approved the statements and froze this
brief on 18 October 2026, with the owner's decisions: `full` for I.45 and II.14 (decision 1,
as revised), and the definitions this brief names approved for the foundations as a class
(decision 4). The rule on proofs in `Staging/` is amended in
[WORKFLOW.md](../WORKFLOW.md), section 2, "What proofs `Staging/` may hold", so that the
derivations this brief lists as proved here stand under it.*

Base: the branch was written on main at `1e5b99a`, and has main merged in; the revision of
18 October was written on main at `f17b427`, and the corrections after Astra's second answer
on `b48640c`. The statements are in `Staging/`, as committed with this brief.
`lake build Staging` passes: 100 declarations, of which 37 carry `sorry` and the rest are definitions,
checks or proofs. Nothing in `Elements/` changes, so main's records, lock and CI are
untouched.

## The owner's decisions

Jack Challis decided three things on 17 October 2026, revised the first on 18 October, and
decided a fourth on 18 October; this brief is written to them:

1. **I.45 and II.14 are stated as Euclid and Byrne state them.** The figure is given by
   its corners and divided into triangles by the straight lines from one corner: Euclid's
   DB, from D, makes the two triangles ABD and DBC, and Byrne's two straight lines from one
   corner, in his I.45, make three. The parallelogram, and in II.14 the square, is equal to
   those triangles taken together, and is built one triangle at a time: I.42 for the first,
   I.44 for each of the rest. Nothing is claimed of another division of the figure: that it gives the
   same sum is a step Euclid takes for granted, and it goes in the gap catalogue, with the
   credit to David Hilbert, who proved it. This replaces the decision taken earlier that
   day, a figure of triangles glued edge to edge in any dissection (`Fitted`), which is
   withdrawn.

   **Revised 18 October 2026, after Astra's answer: I.45 and II.14 go full.** The owner's
   words, on [issue #13](https://github.com/jackChallis/stoicheia/issues/13): "I.45 and
   II.14 go `full` by two companions each. Euclid's and Byrne's fan stays the main one, with
   the conditions that make its triangles divide the figure (neighbouring triangles on
   opposite sides of the straight line they share, and the angles at the first corner
   together less than four right angles). A second companion takes any supplied division
   into triangles, tied geometrically to the figure. Independence from another division is
   not claimed; the gap catalogue keeps that step, crediting Hilbert." So the owner asked
   for the checked fan and for any supplied division. To meet that, this brief stages three
   forms, each checked geometrically as FORMALIZATION, section 4, asks of a dissection
   supplied as input: `apart`, for any division, as triangles that lie apart, no point
   inside two of them (`Apart`); `figure`, for a figure with one boundary, given with
   triangles glued edge to edge in a suitable order (`Fitted`, the design withdrawn on 17
   October, restored); and `fan`, Euclid's and Byrne's division from one corner, with the
   two conditions, which concludes that its triangles are fitted (`Fitted.fan`). The
   `figure` form and the bridge `Fitted.fan` are this brief's choice, not the owner's words.
   The owner's call leaves the rest of the decision as it was: the parallelogram, and the
   square, are built one triangle at a time, and nothing is claimed of another division.
   Astra's second answer (18 October) accepts `full` for these statements.
2. **III.24 is restated** to conclude that the segments are congruent, by Euclid's route:
   one segment is applied to the other. Today's proof by the radii is kept, as the
   labelled alternative proof, `Prop24.equalCircles`.
3. **Placement has no fallback and no time limit, and no new axiom may be added.** III.24
   waits for a proved `placement`; the other work goes on in parallel. If a case of
   placement turns out to need a fact the 87 axioms lack, work on it stops and the case is
   reported to Jack. Brief 0005's "timeboxed", its fallback congruence and "if the
   fallback was used" are withdrawn.
4. **The definitions this brief names are approved for the foundations as a class**
   (18 October 2026), each recorded in its pull request: the words listed under
   Conventions, "No new axioms". Each still moves with the first approved statement that
   uses it, as the staging rule below says.

## The staging rule

- **Statements before proofs live in `Staging/`,** a library of their own
  (`[[lean_lib]] name = "Staging"` in `lakefile.toml`, with a comment like Audit's). It is
  not in `defaultTargets`; `lake build Staging` checks it, `sorry` warnings and all. Most
  of its files import only the modules of `Elements` they need, mirroring their future
  homes. Three, `Sums.lean`, `Stage2/BookI/Prop40.lean` and `Stage4/Foot.lean`, import all
  of `Elements`, and the files that import them see it too. So the order of proof, in
  which nothing cites a later proposition, is not enforced inside `Staging/`: it is checked
  when each statement moves into `Elements/`, where `check_fidelity.py` refuses a later
  citation. Nothing imports the staged files.
- **Each staged declaration has a docstring in plain words,** and a companion says which
  proposition it accompanies and its certificate name ("companion of I.40").
- **A restated main theorem** is staged as `Elements.Book<book>.Staging.PropN`, so as not to
  collide with the theorem it will replace; the `Staging` namespace is dropped when it
  moves.
- **Proofs in `Staging/`** are those that [WORKFLOW.md](../WORKFLOW.md), section 2, "What
  proofs `Staging/` may hold", allows: the derivations of one staged statement from others
  that this brief lists as proved here, and the checks of today's statements. A staged
  statement's own proof waits for this brief's approval.
- **When a statement is proved, it leaves `Staging/`.** A companion moves into its
  `PropNN.lean`, after the proposition, and its entry into the companions list,
  `Elements/Companions.lean`, which the integrator writes (AGENTS.md; WORKFLOW, section 4)
  and `Certificate/Facts.lean` reads and checks; a shared step moves to the file named
  below; a definition moves to the
  foundations, joins the lock's vocabulary with a decisions entry, and its consumers'
  records are read again. Its staged copy, and any staged check that names the old
  statement, is deleted in the same change, so that no name is declared twice and
  `lake build Staging` stays green. Every review record whose statement or Lean file
  changes is re-reviewed (WORKFLOW, section 6).
- **Folders follow brief 0005's stages:** `Staging/Stage2/` (I.40, I.45, II.1, II.14, and
  the sums they need), `Staging/Stage3/` (arcs, placement, III.23 point, III.24, III.26,
  III.28, `Arcs.lean`) and `Staging/Stage4/` (`Foot`, III.14, III.15, III.25).
- **CI builds `Staging`.** Since the `Staging` library landed (pull request #4), CI's
  `check` job runs `lake build Staging`, which builds every file under `Staging/`, and so
  does the pre-flight's check sequence (WORKFLOW, section 8), so a change on main cannot
  break a staged statement silently before it moves; `sorry` warnings do not fail it.

## Conventions

**Companions.** A generalization is a companion theorem beside the unchanged `PropN`, which
stays as Euclid's worked configuration under his sentences; the fidelity check reads only
`theorem PropN` ([FORMALIZATION.md](../FORMALIZATION.md), section 2). Each companion gets a
certificate entry, named below in quotation marks ("I.40 general"), is listed in the review
record's `companions`, and is shown on the page with its own certificate. Where today's
statement is kept as a companion (`Prop40.special`, `Prop24.equalCircles`,
`Prop25.of_circle`), a check of the form `example : type_of% @Elements.BookI.Prop40 := …`
confirms that it is today's statement, checked by Lean up to unfolding definitions. The
same kind of check derives today's I.45, II.1, II.14, III.14, III.15, III.26 and III.28 from
the new statements.

**No new axioms.** The lock's `[axioms]` table stays at 87. Its `[vocabulary]` table, which
holds every definition a proposition's, porism's or companion's statement reaches, grows by
the new words below, each with a decisions entry and `check_fidelity.py --write-lock`, with
`tests/model/lock.sha256` updated and `tests/model/MODEL.md` read again in the same change
(FORMALIZATION, section 7). The words: `Magnitude.sum` (with its auxiliary `match_`
declarations), `InOrder`, `segments`, `endOf`, `OnFiniteLine`, `OnOrInsideTriangle`,
`Corners`, `Fitted` (with its constructors), `Rectilineal`, `Rectilineal.area`, `Apart`,
`Apart.area`, `triples`, `Arc`, `Arc.Drawn`, `OnSideOrLine`, `OnArc`, `InSegment`, `Arc.Less`, `Arc.Semicircle`,
`Arc.Greater`, `Arc.SameKind`, `Arc.measure`, `Places`, `Arc.Congruent` and `Foot`, as far
as frozen statements reach them. (Until the revision of 18 October, I.45 and II.14 needed
no word of their own; the checked division needs the nine words of the rectilineal
figure.)

**Where things live.** A new word is a definition in the foundations, owned by the
coordinator (WORKFLOW, section 2, item 1). A fact proved from the foundations alone goes to
Book Zero, `Elements/Figure/`. A shared step that cites a proposition goes at or after it
(FORMALIZATION, section 6). So the sums are split: brief 0005 put `Magnitude.sum`,
`InOrder`, `segments` and `endOf` in Book Zero, but they are words that statements use, and
go to the foundations; their facts go to Book Zero. The table of homes and owners is below.

**"Equal" segments and circumferences.** No magnitude of a segment is defined, and no area
of one. Segments that Euclid calls equal are read through Common Notion 4 ("things which
coincide with one another are equal to one another"): one map carries the one onto the
other, keeping every distance between their points (`Arc.Congruent`). III.24 concludes
that. III.26 and III.28 now read "equal circumferences" as equal in measure and congruent,
which says more than Heath's words; a statement that claims more is still full. The III.24,
III.26 and III.28 records will say so.

**A deliberate limit: the figure comes with its division, and the division is checked.**
*(Revised 18 October 2026, after Astra's answer; the limit of 17 October is kept below it,
marked.)* A rectilineal figure is given with the triangles it is cut into, and "a
parallelogram (a square) equal to the given rectilineal figure", in I.45 and II.14, means
equal to those triangles taken together. That sum is what Euclid adds up when he calls ABD
and DBC "the whole rectilineal figure ABCD". The division is supplied in one of three ways,
and checked geometrically in each, as FORMALIZATION, section 4, asks of a dissection
supplied as input:

- **any figure, with any boundaries, and any division of it**, as triangles that lie apart
  (`Apart`): no point is inside two of them, which is exactly what makes their sum the area
  of the figure they make up. The figure is the triangles together; it may have a hole
  (Definition I.14: "contained by any boundary or boundaries"), touch itself at a corner, or
  be in more than one piece, which only claims more;
- **a figure with one boundary**, as triangles glued edge to edge in a suitable order
  (`Fitted`): each new triangle lies across a side of an earlier one and meets the earlier
  ones only along that side, so the triangles do not overlap (`Fitted.inside_pairwise`,
  proved), so lie apart, and together make one figure. Every such figure has a division
  that can be so ordered and named, but not every division of it can (below);
- **Euclid's and Byrne's division**, by the straight lines from one corner A₀, with the two
  conditions that make it a division: each two neighbouring triangles lie on opposite sides
  of the straight line A₀Aᵢ they share, and the angles A₁A₀A₂, A₂A₀A₃, …, Aₙ₋₁A₀Aₙ together
  are less than four right angles. Such a fan is a fitted figure (`Fitted.fan`, to prove),
  and a fitted figure's triangles lie apart, so the three ways agree. That the figure a
  checked fan makes is the one bounded by the closed line A₀A₁…AₙA₀, its corners in that
  order, is a reading of the two conditions, true in the plane; no statement says it, and
  the docstrings say so.

Astra's pentagon (the revision note above) fails the first condition at its third corner,
and so is no longer taken as a fan: its triangles from the first corner overlap. Any
division of any figure, a figure with a hole among them, is taken by triangles that lie
apart; a figure with one boundary, a figure that no corner divides among them, is also taken
by gluing, in a suitable order. What is not proved, and is stated: that every rectilineal
figure can be cut into triangles that lie apart, and every figure with one boundary into
triangles glued in this way (both can, by straight lines joining corners, but no statement
here says so); and that another division of the same figure gives the same sum, the tacit
step below, which Hilbert proved for his measure of area. `Rectilineal.area` is therefore
the area of the figure with its division, not a measure of the figure alone, and its
docstring says so, as Astra asked; `Apart.area` likewise. A figure made by gluing is bounded
by one closed line that neither crosses nor touches itself, with no hole; a figure with a
hole, or touching itself at a corner, is taken by the first way (open question 2, closed).

Today's I.45, whose ABD and DBC need only be triangles, follows from neither checked
companion, since it asks less of its triangles. It follows from the construction for any
list of triangles, `Prop45.sum`, which claims nothing of a figure; II.14 likewise from
`Prop14.sum`. So nothing is lost, and no companion presents an unchecked list of triangles
as the figure. The main theorems, `Prop45` and `Prop14`, stay as Euclid's worked
configuration, and their two triangles ABD and DBC stay unchecked: nothing asks that A and C
lie on opposite sides of DB, so the triangles may overlap, and their sum need not equal the
area of their union. They are area-sum theorems, which represent Euclid's pictured division
when the geometric condition holds. The checked form of today's statement is `Prop45.fan`
(`Prop14.fan`) for the corners D, A, B, C, the list `ps` being [C]: there the condition on
neighbours is exactly that A and C lie on opposite sides of DB, and the angles at D, each
less than two right angles, are together less than four. So the I.45 and II.14 records keep
a representation note beside the tag, as the record of I.45 has one today: "The main
theorem is an area-sum theorem: it takes ABD and DBC unchecked, and they may overlap. It
represents Euclid's pictured division when A and C lie on opposite sides of DB; that
checked case is `Prop45.fan` (`Prop14.fan`) for the corners D, A, B, C. Full coverage is
carried by `Prop45.apart` (`Prop14.apart` and `Prop14.square`), for any figure given with
any division into triangles that lie apart." The tag `two-triangles` goes from them; the
note stays.

The owner decided (open question 1, answered) that the I.45 and II.14 records are `full`, by
the companions together, in this representation, and Astra's second answer accepts it, with
`Prop45.apart` and `Prop14.square` the decisive companions. As FORMALIZATION, section 3,
requires, the limit is stated here, carried by a tag of `review/terms.toml` in the I.45 and
II.14 records, and shown on both pages. The tag replaces `two-triangles` for them, and is
added to `review/terms.toml` when their records change (a tag is added before any record
uses it). Its kind is `representation`:

```toml
[tag.figure-with-dissection]
kind = "representation"
meaning = "A rectilineal figure is given with its division into triangles, checked: any division, as triangles that lie apart, no point inside two of them, so that the figure may have a hole; or, for a figure with one boundary, triangles glued edge to edge in a suitable order, each across a side of an earlier one and meeting the earlier ones only along it; or, as Euclid and Byrne divide it, the triangles from one corner, neighbours on opposite sides of the straight line they share and the angles at that corner together less than four right angles. Equal to the figure means equal to those triangles together. That every figure can be so divided, and that another division gives the same sum, are not proved here; Hilbert proved the second, for his measure of area (I.45, II.14)."
```

The page note goes in the field table's Representation row, and the mishnah of I.45 and
II.14 says it in a sentence. FORMALIZATION, section 3's row for a rectilineal figure changes
to match, and so do the Book I and Book II briefs.

*The limit of 17 October, withdrawn on 18 October.* Before Astra's answer the limit read:
the figure is divided as Euclid and Byrne divide it, by the straight lines from A₀, and
nothing checks the division; nothing asks the straight lines from A₀ to run within the
figure, so that from a corner where they do not, the triangles overlap or reach outside the
figure, and a figure that no corner divides is not taken. It named the two conditions that
would check the division (now hypotheses of `Prop45.fan` and `Prop14.fan`), recommended the
scope `restricted`, and planned the tag `figure-by-corners`, of kind `scope`. That tag is
not added.

## Homes and owners

Each new module has one owner during the work that fills it (AGENTS.md, rule 8). The
coordinator owns the foundations; the other owners are the tasks of the proof order below,
and each wave's orders name the agent.

| Module | What goes in it | Place in the dependency order | Owner |
|---|---|---|---|
| `Elements/Foundations/Magnitudes.lean` | `Magnitude.sum` | the foundations | coordinator |
| `Elements/Foundations/Phrases.lean` | `InOrder`, `segments`, `endOf`, `OnFiniteLine`, `OnOrInsideTriangle`, `Corners`, `triples`; then `Fitted`, `Rectilineal`, `Rectilineal.area`, `Apart`, `Apart.area` (Definitions I.14, I.19), after `InsideTriangle` and `OppositeSidesOf`, which they use | the foundations | coordinator |
| `Elements/Foundations/DefinitionsIII.lean` | the arc words of stage 3; `Foot` (Definitions III.4, III.5) | the foundations | coordinator |
| `Elements/Figure/Sums.lean` (new) | `Magnitude.sum_singleton`, `Magnitude.sum_append`, `InOrder.between_end` | Book Zero: imports no proposition | stage 2 ground task |
| `Elements/Figure/Rectilineal.lean` (new) | `Fitted.ne_nil`, `Fitted.triangle`, `Fitted.inside_pairwise`; `Fitted.fan` if its proof cites no proposition | Book Zero: imports no proposition | stage 2 ground task |
| `Elements/Figure/Chords.lean` (new) | `chord_cases`, `Arc.meets`, `Arc.congr_side`, `Arc.Congruent.congr_side` | Book Zero, after `DefinitionsIII` | stage 3 ground task |
| `Elements/BookI/HelpersTriangles.lean` (new) | `Prop20.collinear_iff`, `Prop20.collinear_congr`, `Prop20.between_iff`, `Prop20.between_congr` | after I.20; cites nothing later. Not `Helpers.lean`, which I.7 imports before I.20 exists | placement step 2 |
| `Elements/BookIII/Placement/Exists.lean` (new) | `Placement.exists_off`, `Placement.exists_on` | after Book I (cites I.3, I.20, I.22) | placement step 2 |
| `Elements/BookIII/Placement/Strict.lean` (new) | `Placement.base_choice`, `Placement.dist_strict` | after Book I (I.4, I.8, I.24) | placement step 1 |
| `Elements/BookIII/Placement/Unique.lean` (new) | `Placement.unique_off`, `Placement.unique_on` | after Book I (I.7) | placement step 3 |
| `Elements/BookIII/Placement/OnLine.lean` (new) | `Placement.dist_on_on` | after `HelpersTriangles` | placement step 3 |
| `Elements/BookIII/Placement/Mixed.lean` (new) | `Placement.dist_on_off` | after Book I (I.4, I.8) and `HelpersTriangles` | placement step 3 |
| `Elements/BookIII/Placement.lean` (new) | `placement`, `Placement.exists`, `Placement.unique`, `Placement.dist_off_off`, `Placement.dist` | after the five files above; before III.24 | placement step 4 |
| `Elements/BookIII/Squares.lean` | `Arc.eq_of_aligned` (cites I.7); in stage 4, `Foot.exists`, `Foot.unique` (cite I.12, I.17) | Book III's shared steps citing Books I and II | placement step 2; then stage 4 |
| `Elements/BookIII/Circumferences.lean` | `Circumference.add` | after III.22, as now | stage 3 ground task |
| `Elements/BookIII/Prop23.lean` | the companion `Prop23.point` ("III.23 point") | after III.23 | placement step 2 |
| `Elements/BookIII/Prop24.lean` | III.24 restated; `Prop24.equalCircles`, `Prop24.equalMeasure` | III.24 | placement step 4 |
| `Elements/BookIII/Prop26.lean`, `Prop28.lean` | III.26 and III.28 upgraded; the `.1` calls in `Prop27.lean` and `Prop30.lean` | as now | placement step 4 |
| `Elements/BookIII/Arcs.lean` (new) | `Arc.measure_eq_iff`, `Arc.congruent_iff` | after III.29, so that III.26–III.29 cannot rest on it | placement step 4 |
| `Elements/BookI/Prop40.lean`, `Prop45.lean`; `Elements/BookII/Prop01.lean`, `Prop14.lean` | the stage 2 companions; in `Prop45.lean`, before `Prop45.fan`, the bridge `Fitted.fan` if its proof cites a proposition (Book I only) | after each proposition | one task each |
| `Elements/BookIII/Prop14.lean`, `Prop15.lean`, `Prop25.lean` | the stage 4 companions; III.25 restated | after each proposition | one task each |
| `Elements/Companions.lean` | the companions list, which `Certificate/Facts.lean` reads and checks | | each stage's integrator |

## Stage 2: Books I and II

### Sums, and points in order

`Staging/Stage2/Sums.lean`. II.1 cuts a straight line "into any number of segments
whatever", and I.45 and II.14 take a figure of any number of sides. Lean says "any
number" with a list.

```lean
noncomputable def Magnitude.sum {k : Kind} : List (Magnitude k) → Magnitude k
  | [] => 0
  | a :: as => a + Magnitude.sum as

theorem Magnitude.sum_singleton {k : Kind} (a : Magnitude k) : Magnitude.sum [a] = a

theorem Magnitude.sum_append {k : Kind} (l₁ l₂ : List (Magnitude k)) :
    Magnitude.sum (l₁ ++ l₂) = Magnitude.sum l₁ + Magnitude.sum l₂

def InOrder : List Point → Prop
  | [] => True
  | [_] => True
  | [p, q] => p ≠ q
  | p :: q :: r :: rest => p ≠ q ∧ Between p q r ∧ InOrder (q :: r :: rest)

def segments : List Point → List (Point × Point)
  | p :: q :: rest => (p, q) :: segments (q :: rest)
  | _ => []

def endOf (B : Point) : List Point → Point
  | [] => B
  | p :: ps => endOf p ps

theorem InOrder.between_end {B P : Point} {ps : List Point} (h : InOrder (B :: P :: ps))
    (hps : ps ≠ []) : Between B P (endOf P ps)
```

- **In plain words.** The sum of a list of magnitudes of one kind, nothing for the empty
  list. Points in order: each differs from the next, and of any three in a row the middle
  is between the others, so `InOrder [B, D, E, C]` is II.1's BC cut at D and E. The
  segments of `[B, D, E, C]` are BD, DE, EC; `endOf B [D, E, C]` is C. Of three or more
  points in order, the second is between the first and the last. In I.45 and II.14 the
  segments of a figure's corners A₁, …, Aₙ, which need not be in order on a straight line,
  are its sides away from the corner A₀.
- **Homes.** The four words to the foundations; the three facts to `Elements/Figure/Sums.lean`.
- **Proof plan.** By induction on the lists, from the magnitude laws and System E's rules
  of order (Between 6, Diagram-segment 1). No proposition.

### A rectilineal figure, given with its triangles

`Staging/Stage2/Rectilineal.lean`, restored on 18 October 2026 from the design of 17
October (the file as it stood before commit `a3fbb16`), with `triples` and `Fitted.fan`
added, and then `Apart` and `Apart.area`, for a figure with any boundaries. Definition I.14:
"A figure is that which is contained by any boundary or boundaries"; Definition I.19:
"Rectilineal figures are those which are contained by straight lines". Decision 1, as
revised, and the three forms this brief stages for it, as definitions:

```lean
def OnFiniteLine (Y P Q : Point) : Prop := Y = P ∨ Y = Q ∨ Between P Y Q

def OnOrInsideTriangle (Y A B C : Point) : Prop :=
  InsideTriangle Y A B C ∨ Between A Y B ∨ Between B Y C ∨ Between C Y A ∨
    Y = A ∨ Y = B ∨ Y = C

def Corners (t : Point × Point × Point) (P Q R : Point) : Prop :=
  t = (P, Q, R) ∨ t = (Q, R, P) ∨ t = (R, P, Q) ∨ t = (Q, P, R) ∨ t = (P, R, Q) ∨
    t = (R, Q, P)

inductive Fitted : List (Point × Point × Point) → Prop
  | single {A B C : Point} (h : Triangle A B C) : Fitted [(A, B, C)]
  | glue {ps : List (Point × Point × Point)} {t : Point × Point × Point} {P Q R X : Point}
      (hps : Fitted ps) (ht : t ∈ ps) (hside : Corners t P Q R)
      (hX : OppositeSidesOf X R P Q)
      (hmeet : ∀ Y : Point, OnOrInsideTriangle Y P Q X →
        ∀ s ∈ ps, OnOrInsideTriangle Y s.1 s.2.1 s.2.2 → OnFiniteLine Y P Q) :
      Fitted (ps ++ [(P, Q, X)])

structure Rectilineal where
  pieces : List (Point × Point × Point)
  fitted : Fitted pieces

noncomputable def Rectilineal.area (R : Rectilineal) : Area :=
  Magnitude.sum (R.pieces.map fun t => △ t.1 t.2.1 t.2.2)

structure Apart where
  pieces : List (Point × Point × Point)
  ne : pieces ≠ []
  triangle : ∀ t ∈ pieces, Triangle t.1 t.2.1 t.2.2
  apart : pieces.Pairwise fun s s' => ∀ Y : Point,
    InsideTriangle Y s.1 s.2.1 s.2.2 → ¬ InsideTriangle Y s'.1 s'.2.1 s'.2.2

noncomputable def Apart.area (R : Apart) : Area :=
  Magnitude.sum (R.pieces.map fun t => △ t.1 t.2.1 t.2.2)

def triples : List Point → List (Point × Point × Point)
  | p :: q :: r :: rest => (p, q, r) :: triples (q :: r :: rest)
  | _ => []

theorem Fitted.ne_nil {ps : List (Point × Point × Point)} (h : Fitted ps) : ps ≠ []

theorem Fitted.triangle {ps : List (Point × Point × Point)} (h : Fitted ps) :
    ∀ t ∈ ps, Triangle t.1 t.2.1 t.2.2

theorem Fitted.inside_pairwise {ps : List (Point × Point × Point)} (h : Fitted ps) :
    ps.Pairwise (fun s s' => ∀ Y : Point,
      InsideTriangle Y s.1 s.2.1 s.2.2 → ¬ InsideTriangle Y s'.1 s'.2.1 s'.2.2)

theorem Fitted.fan {A₀ A₁ A₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2)
    (hopp : ∀ t ∈ triples (A₁ :: A₂ :: ps), OppositeSidesOf t.1 t.2.2 A₀ t.2.1)
    (hA₀ : Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => ∠ s.1 A₀ s.2) <
      ∟ + ∟ + (∟ + ∟)) :
    Fitted ((segments (A₁ :: A₂ :: ps)).map fun s => (A₀, s.1, s.2))
```

- **In plain words.** One triangle is a figure. A figure with a new triangle PQX laid
  against the side PQ of one of its triangles, X on the other side of PQ from that
  triangle's third corner R, is a figure, provided every point within or on the new
  triangle that is within or on an earlier one lies on the finite straight line PQ. A
  rectilineal figure is such a list, and the figure is its triangles together; its area,
  as given, is the sum of its triangles. Every figure has a triangle, each piece is a
  triangle, and no point is inside two pieces. **A figure with any boundaries** is given
  with triangles that lie apart: at least one, each a triangle, and no point inside two of
  them; the figure is the triangles together, and its area, as given, is their sum
  (`Apart`, `Apart.area`). The triples of a list of corners are each
  corner with the next two. **A figure divided from one corner**, with corners A₀, A₁, …,
  Aₙ, the list `ps` being A₃, …, Aₙ, and its triangles A₀A₁A₂, …, A₀Aₙ₋₁Aₙ, one on each side
  `segments (A₁ :: A₂ :: ps)`, is a figure in this sense when each piece is a triangle,
  each two neighbouring triangles A₀Aᵢ₋₁Aᵢ and A₀AᵢAᵢ₊₁ lie on opposite sides of the
  straight line A₀Aᵢ they share, and the angles at A₀ together are less than four right
  angles (`Fitted.fan`). That figure is read as the one with corners A₀, A₁, …, Aₙ in order
  round it; that its boundary is the closed line A₀A₁…AₙA₀ is true under the two
  conditions, but no statement says it, and `Fitted.fan` proves only that the triangles fit
  together into one figure. The docstrings of `Fitted.fan`, `Prop45.fan` and `Prop14.fan`
  say so, as `Fitted`'s does of what the rule accepts and rejects.
- **Why `Apart` beside `Fitted`** (18 October, after the challenge to the revision). A
  square with a smaller square cut from its middle is contained by two boundaries, and so is
  a given rectilineal figure in Euclid's words; no list of its triangles is fitted, since
  the last triangle of the ring meets the earlier ones along two sides. Lying apart takes
  it, needs no new predicate (`InsideTriangle` is in the foundations), and is exactly the
  condition that makes the sum of the triangles the area of the figure they make up. It
  also takes a figure touching itself at a corner, a triangle laid against part of a side of
  another, and a figure in more than one piece, which only claims more. `Fitted` stays, as
  the figure with one boundary, the triangles fitted together in a suitable order, because
  it names what Euclid's and Byrne's figures are, and a checked fan is connected to it
  (`Fitted.fan`). `Apart` is the interface for a supplied division in general; `Fitted` is
  narrower, and no statement's coverage rests on it alone.
- **What the gluing rule accepts and rejects** (checked by a challenger, by hand, on 17
  October, and by Astra's second answer on 18 October; the argument is now in `Fitted`'s
  docstring). Any cutting of a figure bounded by one closed line that neither crosses nor
  touches itself into triangles, by straight lines joining its corners, listed so that each
  after the first shares a side with one before it, with each later triangle named so that
  its attached side is its first two corners, satisfies the rule: a later triangle can meet
  an earlier one that is not its neighbour only at an end of its glued side. The naming
  matters, since the rule appends the new triangle as (P, Q, X) with PQ the attached side:
  the square ABCD cut along AC and listed ABC, ADC is a division, but is not fitted, and
  listed ABC, ACD it is. So every such figure has a fitted division, but not every division
  of it is fitted. Every figure the rule makes is bounded by such
  a line, with no hole and no pinch. Rejected: a ring of triangles closing round a point or
  a hole (the last would meet the others along two sides), and a triangle laid against part
  of a side, or against two sides in line. A figure cut in a ring round a point, or in the
  second way, can be cut again so that the rule accepts it; a figure with a hole cannot, and
  is taken by `Apart` (open question 2, closed). Neither direction is stated
  in Lean; `Fitted.inside_pairwise` is, and pins the no-overlap meaning of the rule against
  a later edit of `hmeet`.
- **What the two conditions on a fan do.** Opposite sides at each shared straight line make
  the triangles turn one way round A₀, each laid across the straight line its neighbour
  ends on; the angles at A₀ together less than four right angles stop them coming round on
  themselves. Together they make the triangles from A₀ a division of the figure A₀A₁…Aₙ,
  and they are the two conditions this brief named on 17 October as what checking the
  division would take. Astra's pentagon fails the first: its second and fourth corners lie
  on one side of the straight line from the first corner to the third. Euclid's ABCD,
  divided from D, satisfies both: A and C are on opposite sides of DB, and the two angles
  at D, each less than two right angles, are together less than four. Byrne's figure (Oliver
  Byrne, *The First Six Books of the Elements of Euclid*, London, 1847, p. 46;
  `byrne1847first` in [references.bib](../references.bib)) is not convex, and satisfies
  both from its one re-entrant corner, from which both his straight lines start; there the
  angles at A₀ together are more than two right angles and less than four. From his top
  corner, the straight line to the far left corner runs outside the figure, and the first
  condition fails.
- **What the sum is, and is not.** It is what Euclid adds up when he calls ABD and DBC "the
  whole rectilineal figure ABCD", and what Byrne adds up with three triangles. It is the
  area of the figure with its division (`Rectilineal.area`); no statement says that another
  division gives the same sum (the limit, under Conventions; the tacit step, below), and
  Hilbert proved, for his measure of area, that it does.
- **The limit**, as stated under Conventions: the figure comes with its division, checked.
- **Proved here:** `Fitted.ne_nil`, `Fitted.triangle` and `Fitted.inside_pairwise` (the
  last from the challenger's scratch proof of 17 October, with thanks), restored as they
  were. **To prove:** `Fitted.fan`. Its route: by induction along the corners, each new
  triangle glued to the one before it along A₀Aᵢ, with R = Aᵢ₋₁ and X = Aᵢ₊₁ on opposite
  sides of A₀Aᵢ by the condition on neighbours. For `hmeet`, the invariant is the region
  the earlier triangles fill: the cumulative sector at A₀ swept from the ray A₀A₁ to the ray
  A₀Aᵢ in the one orientation the condition on neighbours fixes, not the angle A₁A₀Aᵢ,
  since an angle as the library measures it is less than two right angles and the sector
  may be greater. A point within or on the earlier triangles lies within or on that sector,
  and a point within or on the new triangle within or on the angle AᵢA₀Aᵢ₊₁ beyond A₀Aᵢ;
  since the angles at A₀ together are less than four right angles, the two meet only on
  the ray from A₀ through Aᵢ, and the new triangle meets it only along the finite straight
  line A₀Aᵢ. The step has three cases by the running sum of the angles: less than two right
  angles, where the sector is an angle; exactly two, where A₁, A₀ and Aᵢ are on one
  straight line and the sector is a half-plane bounded by it; and more than two, where the
  sector is that half-plane together with the angle between A₁A₀ produced through A₀ and
  A₀Aᵢ (I.13). No new axiom is expected (Astra saw no need of one); if a step needs a
  fact the 87 axioms lack, work on it stops and the case is reported to Jack, as decision 3
  has it for placement.
- **Euclid's figure.** `Fitted.two` of 17 October, Euclid's ABCD as the list ABD, DBC, is not
  restored: `Fitted.fan` for the corners D, A, B, C says it, with the triangle ABD named
  DAB from D.
- **Homes.** The words, `Apart` and `Apart.area` among them, to the foundations;
  `Fitted.ne_nil`, `Fitted.triangle`,
  `Fitted.inside_pairwise` to `Elements/Figure/Rectilineal.lean`; `Fitted.fan` there too if
  its proof cites no proposition, and otherwise in `Elements/BookI/Prop45.lean`, before
  `Prop45.fan`.

*The figure given by its corners, 17 October, as it stood until the revision.* A figure was
given by its corners A₀, A₁, …, Aₙ and divided by the straight lines from A₀, and a
statement asked only that each piece be a triangle, `(htri : ∀ s ∈ segments (A₁ :: A₂ ::
ps), Triangle A₀ s.1 s.2)`, with no new word; nothing asked the straight lines from A₀ to
run within the figure. That hypothesis is kept, as the first of the fan's three, and the
form of the figure by its corners is kept in `Prop45.fan` and `Prop14.fan`. What is
withdrawn is the reading that it alone gives the figure. The words and facts withdrawn
with `Fitted` on 17 October (`OnFiniteLine`, `OnOrInsideTriangle`, `Corners`, `Fitted`,
`Rectilineal`, `Rectilineal.area`, `Fitted.ne_nil`, `Fitted.triangle`,
`Fitted.inside_pairwise`) are restored; `Fitted.two` is not (above).

### I.40, for bases anywhere on one straight line

`Staging/Stage2/BookI/Prop40.lean`. Companions "I.40 general", "I.40 join", "I.40 special".

```lean
theorem Prop40.general {A B C D E F : Point} {L : Line} (hABC : Triangle A B C)
    (hDEF : Triangle D E F) (hB : OnLine B L) (hC : OnLine C L) (hE : OnLine E L)
    (hF : OnLine F L) (hbase : ‖B C‖ = ‖E F‖) (heq : △ A B C = △ D E F)
    (hside : SameSide A D L) :
    ∃ M : Line, Parallel M L ∧ OnLine A M ∧ OnLine D M

theorem Prop40.join {A B C D E F : Point} {L : Line} (hABC : Triangle A B C)
    (hDEF : Triangle D E F) (hB : OnLine B L) (hC : OnLine C L) (hE : OnLine E L)
    (hF : OnLine F L) (hbase : ‖B C‖ = ‖E F‖) (heq : △ A B C = △ D E F)
    (hside : SameSide A D L) (hAD : A ≠ D) :
    AreParallel A D B C

theorem Prop40.special {A B C D E : Point} (hABC : Triangle A B C) (hCDE : Triangle C D E)
    (hBCE : Between B C E) (hbase : ‖B C‖ = ‖C E‖) (heq : △ A B C = △ C D E)
    (hside : SameSideOf A D B E) (hAD : A ≠ D) :
    AreParallel A D B E
```

- **In plain words.** Equal triangles ABC, DEF on equal bases BC, EF of one straight line
  L, on the same side of it, have A and D on one straight line parallel to L; when A and D
  differ, AD is parallel to BC. `Prop40.special` is today's statement, bases BC, CE end to
  end, derived from `Prop40.general` (proved; checked against `type_of% @Prop40`).
- **Coverage.** Heath: "Equal triangles which are on equal bases and on the same side are
  also in the same parallels." Full, with the companions: the bases may be apart,
  touching, overlapping or one, and named either way along L. Today's `adjacent-bases`
  restriction goes.
- **Cases.** The four placings of the bases; the bases named in opposite orders; A and D
  one point (then the parallel is the one through A).
- **Route.** Euclid's: the parallel through A [I. 31], and I.38 for the triangles on equal
  bases, now general, with the library's `Prop31.line`, `Prop30.meet` and
  `OnRay.eq_of_area_eq`; the end of his reductio direct, as today (route `modified`, as
  I.40's record says now).
- **Dependencies.** I.31, I.38, `Prop30.meet` (HelpersParallels), `Prop31.line`,
  `OnRay.eq_of_area_eq`; `AreParallel.of_parallel` for `special`.

### I.45, for any rectilineal figure

`Staging/Stage2/BookI/Prop45.lean`. Companions "I.45 append", "I.45 sum", "I.45 apart",
"I.45 figure", "I.45 fan".

```lean
theorem Prop45.append {A B C K F L M E₁ E E₂ : Point} (hKFLM : Parallelogram K F L M)
    (hang : ∠ F K M = ∠ E₁ E E₂) (hABC : Triangle A B C) (hE : Triangle E₁ E E₂) :
    ∃ K' F' L' M' : Point, Parallelogram K' F' L' M' ∧ ∠ F' K' M' = ∠ E₁ E E₂ ∧
      quadArea K' F' L' M' = quadArea K F L M + △ A B C

theorem Prop45.sum {E₁ E E₂ : Point} (ts : List (Point × Point × Point)) (hne : ts ≠ [])
    (hts : ∀ t ∈ ts, Triangle t.1 t.2.1 t.2.2) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = Magnitude.sum (ts.map fun t => △ t.1 t.2.1 t.2.2)

theorem Prop45.apart {E₁ E E₂ : Point} (R : Apart) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = R.area

theorem Prop45.figure {E₁ E E₂ : Point} (R : Rectilineal) (hE : Triangle E₁ E E₂) :
    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
      quadArea K F L M = R.area

theorem Prop45.fan {A₀ A₁ A₂ E₁ E E₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2)
    (hopp : ∀ t ∈ triples (A₁ :: A₂ :: ps), OppositeSidesOf t.1 t.2.2 A₀ t.2.1)
    (hA₀ : Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => ∠ s.1 A₀ s.2) <
      ∟ + ∟ + (∟ + ∟))
    (hE : Triangle E₁ E E₂) :
    ∃ R : Rectilineal,
      R.pieces = (segments (A₁ :: A₂ :: ps)).map (fun s => (A₀, s.1, s.2)) ∧
      ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧
        quadArea K F L M = R.area
```

- **In plain words.** Given a parallelogram in the angle E and a triangle, a parallelogram
  in the same angle equal to both together (`append`). Given any number of triangles, at
  least one, a parallelogram in the angle E equal to all of them together; they need not fit
  together, and nothing is said of a figure (`sum`). Given a rectilineal figure, with any
  boundaries, and any division of it into triangles, no point inside two of them, a
  parallelogram in the angle E equal to it, that is, to those triangles together (`apart`).
  Given a rectilineal figure with one boundary and its triangles, glued edge to edge in a
  suitable order, a parallelogram in the angle E equal to it, that is, to those triangles
  together (`figure`). Given a rectilineal figure by its corners A₀, A₁, …, Aₙ, divided by
  the straight lines from A₀, with each piece a triangle, each two neighbouring triangles on
  opposite sides of the straight line A₀Aᵢ they share, and the angles at A₀ together less
  than four right angles: the triangles A₀A₁A₂, …, A₀Aₙ₋₁Aₙ, in that order, are a fitted
  figure, and there is a parallelogram in the angle E equal to that figure, that is, to the
  triangles together (`fan`); that the triangles make the figure with those corners in order
  is a reading, not a Lean statement. Today's I.45 follows from `Prop45.sum` for the list
  ABD, DBC (checked by Lean).
- **Why `apart`, `figure` and `fan`.** `fan` names the main companion, the division Euclid
  draws in his proof and Byrne in his figure, from one corner, which not every figure
  admits. `figure` is Euclid's word for what is given, "a given rectilineal figure", and so
  it names the companion for a figure glued together, as in the design of 17 October and in
  FORMALIZATION, section 2's list of companions; `apart` names the figure whose triangles
  lie apart, the widest form, which carries the coverage. On 17 October `Prop45.figure` was,
  for a day, the unchecked division from a corner; that statement is withdrawn, and its form
  lives on in `Prop45.fan`, with the two conditions added.
- **Coverage.** Heath: "To construct, in a given rectilineal angle, a parallelogram equal
  to a given rectilineal figure." **Full, by the companions together,** as the owner decided
  on 18 October after Astra's first answer, and as Astra's second answer accepts, in the
  representation `figure-with-dissection`. `Prop45.apart` carries it: any rectilineal
  figure, with any boundaries, given with any division into triangles that lie apart.
  `Prop45.figure` takes a figure with one boundary, given with triangles glued edge to edge
  in a suitable order, and follows from `Prop45.apart`. `Prop45.fan`, the main companion,
  takes Euclid's and Byrne's division from one corner, checked, and concludes that its
  triangles are a fitted figure (`Fitted.fan`) and the parallelogram equal to it
  (`Prop45.figure`). The fan alone covers a restricted class, since some figures have no
  such fan, and does not carry `full` on its own; nor does `figure`, which takes no figure
  with a hole. The `two-triangles` restriction goes. What the
  representation leaves unproved is stated with the tag: that every figure can be so
  divided, and that another division gives the same sum (the tacit step, below). A figure
  with a hole is taken, by `Prop45.apart` (open question 2, closed). The main theorem keeps
  its unchecked two triangles, and the record a representation note saying so: an area-sum
  theorem, representing Euclid's pictured division when A and C lie on opposite sides of
  DB, the checked case being `Prop45.fan` for the corners D, A, B, C, and full coverage
  carried by `Prop45.apart` (the limit, under Conventions).
- **Cases.** A triangle (I.42 alone; for the fan, the list `ps` empty and no triple);
  Euclid's four corners, divided from D; Byrne's five, divided from his re-entrant corner,
  where the angles at A₀ together exceed two right angles; any number of corners; a figure
  convex or not; a figure that no corner divides, by `Prop45.figure`; a square with a square
  hole, cut into eight triangles, and a figure touching itself at a corner, by
  `Prop45.apart` alone. Astra's
  pentagon, divided from its first corner, is not a fan (its triangles overlap); divided
  otherwise it is a figure for `Prop45.figure`.
- **Construction.** Given: the angle (the triangle E₁EE₂) and the figure, with its division.
  Returned: the parallelogram KFLM. Shown: it is a parallelogram, its angle at K is the
  given angle, and it is equal to the figure's triangles taken together.
- **Route.** Euclid's, as Byrne draws it for three triangles: a parallelogram for the first
  triangle [I. 42], one for the next applied to its side [I. 44], and Euclid's proof that
  the two make one parallelogram (I.29, I.14, I.34, I.33); then the same for each triangle
  after. `Prop45.append` is that second step, and `Prop45.sum` takes the triangles one at a
  time, in order. **Proved here:** `Prop45.sum`, by induction on the list, from I.42 and
  the stubbed `Prop45.append` (the proof `Prop45.figure` had on 17 October, for any list);
  `Prop45.apart`, from `Prop45.sum` with the figure's own `ne` and `triangle`;
  `Prop45.figure`, from `Prop45.apart` with `Fitted.ne_nil`, `Fitted.triangle` and
  `Fitted.inside_pairwise`; `Prop45.fan`, the figure that the stubbed `Fitted.fan` gives,
  with `Prop45.figure` for it. Each is a derivation of one staged statement from others,
  as WORKFLOW, section 2, allows in `Staging/`, and rests on the stubs until they are
  proved. Euclid shows two triangles; the repetition is noted in the record.
- **The fan's two conditions do logical work.** `Prop45.fan` concludes, besides the
  parallelogram, that the fan's triangles are a fitted figure, and that conclusion needs
  the condition on neighbours and the condition on the angles at A₀: without them the
  triangles from A₀ may overlap (Astra's pentagon), and are then not fitted. The
  parallelogram alone would follow from each piece being a triangle, by `Prop45.sum`; the
  first conclusion is what the conditions are for. "I.45 fan" therefore waits for
  `Fitted.fan`, the hardest stub of stage 2. **If `Fitted.fan` stalls,** `Prop45.fan`
  cannot be proved, and stays in `Staging/`. The fitting implication is then unformalized:
  the records and pages say so, and stop presenting the checked fan as Lean-checked; the
  construction for the fan's triangles is still `Prop45.sum` for that list, which checks
  nothing of a figure. No `redundant-hypothesis` tag stands in for the missing bridge, and
  a weaker fan statement would be a revision of this brief. `full` does not depend on it,
  since `Prop45.apart` carries the coverage.
- **Restored:** `Prop45.sum`, withdrawn on 17 October when nothing used it. Today's I.45
  asks only that ABD and DBC be triangles, so it follows from neither checked companion,
  and `Prop45.sum` is what it follows from; it is also the one construction that both
  `figure` and `fan` repeat.
- **Dependencies.** I.42, I.44 and the steps of today's I.45; `Apart`, `Rectilineal`,
  `Fitted.ne_nil`, `Fitted.triangle`, `Fitted.inside_pairwise`, `Fitted.fan`; `segments`, `triples`, `Magnitude.sum`, and the magnitude
  laws `add_zero` and `add_assoc`.

### II.1, for any number of segments

`Staging/Stage2/BookII/Prop01.lean`. Companions "II.1 two", "II.1 general".

```lean
theorem Prop1.two {A₁ A₂ B C D : Point} (h : Between B D C) :
    rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D C

theorem Prop1.general {A₁ A₂ B : Point} {ps : List Point} (h : InOrder (B :: ps)) :
    rect A₁ A₂ B (endOf B ps) =
      Magnitude.sum ((segments (B :: ps)).map fun s => rect A₁ A₂ s.1 s.2)
```

- **In plain words.** If BC is cut at D, the rectangle of A₁A₂ and BC is the rectangles of
  A₁A₂ with BD and with DC. If the straight line from B is cut at any number of points in
  order, the list `ps` being the points of section and then the end, the rectangle of A₁A₂
  and the whole is the sum of the rectangles of A₁A₂ and each segment. Today's II.1 follows
  for `[D, E, C]` (checked by Lean).
- **Coverage.** Heath: "If there be two straight lines, and one of them be cut into any
  number of segments whatever, …". Full, with the companions. The `three-pieces`
  restriction goes.
- **Cases.** No point of section (one segment, the whole); one (`Prop1.two`); Euclid's two;
  any number. With no points at all the straight line is nothing, and so is each side; the
  uncut A₁A₂ may be nothing too.
- **Route.** `Prop1.two` is II.1's construction with one parallel [I. 11, I. 3, I. 31,
  I. 34]. `Prop1.general` repeats it by induction, cutting off one segment at a time
  (`InOrder.between_end`); Euclid draws every parallel in one figure, and the induction is
  noted in the record.
- **Dependencies.** I.3, I.11, I.31, I.34; `Rectangle.contained`; the sums.

### II.14, for any rectilineal figure, with a drawn square

`Staging/Stage2/BookII/Prop14.lean`. Companions "II.14 rectangle", "II.14 sum",
"II.14 apart", "II.14 general", "II.14 square", "II.14 fan".

```lean
theorem Prop14.rectangle {E B C D : Point} (h : Rectangle E B C D) :
    ∃ P Q : Point, sq P Q = quadArea E B C D

theorem Prop14.sum (ts : List (Point × Point × Point)) (hne : ts ≠ [])
    (hts : ∀ t ∈ ts, Triangle t.1 t.2.1 t.2.2) :
    ∃ P Q : Point, sq P Q = Magnitude.sum (ts.map fun t => △ t.1 t.2.1 t.2.2)

theorem Prop14.apart (R : Apart) : ∃ P Q : Point, sq P Q = R.area

theorem Prop14.general (R : Rectilineal) : ∃ P Q : Point, sq P Q = R.area

theorem Prop14.square (R : Apart) :
    ∃ P Q S T : Point, Square P Q S T ∧ Parallelogram P Q S T ∧ quadArea P Q S T = R.area

theorem Prop14.fan {A₀ A₁ A₂ : Point} {ps : List Point}
    (htri : ∀ s ∈ segments (A₁ :: A₂ :: ps), Triangle A₀ s.1 s.2)
    (hopp : ∀ t ∈ triples (A₁ :: A₂ :: ps), OppositeSidesOf t.1 t.2.2 A₀ t.2.1)
    (hA₀ : Magnitude.sum ((segments (A₁ :: A₂ :: ps)).map fun s => ∠ s.1 A₀ s.2) <
      ∟ + ∟ + (∟ + ∟)) :
    ∃ R : Rectilineal,
      R.pieces = (segments (A₁ :: A₂ :: ps)).map (fun s => (A₀, s.1, s.2)) ∧
      ∃ P Q : Point, sq P Q = R.area
```

- **In plain words.** A square equal to a given rectangle (`rectangle`); a square equal to
  any number of triangles together, at least one, which need not fit together (`sum`); a
  square equal to a rectilineal figure, with any boundaries, given with any division into
  triangles that lie apart, that is, to those triangles together (`apart`); a square equal
  to a rectilineal figure with one boundary, given with its triangles glued edge to edge in
  a suitable order (`general`); a square drawn as four corners, equal to a figure given with
  triangles that lie apart (`square`); and, for a figure divided from one corner A₀ and
  checked as in `Prop45.fan`, that the triangles A₀A₁A₂, …, A₀Aₙ₋₁Aₙ are a fitted figure and
  a square equal to it, that is, to those triangles together (`fan`), read as the figure
  with those corners in order, as in I.45. Today's
  II.14 follows from `Prop14.sum` for I.45's two triangles A₁A₂A₄ and A₄A₂A₃, which are
  ABD and DBC (checked by Lean).
- **`Prop14.sum` restored, in a new form.** On 17 October `Prop14.sum` was today's
  two-triangle statement, kept as a companion, and was withdrawn when the division from a
  corner made it unnecessary. It now takes any list of triangles, as `Prop45.sum` does, and
  today's statement is the check derived from it. The two-triangle form is not lost: the
  check states it.
- **The route of `Prop14.rectangle` is decided:** it is proved directly by the second part
  of Euclid's proof, today's proof of II.14 after the rectangle is made. If BE is equal to
  ED, the rectangle is a square. If not, the greater, BE, is produced to F with EF equal to
  ED, BF is bisected at G, the semicircle BHF is described, DE is produced to H, and II.5
  and I.47 make the rectangle the square on EH. **It does not cite II.14.** Brief 0005's
  "applies Prop14 to the rectangle's two halves" is withdrawn: it would rest the companions
  on the two-triangle statement rather than on Euclid's construction, and make the check of
  today's II.14 prove II.14 from II.14, and no check would catch it.
- **Proved here:** `Prop14.sum` (a right angle by I.11 at the corner A of the first triangle
  ABC, on AB, then `Prop45.sum` and `Prop14.rectangle`), from the stubs; `Prop14.apart`,
  from `Prop14.sum` for the figure's triangles; `Prop14.general`, from `Prop14.apart` with
  `Fitted.inside_pairwise`; `Prop14.fan`, the figure that `Fitted.fan` gives, with
  `Prop14.general` for it. As in I.45, the fan's two conditions do logical work:
  `Prop14.fan` concludes that the fan's triangles are a fitted figure, which needs them,
  while the square alone would follow from each piece being a triangle, by `Prop14.sum`. If
  `Fitted.fan` stalls, `Prop14.fan` stays unproved in `Staging/`, the fitting implication is
  unformalized, and the records stop presenting the checked fan as Lean-checked, as under
  I.45; `full` rests on `Prop14.apart` and `Prop14.square`. **To prove:**
  `Prop14.rectangle`; `Prop14.square`, the square on the side `Prop14.apart` finds,
  described on it [I. 46] with `Square.described`. `Prop14.square` takes the widest form,
  `Apart`, so that the square is drawn for a figure with a hole too (revised 18 October; it
  took `Rectilineal` before). The square drawn for a figure glued together, or for a fan, is
  `Prop14.square` for that figure's triangles, which lie apart (`Fitted.inside_pairwise`),
  with the same sum by unfolding, and needs no statement of its own.
- **Coverage.** Heath: "To construct a square equal to a given rectilineal figure." **Full,
  by the companions together,** as the owner decided on 18 October, and as Astra's second
  answer accepts, in I.45's representation `figure-with-dissection`. `Prop14.apart` and
  `Prop14.square` carry it: any rectilineal figure, with any boundaries, given with any
  division into triangles that lie apart, the square drawn. `Prop14.general` takes a figure
  with one boundary, glued edge to edge in a suitable order; `Prop14.fan`, the main
  companion, Euclid's and Byrne's division from one corner, checked, and concludes that it
  is a fitted figure. Neither of the last two carries `full` on its own. The `two-triangles`
  restriction goes, and `Prop14.square` answers `side-not-square`, which stays for the main
  theorem. The unproved steps are I.45's, stated with the tag; a figure with a hole is
  taken, by `Prop14.apart` (open question 2, closed). The main theorem keeps its unchecked
  two triangles, and the record a representation note saying so: an area-sum theorem,
  representing Euclid's pictured division when A and C lie on opposite sides of DB, the
  checked case being `Prop14.fan` for the corners D, A, B, C, and full coverage carried by
  `Prop14.apart` and `Prop14.square`.
- **Cases.** The rectangle a square already; BE the greater; ED the greater. The figure's
  are I.45's: a triangle, Euclid's four corners, Byrne's five, any number, convex or not,
  a figure that no corner divides, by `Prop14.general`, and a figure with a hole, by
  `Prop14.apart`.
- **Dependencies.** I.11, I.45 (`Prop45.sum`), II.5, I.47, I.46, `Rectangle.of_right`,
  `Square.described`; `Apart`, `Rectilineal`, `Fitted.ne_nil`, `Fitted.triangle`,
  `Fitted.inside_pairwise`, `Fitted.fan`.

### The tacit step, for the gap catalogues

Euclid takes "the whole rectilineal figure ABCD" to be ABD and DBC together, and so takes
for granted that the whole is the same however the figure is cut into triangles: AC would
have given ABC and ACD. For a four-sided figure whose diameters cross, as in Euclid's
figure, Book Zero proves it (`quadArea_rotate_of_cross`). For any polygon and any division
into triangles, David Hilbert proved it, for the measure of area he builds from his axioms,
in *Grundlagen der Geometrie* (1899), chapter IV. In E. J. Townsend's translation,
[*The Foundations of Geometry*](https://www.gutenberg.org/ebooks/17384) (1902), that is
chapter IV, "The Theory of Plane Areas", section 20, "The measure of area of triangles and
polygons", where theorem 29 and the definition after it give that the measure of area of a
polygon "is independent of the manner of decomposition into triangles and, consequently, is
definitely determined by the polygon itself" (checked against the Project Gutenberg text).
Hilbert's own note to the chapter, at section 18 (from the French edition), names others
who developed such a theory: Gérard, in his thesis (1892) and *Géométrie plane* (1898),
with parallel transversals where Hilbert's run from a vertex, and F. Schur, in the
proceedings of the Dorpat naturalists' society (1892) and his *Lehrbuch der analytischen
Geometrie* (1898). The note also refers to an article by O. Stolz in the *Monatshefte für
Mathematik und Physik* (1894). The statements here claim nothing of another cutting. As
Astra put it, independence from another division "need not be part of a construction
theorem explicitly about a figure supplied with one dissection, but it is needed before
presenting the sum as a choice-independent area of the polygon", and historical credit
cannot discharge it in Lean; so neither `Rectilineal.area` nor `Apart.area` is presented as
such an area. The
entries planned, for whoever writes stage 2's records (revised 18 October for the checked
division):

- `docs/reports/gaps-book-I.md`, I.45, the first entry becomes: "Euclid cuts the
  rectilineal figure ABCD by DB into the triangles ABD and DBC, and takes "the whole
  rectilineal figure ABCD" to be the two together. Any rectilineal area, Heath says, "can
  of course be resolved into triangles" (vol. 1, p. 347). Taken for granted is that every
  cutting gives the same whole: AC would give ABC and ACD. For a four-sided figure whose
  diameters cross, Book Zero proves it (`quadArea_rotate_of_cross`); for any figure and any
  cutting, David Hilbert proved it, for his measure of area (*The Foundations of Geometry*,
  ch. IV, "The Theory of Plane Areas", section 20), and his own note to the chapter credits
  Gérard and F. Schur (1892 and 1898) with like theories and refers to an article by
  O. Stolz (1894). Our companions take the figure with a division into triangles that is
  checked to be one: any division into triangles that lie apart, for a figure with any
  boundaries; for a figure with one boundary, triangles glued edge to edge in a suitable
  order; or Euclid's and Byrne's, by the straight lines from one corner; they make the
  parallelogram equal to those triangles, and claim nothing of another cutting."
- `docs/reports/gaps-book-II.md`, II.14, the first entry becomes: ""Let A be the given
  rectilineal figure": it may have any number of sides. Any rectilineal area, Heath says
  under I.45, "can of course be resolved into triangles" (vol. 1, p. 347). Our companions
  take the figure with a checked division into triangles, as I.45's do, and make the square
  equal to those triangles; that another cutting gives the same whole is the step
  taken for granted under I.45, which David Hilbert proved, for his measure of area; his own
  note credits Gérard and F. Schur (1892 and 1898) with like theories and refers to an
  article by O. Stolz (1894)."

## Stage 3: arcs and segments

### The words

`Staging/Stage3/Definitions.lean`, for `DefinitionsIII.lean`. None is an assumption.

```lean
structure Arc where
  circle : Circle
  B : Point
  C : Point
  K : Point

def Arc.Drawn (a : Arc) : Prop :=
  (∃ O : Point, Centre O a.circle) ∧ OnCircle a.B a.circle ∧ OnCircle a.C a.circle ∧
    ¬ Collinear a.B a.C a.K

def OnSideOrLine (P K B C : Point) : Prop :=
  SameSideOf P K B C ∨ Collinear B C P

def OnArc (P : Point) (a : Arc) : Prop :=
  OnCircle P a.circle ∧ OnSideOrLine P a.K a.B a.C

def InSegment (P : Point) (a : Arc) : Prop :=
  (InsideCircle P a.circle ∨ OnCircle P a.circle) ∧ OnSideOrLine P a.K a.B a.C

def Arc.Less (a : Arc) : Prop :=
  ∃ O : Point, Centre O a.circle ∧ OppositeSidesOf O a.K a.B a.C

def Arc.Semicircle (a : Arc) : Prop :=
  ∃ O : Point, Centre O a.circle ∧ Collinear a.B a.C O

def Arc.Greater (a : Arc) : Prop :=
  ∃ O : Point, Centre O a.circle ∧ SameSideOf O a.K a.B a.C

def Arc.SameKind (a b : Arc) : Prop :=
  (a.Less ∧ b.Less) ∨ (a.Semicircle ∧ b.Semicircle) ∨ (a.Greater ∧ b.Greater)

noncomputable def Arc.measure (a : Arc) : Angle :=
  circumference a.circle a.B a.K a.C

def Places (f : Point → Point) (S T : Point → Prop) : Prop :=
  (∀ P, S P → T (f P)) ∧ (∀ Q, T Q → ∃ P, S P ∧ f P = Q) ∧
    ∀ P Q, S P → S Q → ‖(f P) (f Q)‖ = ‖P Q‖

def Arc.Congruent (a b : Arc) : Prop :=
  ∃ f : Point → Point, f a.B = b.B ∧ f a.C = b.C ∧
    Places f (InSegment · a) (InSegment · b) ∧ Places f (OnArc · a) (OnArc · b)
```

- **In plain words.** An arc (Definition III.6) is a circle, the ends B, C of its base,
  and a point K naming the side, which need not be on the circle. It is drawn when its
  circle has a centre, B and C are on it, and K is off BC. A closed half-plane, for B ≠ C:
  K's side of BC, or BC itself. The arc's points: on the circle and in that half-plane; the
  segment's: inside or on the circle, and in it. The kind is decided by the centre: beyond
  the base (less than a semicircle), on it, or on the arc's side (greater), as III.25
  decides it. The measure is the circumference BKC, twice the angle that stands on it
  (Definition III.9); it carries no radius. A map places S on T when it carries S into T,
  every point of T comes from S, and it keeps every distance between points of S. Two
  segments are congruent when one map puts the ends on the ends, in order, and places the
  segment on the segment and the arc on the arc.
- **Similar segments** (Definition III.11, with the angle in a segment of Definition
  III.8) stay as today: equal angles at points of the arcs, III.24's `hsim`.
- The four-argument `circumference` and `standing` stay as Heath's measure words.

### I.20's degenerate case

`Staging/Stage3/Degenerate.lean`, for `Elements/BookI/HelpersTriangles.lean`. This is the
one statement of the fact in Staging: the stage 2 draft had a second, with the distances in
another order, removed when the two drafts were merged.

```lean
theorem Prop20.collinear_iff {A B P : Point} :
    Collinear A B P ↔
      ‖A B‖ = ‖A P‖ + ‖P B‖ ∨ ‖A P‖ = ‖A B‖ + ‖B P‖ ∨ ‖B P‖ = ‖B A‖ + ‖A P‖

theorem Prop20.collinear_congr {A B P C D Q : Point} (hAB : ‖A B‖ = ‖C D‖)
    (hAP : ‖A P‖ = ‖C Q‖) (hBP : ‖B P‖ = ‖D Q‖) : Collinear A B P ↔ Collinear C D Q

theorem Prop20.between_iff {A B P : Point} :
    Between A P B ↔ ‖A P‖ ≠ 0 ∧ ‖P B‖ ≠ 0 ∧ ‖A P‖ + ‖P B‖ = ‖A B‖

theorem Prop20.between_congr {A B P C D Q : Point} (hAB : ‖A B‖ = ‖C D‖)
    (hAP : ‖A P‖ = ‖C Q‖) (hBP : ‖B P‖ = ‖D Q‖) : Between A P B ↔ Between C Q D
```

- **In plain words.** Three points are on one straight line exactly when one distance among
  them is the other two together; P is between A and B exactly when it is neither end and
  AP, PB make AB. So both are decided by the three distances, and carry across to points
  with the same distances.
- **Proved here:** the two `congr` forms, from the other two. **To prove:**
  `collinear_iff` from I.20 off the line and `between_cases`, `len_add_of_between` on it;
  `between_iff` likewise.
- **Users.** Placement; stage 4's `Prop14.general` and `Prop15.le_diameter`.

### Book Zero for arcs

`Staging/Stage3/Chord.lean`, for `Elements/Figure/Chords.lean`.

```lean
theorem chord_cases {A B P : Point} {α : Circle} (hA : OnCircle A α) (hB : OnCircle B α)
    (hAB : A ≠ B) (hP : Collinear A B P) :
    (OnCircle P α ↔ P = A ∨ P = B) ∧ (InsideCircle P α ↔ Between A P B)

theorem Arc.meets {a : Arc} (ha : a.Drawn) {X Y : Point} (hX : Between a.B X a.C)
    (hY : SameSideOf Y a.K a.B a.C) : ∃ Q : Point, OnArc Q a ∧ OnRay Q X Y

theorem Arc.congr_side {α : Circle} {B C K K' : Point} (h : SameSideOf K K' B C) :
    (∀ P : Point, OnArc P ⟨α, B, C, K⟩ ↔ OnArc P ⟨α, B, C, K'⟩) ∧
      (∀ P : Point, InSegment P ⟨α, B, C, K⟩ ↔ InSegment P ⟨α, B, C, K'⟩)

theorem Arc.Congruent.congr_side {α β : Circle} {B C K K' D E L L' : Point}
    (h : Arc.Congruent ⟨α, B, C, K⟩ ⟨β, D, E, L⟩) (hK : SameSideOf K K' B C)
    (hL : SameSideOf L L' D E) : Arc.Congruent ⟨α, B, C, K'⟩ ⟨β, D, E, L'⟩
```

- **In plain words.** A point of the straight line through two points of a circle is on the
  circle exactly when it is one of them, and within it exactly when it is between them. A
  ray from a point within the base, towards the arc's side, meets the arc. Only the side
  names an arc: naming points on one side give the same arc and segment, and a congruence
  carries over to them by the same map.
- **Proved here:** `chord_cases`, `Arc.congr_side`, `Arc.Congruent.congr_side`. **To
  prove:** `Arc.meets` (System E, Circle 2, Intersections 5, Pasch 3).
- **Why `congr_side`.** III.24 concludes congruence for arcs named by points on the circle
  (E, F); III.26 and III.28 name their arcs by side points (K, L, C, G, F, H) that need not
  be on it; `Arc.congruent_iff` takes any drawn arcs.

### Placement

`Staging/Stage3/Placement.lean` (the assembly, proved from the stubs) and
`Staging/Stage3/Placement/` (the cases), for `Elements/BookIII/Placement.lean` and
`Elements/BookIII/Placement/`.

```lean
theorem placement {A B C D E F : Point} (hE : ¬ Collinear A B E) (hF : ¬ Collinear C D F)
    (hlen : ‖A B‖ = ‖C D‖) :
    ∃ f : Point → Point, f A = C ∧ f B = D ∧
      Places f (OnSideOrLine · E A B) (OnSideOrLine · F C D) ∧
      ∀ P : Point, OnSideOrLine P E A B → ‖C (f P)‖ = ‖A P‖ ∧ ‖D (f P)‖ = ‖B P‖ ∧
        (SameSideOf P E A B ↔ SameSideOf (f P) F C D) ∧ (Between A P B ↔ Between C (f P) D)

theorem Placement.exists {A B C D E F P : Point} (hE : ¬ Collinear A B E)
    (hF : ¬ Collinear C D F) (hlen : ‖A B‖ = ‖C D‖) (hP : OnSideOrLine P E A B) :
    ∃ Q : Point, OnSideOrLine Q F C D ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖

theorem Placement.unique {C D F Q₁ Q₂ : Point} (hF : ¬ Collinear C D F)
    (hQ₁ : OnSideOrLine Q₁ F C D) (hQ₂ : OnSideOrLine Q₂ F C D) (hC : ‖C Q₁‖ = ‖C Q₂‖)
    (hD : ‖D Q₁‖ = ‖D Q₂‖) : Q₁ = Q₂

theorem Placement.dist_off_off {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hPQ : SameSideOf P Q A B) (hP'Q' : SameSideOf P' Q' C D)
    (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖) (hQ₁ : ‖C Q'‖ = ‖A Q‖)
    (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖

theorem Placement.dist {A B C D E F P Q P' Q' : Point} (hE : ¬ Collinear A B E)
    (hlen : ‖A B‖ = ‖C D‖) (hP : OnSideOrLine P E A B) (hQ : OnSideOrLine Q E A B)
    (hP' : OnSideOrLine P' F C D) (hQ' : OnSideOrLine Q' F C D)
    (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖) (hQ₁ : ‖C Q'‖ = ‖A Q‖)
    (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖
```

The cases, each in a file of its own so that parallel provers never share one:

```lean
-- Placement/Exists.lean
theorem Placement.exists_off {A B C D F P : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hF : ¬ Collinear C D F) (hP : ¬ Collinear A B P) :
    ∃ Q : Point, SameSideOf Q F C D ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖

theorem Placement.exists_on {A B C D P : Point} (hlen : ‖A B‖ = ‖C D‖) (hAB : A ≠ B)
    (hP : Collinear A B P) :
    ∃ Q : Point, Collinear C D Q ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖

-- Placement/Unique.lean
theorem Placement.unique_off {C D F Q₁ Q₂ : Point} (hQ₁ : SameSideOf Q₁ F C D)
    (hQ₂ : SameSideOf Q₂ F C D) (hC : ‖C Q₁‖ = ‖C Q₂‖) (hD : ‖D Q₁‖ = ‖D Q₂‖) : Q₁ = Q₂

theorem Placement.unique_on {C D Q₁ Q₂ : Point} (hCD : C ≠ D) (hQ₁ : Collinear C D Q₁)
    (hQ₂ : Collinear C D Q₂) (hC : ‖C Q₁‖ = ‖C Q₂‖) (hD : ‖D Q₁‖ = ‖D Q₂‖) : Q₁ = Q₂

-- Placement/OnLine.lean
theorem Placement.dist_on_on {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hAB : A ≠ B) (hP : Collinear A B P) (hQ : Collinear A B Q) (hP' : Collinear C D P')
    (hQ' : Collinear C D Q') (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖)
    (hQ₁ : ‖C Q'‖ = ‖A Q‖) (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖

-- Placement/Mixed.lean
theorem Placement.dist_on_off {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hP : Collinear A B P) (hQ : ¬ Collinear A B Q) (hP' : Collinear C D P')
    (hQ' : ¬ Collinear C D Q') (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖)
    (hQ₁ : ‖C Q'‖ = ‖A Q‖) (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖

-- Placement/Strict.lean
theorem Placement.base_choice {A B P Q : Point} (hPQ : SameSideOf P Q A B) (hne : P ≠ Q) :
    ∠ B A P ≠ ∠ B A Q ∨ ∠ A B P ≠ ∠ A B Q

theorem Placement.dist_strict {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hPQ : SameSideOf P Q A B) (hP'Q' : SameSideOf P' Q' C D)
    (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖) (hQ₁ : ‖C Q'‖ = ‖A Q‖)
    (hQ₂ : ‖D Q'‖ = ‖B Q‖) (hlt : ∠ B A P < ∠ B A Q) : ‖P' Q'‖ = ‖P Q‖
```

- **In plain words.** On equal straight lines AB, CD, with E off AB and F off CD, there is
  a map that puts A on C and B on D and carries the points on E's side of AB, or on AB,
  onto the points on F's side of CD, or on CD, keeping every distance between them; each
  point goes to the point as far from C as it was from A and from D as it was from B; and
  a point is on E's side, or between A and B, exactly when its image is on F's side, or
  between C and D. This is Euclid's "let the point A be placed on C and the straight line
  AB on CD", with no motion assumed beyond I.4 and I.8.
- **Route, with the citations corrected.** The place of each point is chosen
  (`Classical.epsilon`). It exists: off the base by I.22, the triangle on CD with sides AP,
  BP meeting I.20's condition because ABP is a triangle; on the base by I.3, or by
  producing CD (`produce`, `OnRay.exists_len_eq`). It is the only one: off the base by I.7;
  on it by the order of points (`OnRay.eq_of_len_eq`, `len_add_of_between`); never one on
  and one off, by I.20's degenerate case. Distances are kept: two points of the base by
  their order; a point of the base and one off it by I.8 and then I.4, the end of the base
  chosen so that the point of the base lies on the ray through the other end; two points
  off the base by `base_choice` (at A if the angles BAP, BAQ differ, else at B), then I.8,
  `Prop24.within` (I.24's step), `angle_add_of_within`, C.N. 3 and I.4. Onto: the same
  construction run back from CD to AB. Brief 0005's "existence from I.23 … and I.4" and
  "proved from I.4, I.7, I.8, I.20 and I.23" are withdrawn.
- **Proved here:** `placement` and the four assembly lemmas, from the stubs; and
  `Placement.unique_off`, which is I.7. **To prove:** the seven stubbed cases.
- **The policy.** Outside `Elements/BookIII/Placement.lean` and
  `Elements/BookIII/Placement/`, only III.24 and `Arcs.lean` may cite `placement` or any
  declaration of the `Placement` namespace: the sub-lemmas carry the same distance-keeping
  content, and a check confined to `placement` could be got round through them. The check
  joins `check_fidelity.py` with a negative test.
- **Superposition, checked as it can be.** `#print axioms placement` lists
  `Tacit.superposition`, and always will: placement cites I.7, and its cases cite I.4 and
  I.8, which rest on it, as every congruence does. Brief 0005's check "`#print axioms` of
  `placement` shows no superposition" can never pass and is withdrawn. The check is that
  `placement` and its sub-lemmas use `Tacit.superposition` nowhere directly (the walk
  through helpers that `check_fidelity.py`'s `direct_axioms` policy uses, which stops at
  I.4, I.7 and I.8 as entries), and that `#print axioms` lists only axioms in the lock.

### III.23, point by point

`Staging/Stage3/Prop23Point.lean`. A companion of III.23, "III.23 point", for
`Elements/BookIII/Prop23.lean` after III.23.

```lean
theorem Prop23.point {A B E P : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α) (hB : OnCircle B α) (hE : OnCircle E α) (hPE : SameSideOf P E A B) :
    (OnCircle P α ↔ ∠ A P B = ∠ A E B) ∧ (InsideCircle P α ↔ ∠ A E B < ∠ A P B)
```

- **In plain words.** On E's side of a chord AB of a circle through E, a point is on the
  circle exactly when the chord subtends at it the angle AEB, and within it exactly when it
  subtends a greater angle. It is III.23's content ("there cannot be constructed two
  similar and unequal segments … on the same side"), point by point.
- **Companion, not a shared step** (the two readers who raised it offered both; this brief
  takes the companion). III.24 cites it for the cases Euclid leaves to III.23, a segment
  falling within the other or outside it, which Heath says are disposed of by a tacit
  reference to III.23 (vol. 2, p. 54). As III.23's companion, that dependency shows in
  III.24's certificate.
- **Proof plan.** Through a point M between A and B, which is within the circle. On the
  circle: III.21. Outside: the finite straight line PM meets the arc at Q, within the
  triangle ABP, so the angle at Q is the greater [I. 21]. Within: MP produced beyond P
  meets the circle at Q, and P is within the triangle ABQ [I. 21]. In both, the angle AQB
  is the angle AEB [III. 21]. (The spike's plan, drawing AP on, fails when AP touches the
  circle at A.)
- **Dependencies.** I.21, III.21; Book Zero's meeting and side rules.

### Arcs on one base

`Staging/Stage3/Aligned.lean`, a shared step for `Elements/BookIII/Squares.lean` (it cites
I.7 and nothing of Book III). Not a companion: its hypotheses are not III.23's.

```lean
theorem Arc.eq_of_aligned {a b : Arc} (ha : a.Drawn) (hb : b.Drawn) (hB : a.B = b.B)
    (hC : a.C = b.C) (hK : SameSideOf a.K b.K a.B a.C)
    (hcircles : EqualCircles a.circle b.circle) (hkind : Arc.SameKind a b) :
    a.circle = b.circle ∧ (∀ P : Point, OnArc P a ↔ OnArc P b) ∧
      (∀ P : Point, InSegment P a ↔ InSegment P b)
```

- **In plain words.** Two drawn arcs on one base, on one side, in equal circles and of one
  kind, are one arc in one circle. **Plan:** the centres are equally far from the ends and
  lie alike, so they are one point (I.7 off the base, the order on it); `circle_eq`.

### Adding circumferences

`Staging/Stage3/CircumferenceAdd.lean`, for `Elements/BookIII/Circumferences.lean`; ground
for Book IV, cited by nothing in Book III.

```lean
theorem Circumference.add {B C D K X Y : Point} {α : Circle} (hα : ∃ O : Point, Centre O α)
    (hB : OnCircle B α) (hC : OnCircle C α) (hD : OnCircle D α) (hCK : SameSideOf C K B D)
    (hX : OppositeSidesOf X D B C) (hY : OppositeSidesOf Y B C D) :
    circumference α B X C + circumference α C Y D = circumference α B K D
```

- **In plain words.** With C on the arc BD on K's side, the circumferences BC and CD make up
  BD. **Plan:** the measures at D and B, the whole at a point beyond BD [III. 21], the angles
  of BCD [I. 32], and the quadrilateral in the circle [III. 22].

### III.24 restated

`Staging/Stage3/Prop24.lean`. The main theorem, with companions "III.24 equalCircles" and
"III.24 equalMeasure".

```lean
/-- Similar segments of circles on equal straight lines are equal to one another. -/
theorem Prop24 {A B C D E F : Point} {AEB CFD : Circle} (hAEB : ∃ O : Point, Centre O AEB)
    (hCFD : ∃ O : Point, Centre O CFD) (hA : OnCircle A AEB) (hB : OnCircle B AEB)
    (hE : OnCircle E AEB) (hC : OnCircle C CFD) (hD : OnCircle D CFD)
    (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E) (hF_CD : ¬ Collinear C D F)
    (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    Arc.Congruent ⟨AEB, A, B, E⟩ ⟨CFD, C, D, F⟩

theorem Prop24.equalCircles {A B C D E F : Point} {AEB CFD : Circle}
    (hAEB : ∃ O : Point, Centre O AEB) (hCFD : ∃ O : Point, Centre O CFD)
    (hA : OnCircle A AEB) (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD)
    (hD : OnCircle D CFD) (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E)
    (hF_CD : ¬ Collinear C D F) (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :
    EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D

theorem Prop24.equalMeasure {a b : Arc} (ha : a.Drawn) (hb : b.Drawn)
    (h : Arc.Congruent a b) : a.measure = b.measure
```

- **In plain words.** Similar segments AEB, CFD on equal bases AB, CD are congruent: one
  map puts A on C and B on D, the segment on the segment and the arc on the arc, keeping
  every distance between their points. `Prop24.equalCircles` is today's statement, the
  circles equal and the circumferences equal in measure (checked against
  `type_of% @Prop24`). `Prop24.equalMeasure`: congruent segments have circumferences equal
  in measure.
- **Coverage.** Heath: "Similar segments of circles on equal straight lines are equal to one
  another." Full, with "equal" read as coincide (C.N. 4); the record's omitted clause "are
  equal to one another" is now proved. Tags: `segment-with-circle`, `centre-given`; for the
  companions, `angle-measure`, and `redundant-hypothesis` (the measure clause of
  `equalCircles` holds without the equal bases).
- **Cases.** Segments less than, equal to and greater than a semicircle, in one argument;
  points of the base (ends, between) by `chord_cases`; points off the base by
  `Prop23.point`.
- **Route: `modified`.** The proof (proved here from the stubs) keeps Euclid's
  application: `placement` puts A on C and AB on CD, and B on D. The coincidence of the
  arcs is argued directly, point by point, by the angles (I.8 at each point and its image,
  then `Prop23.point`), in place of his reductio. The record's passages, planned:
  - "For, if the segment AEB be applied to CFD": `helper`, `placement`.
  - "the point B will also coincide with the point D" and "and, AB coinciding with CD":
    carried.
  - "the segment AEB will also coincide with CFD.": `grouped` with the sentences after it,
    which show it; the Lean begins that argument here (I.8).
  - "it will either fall within it, or outside it;": `different`. Euclid leaves these two
    cases to a tacit reference to III.23 (Heath, vol. 2, p. 54), refuted by reductio; the
    Lean settles every point directly by III.23's companion.
  - "or it will fall awry": `different`. III.10 is not needed: the angles have settled
    every point, so there is no third case.
  - The last two sentences: carried (`chord_cases` on the base; the congruence, C.N. 4).
- **The alternative proof.** `Prop24.equalCircles` keeps today's proof by the radii (the
  angles at the centres, III.20, III.22, `Prop24.isosceles`, `Prop24.angle_type`) and is
  shown on the page as the labelled alternative, with Euclid's text in full under the main
  proof (FORMALIZATION, section 5). The renderer's support for it is stage 3
  infrastructure.
- **Why `Prop24.equalMeasure`.** Today III.26 takes `.2` of III.24, the equal measures, for
  its whole minus part (`Prop26.lean`, line 92). The restated III.24 gives only congruence,
  and the only other theorem from congruence to measure, `Arc.congruent_iff`, comes after
  III.29, where III.26 may not cite it. III.26 cites `Prop24.equalMeasure` after III.24.
  **Plan:** a point P of the first arc off its base [`exists_onCircle_sameSideOf`] goes to a
  point of the second arc off its base (neither end, by the distances and `chord_cases`);
  the angle at P is the angle at its image [I. 8]; the circumference beyond each base is
  twice that angle (`Circumference.eq`), and with it makes up the whole circle
  (`Circumference.whole`); so the two are equal [C.N. 3].
- **Dependencies.** III.24: `placement`, `Prop23.point`, `chord_cases`, I.8.
  `equalCircles`: today's (III.20, III.22, I.5, I.26, I.32, `Circumference.whole`,
  `Circumference.eq`). `equalMeasure`: I.8, `Circumference.eq`, `Circumference.whole`,
  `chord_cases`. Not III.10.

### III.26 upgraded

`Staging/Stage3/Prop26.lean`. It replaces today's statement.

```lean
theorem Prop26 {A B C D E F G H K L : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :
    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩) ∧
    (∠ B A C = ∠ E D F →
      circumference ABC B K C = circumference DEF E L F ∧
        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩)
```

- **In plain words.** In equal circles, equal angles at the centres, or at the
  circumferences, stand on circumferences equal in measure and congruent. Today's statement
  follows by the first conjuncts (checked by Lean).
- **Coverage.** Heath: "In equal circles equal angles stand on equal circumferences, whether
  they stand at the centres or at the circumferences." Full; "equal circumferences" is read
  as equal in measure and congruent, more than Heath's words. "In equal circles" now does
  work: in unequal circles equal angles give no congruence. The `redundant-hypothesis` tag
  leaves III.26's record, and its audit example goes (below).
- **Route.** Euclid's for the measures: the segments BAC, EDF are congruent [III. 24], so
  their circumferences are equal in measure (`Prop24.equalMeasure`), and the remainders
  BKC, ELF are equal, the wholes being equal [C.N. 3]. The congruence of the remainders
  cannot come by subtraction: it comes from III.24 applied to the remaining segments, which
  are similar, their angles making two right angles with the equal angles at A and D
  [III. 22], with `Arc.Congruent.congr_side` for K and L. That step is a `different`
  passage, a mild departure from Euclid's "whole minus part", disclosed in the Lean and the
  mishnah.
- **Dependencies.** I.4, III.20, III.22, III.24, "III.24 equalMeasure",
  `Circumference.whole`, `Prop24.angle_type`, `Arc.Congruent.congr_side`.

### III.28 upgraded

`Staging/Stage3/Prop28.lean`. It replaces today's statement.

```lean
theorem Prop28 {A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)
    (hCG : OppositeSidesOf C G A B) (hFH : OppositeSidesOf F H D E) (hAB : ‖A B‖ = ‖D E‖)
    (hABC : circumference ABC A G B ≤ circumference ABC A C B)
    (hDEF : circumference DEF D H E ≤ circumference DEF D F E) :
    (circumference ABC A C B = circumference DEF D F E ∧
        Arc.Congruent ⟨ABC, A, B, C⟩ ⟨DEF, D, E, F⟩) ∧
      (circumference ABC A G B = circumference DEF D H E ∧
        Arc.Congruent ⟨ABC, A, B, G⟩ ⟨DEF, D, E, H⟩)
```

- **In plain words.** In equal circles, equal straight lines cut off circumferences equal in
  measure and congruent, the greater to the greater and the less to the less. Today's
  statement follows by the first conjuncts (checked by Lean).
- **Coverage.** Heath: "In equal circles equal straight lines cut off equal circumferences,
  the greater equal to the greater and the less to the less." Full, with "equal" read as for
  III.26.
- **Cases.** AB off the centre (a less and a greater circumference); AB through the centre
  (four semicircles).
- **Route.** Euclid's where it can be: the angles at the centres are equal [I. 8], so the
  less circumferences are equal in measure and congruent [III. 26], and the greater are
  equal in measure as remainders [C.N. 3]. Two steps depart, as III.26's congruence does:
  the congruence of the greater circumferences comes from III.24, or III.26's clause at the
  circumference, applied to the greater segments, not by remainder; and when AB passes
  through the centre there is no angle at the centre, so the right angle in each semicircle
  (`Prop24.angle_type`; III.31 comes later) and III.24 give the congruence. Both are
  disclosed where they happen.
- **Dependencies.** I.8, III.24, III.26, `Prop28.diameter`, `Prop28.sides`,
  `Prop24.angle_type`, `Arc.Congruent.congr_side`.

### What equal measures mean: `Arcs.lean`

`Staging/Stage3/Arcs.lean`, for `Elements/BookIII/Arcs.lean`, after III.29, so that the
argument cannot go round in a circle (FORMALIZATION, section 3).

```lean
theorem Arc.measure_eq_iff {a b : Arc} (ha : a.Drawn) (hb : b.Drawn)
    (hcircles : EqualCircles a.circle b.circle) :
    a.measure = b.measure ↔ ‖a.B a.C‖ = ‖b.B b.C‖ ∧ Arc.SameKind a b

theorem Arc.congruent_iff {a b : Arc} (ha : a.Drawn) (hb : b.Drawn) :
    Arc.Congruent a b ↔ EqualCircles a.circle b.circle ∧ a.measure = b.measure
```

- **In plain words.** In equal circles, two arcs have equal measures exactly when their
  chords are equal and they are of one kind. Two drawn arcs are congruent exactly when their
  circles are equal and their measures are equal.
- **Plans.** `measure_eq_iff` by III.28, III.29 (`Prop29.size`) and the comparison of each
  kind with a semicircle. `congruent_iff`: one way cites `Prop24.equalMeasure` for the
  measures and `Prop24.equalCircles` for the circles (the congruence keeps the chord and,
  at a point of the arc and its image, the angle [I. 8]), and proves neither again; the
  other way, `measure_eq_iff`, then the angles in the segments, then III.24.
- These are the bridge theorems for the representation (FORMALIZATION, section 3): they
  say what `circumference` and `Arc.Congruent` mean.

## Stage 4: III.14, III.15, III.25

### The foot of the perpendicular

`Staging/Stage4/Foot.lean`: `Foot` for `DefinitionsIII.lean`; `Foot.exists` and
`Foot.unique` for `Elements/BookIII/Squares.lean`.

```lean
def Foot (E A B F : Point) : Prop :=
  Collinear A B F ∧ (Collinear A B E → F = E) ∧
    (¬ Collinear A B E → ∀ P : Point, Collinear A B P → P ≠ F → ∠ E F P = ∟)

theorem Foot.exists (E A B : Point) : ∃ F : Point, Foot E A B F

theorem Foot.unique {E A B F F' : Point} (hF : Foot E A B F) (hF' : Foot E A B F') :
    F = F'
```

- **In plain words.** F is the foot of the perpendicular from E to AB: on the straight line
  AB, making a right angle with every other point of it when E is off it, and E itself when
  E is on it. If A and B are one point, the foot is E. EF is the distance of AB from E
  (Definitions III.4 and III.5, extended: it is nothing when AB passes through E, a case
  Euclid's definitions do not take). Every straight line has one foot [I. 12, I. 17].

### III.14 with diameters

`Staging/Stage4/Prop14.lean`. Companion "III.14 general".

```lean
theorem Prop14.general {A B C D E F G : Point} {ABDC : Circle} (hE : Centre E ABDC)
    (hA : OnCircle A ABDC) (hB : OnCircle B ABDC) (hC : OnCircle C ABDC)
    (hD : OnCircle D ABDC) (hAB : A ≠ B) (hCD : C ≠ D) (hF : Foot E A B F)
    (hG : Foot E C D G) :
    ‖A B‖ = ‖C D‖ ↔ ‖E F‖ = ‖E G‖
```

- **In plain words.** In a circle, straight lines AB, CD are equal exactly when the feet of
  the perpendiculars from the centre are equally far from it. Today's III.14 follows for
  two straight lines not through the centre (checked by Lean).
- **Coverage.** Heath: "In a circle equal straight lines are equally distant from the
  centre, and those which are equally distant from the centre are equal to one another."
  Full; the `diameters-excluded` restriction goes.
- **Cases.** Two straight lines not through the centre (III.14); two diameters (equal, both
  at distance nothing); one of each (the diameter is greater [I. 20], and the other is at
  some distance, `len_ne_zero`).
- **Dependencies.** III.14, I.20 (`Prop20.collinear_iff`), `Foot.unique`.

### III.15, both clauses for every straight line

`Staging/Stage4/Prop15.lean`. Companions "III.15 le_diameter", "III.15 nearer".

```lean
theorem Prop15.le_diameter {A B C D E : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) :
    ‖B C‖ ≤ ‖A D‖ ∧ (‖B C‖ = ‖A D‖ ↔ Between B E C)

theorem Prop15.nearer {B C E F G H K : Point} {ABCD : Circle} (hE : Centre E ABCD)
    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hF : OnCircle F ABCD)
    (hG : OnCircle G ABCD) (hBC : B ≠ C) (hH : Foot E B C H) (hK : Foot E F G K)
    (hnearer : ‖E H‖ < ‖E K‖) :
    ‖F G‖ < ‖B C‖
```

- **In plain words.** No straight line in a circle is greater than the diameter, and one is
  equal to it exactly when it passes through the centre. Of two straight lines, the one
  whose foot is nearer the centre is the greater; the nearer may be a diameter. Today's
  III.15 follows (checked by Lean).
- **Coverage.** Heath: "Of straight lines in a circle the diameter is greatest, and of the
  rest the nearer to the centre is always greater than the more remote." Full.
- **Route.** `le_diameter` by Euclid's step, BE, EC together greater than BC [I. 20], with
  the equality case from `Prop20.collinear_iff`; `nearer` by his argument [III. 14, I. 24],
  with the diameter case by `le_diameter`.
- **Dependencies.** I.20, I.24, III.14 general, `Foot.exists`, `Foot.unique`.

### III.25 restated: a construction core and its correctness

`Staging/Stage4/Prop25.lean`. The main theorem, with companions "III.25 complete" and
"III.25 of_circle".

```lean
/-- Given a segment of a circle, to describe the complete circle of which it is a segment. -/
theorem Prop25 {A C P : Point} {S : Point → Prop} (hP : ¬ Collinear A C P)
    (hmeet : ∀ X Y : Point, Between A X C → SameSideOf Y P A C →
      ∃ B : Point, S B ∧ OnRay B X Y) :
    ∃ (B D E : Point) (γ : Circle), S B ∧ SameSideOf B P A C ∧ Between A D C ∧
      ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E γ ∧ OnCircle A γ ∧ OnCircle B γ ∧
      OnCircle C γ ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C)

theorem Prop25.complete {A C P B E : Point} {α γ : Circle} (hα : ∃ O : Point, Centre O α)
    (hA : OnCircle A α) (hC : OnCircle C α) (hB : OnArc B ⟨α, A, C, P⟩)
    (hBP : SameSideOf B P A C) (hE : Centre E γ) (hAγ : OnCircle A γ) (hBγ : OnCircle B γ)
    (hCγ : OnCircle C γ) :
    γ = α ∧ ∀ X : Point, OnArc X ⟨α, A, C, P⟩ → OnCircle X γ

theorem Prop25.of_circle {A C : Point} {ABC : Circle} (hABC : ∃ E : Point, Centre E ABC)
    (hA : OnCircle A ABC) (hC : OnCircle C ABC) :
    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧
      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧
      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧
      (∠ A B D < ∠ B A D → SameSideOf E B A C)
```

- **In plain words.** The core is given only the segment's base AC, a point P on its side,
  and its points as a predicate S, with the fact Euclid reads off the figure: every ray from
  a point within AC towards P's side meets S. It never sees a circle or a centre. It
  returns B in S, the midpoint D of AC with the angle ADB right, and a circle γ with centre
  E on DB, through A, B and C (Postulate 3), E beyond AC, at D, or on B's side as the angles
  at A and B decide. `Prop25.complete`: for S the arc of a circle α, any circle through A,
  B and C with a centre is α, and holds every point of the arc. `Prop25.of_circle` is
  today's statement, proved from the core, `Arc.meets` and `complete` (checked against
  `type_of% @Prop25`).
- **The statement is the pair.** The core alone does not say that γ is the circle the
  segment came from: S need not lie on any circle, and nothing puts S on γ. Heath's "the
  complete circle of which it is a segment" is carried by `Prop25.complete`. So III.25's
  frozen statement is the core with `Prop25.complete`: the record lists the companions
  (SCHEMA: "When companions are listed, `scope` describes the main theorem together with
  them, and the note says which declaration covers what"), its scope is full for the pair,
  and its note and the page say that the clause "of which it is a segment" is
  `Prop25.complete`'s. `Prop25.of_circle` stays as a companion, so that today's statement
  keeps its certificate; nothing in `Elements/` cites III.25 today.
- **Construction** (FORMALIZATION, section 4, of which this is the pilot). Given: the base,
  the side, the segment's points and the meeting fact. Operations: bisect AC [I. 10], the
  perpendicular DB [I. 11] meeting the segment (the meeting fact), the angle ABE equal to
  BAD [I. 23], and the circle with centre E through A (Postulate 3). Returned: B, D, E, γ.
  Shown: EA, EB, EC are equal [I. 6, I. 4], so γ passes through all three; and, by
  `Prop25.complete`, γ is the segment's circle [III. 9 or III. 10, `circle_eq`].
- **Cases.** The segment less than a semicircle (E beyond AC), a semicircle (E at D), and
  greater (E on B's side), as Euclid's three.
- **Route.** Euclid's construction; his "[III. 9]" step, which finds the centre of the
  given circle, moves out to `Prop25.complete`, declared as a passage.
- **Dependencies.** The core: I.4, I.6, I.10, I.11, I.23, Postulate 3. `complete`: III.9 or
  III.10, `circle_eq`. `of_circle`: the core, `Arc.meets`, `complete`.

## What the spike found

The stage 3 spike (brief 0005's step 0) stated the definitions, `placement` and every case
with `sorry`, proved the assembly from the stubs, and proved III.24, restated, from stubbed
`placement` and `Prop23.point`. To get the assembly and III.24 through, the interfaces
changed from brief 0005's in these ways:

- **Placement says more.** Besides keeping distances, it gives each point's distances from
  C and D, and carries "on E's side" and "between A and B" both ways. III.24 needs the side
  clause, so that a point off the base goes off the base and `Prop23.point` applies at its
  image, and the between clause, so that `chord_cases` decides the points of the base.
- **The half-plane is closed,** `OnSideOrLine`, so that the base is carried with the
  segment, and `Places` asks for onto as well as into.
- **I.20's degenerate case** decides "on the base" and "between" by distances alone. It is
  what makes the place unique when one candidate is on the base and one off it, and what
  proves the side and between clauses. It needs a Book I helper file after I.20, since
  `Elements/BookI/Helpers.lean` comes before I.7.
- **The comparison is based at whichever end gives unequal angles** (`base_choice`), which
  removes the equal-angle and supplementary-angle branches of the off-base case.
- **Existence is by I.22** off the base, and by I.3 and producing on it, not by I.23 and
  I.4; uniqueness is by I.7, the order on the line, and I.20's degenerate case.
- **Five case files,** so that parallel provers never share one, and a policy check over
  the whole `Placement` namespace.
- **A drawn arc has a centre** (`Arc.Drawn`), because `Prop23.point` needs one.
- **III.24 uses only** `placement`, `Prop23.point`, `chord_cases` (proved) and I.8. III.10 is
  not needed.
- **III.25's interfaces fit:** today's statement follows from the core, `Arc.meets` and
  `Prop25.complete`.

The challenges then added what the restatements' consumers need: `Prop24.equalMeasure` and
`Prop24.equalCircles` (III.26 and `Arcs.lean`), `Arc.congr_side` and its corollary (arcs
named by side points), `Fitted.inside_pairwise` (the meaning of the gluing rule, withdrawn
with `Fitted` on 17 October and restored with it on 18 October), and a plan for `Prop23.point` that does not fail at a tangent.

## The order of proof work

Stages 2 and 3 run alongside each other, on separate files; stage 4 follows. Each step
leaves `lake build`, `lake build Audit` and `lake build Staging` green.

**Stage 2.**
1. Ground (wave R1): the words into the foundations, with the lock and a decisions entry;
   `Elements/Figure/Sums.lean`; `Elements/Figure/Rectilineal.lean`, with `Fitted.fan` there
   or in I.45's file as its proof decides; and the `Placement` policy check. The certificate and
   render support for companions is already in place: it landed on 17 October 2026, and
   `Certificate/Facts.lean` checks each entry of `Elements/Companions.lean`,
   `scripts/render.py` shows each companion and `scripts/check_fidelity.py` applies the
   policies to companions.
2. I.40, II.1, I.45 in parallel (best of two each); II.14 after I.45's statements are
   stable, against `Prop45.sum`. `Fitted.fan` alongside, by one prover: `Prop45.fan` and
   `Prop14.fan` wait for it, and if it stalls they stay unproved, the fitting implication
   unformalized and the fan no longer presented as Lean-checked (I.45, the fan's two
   conditions).
3. Records, pages, mishnah notes; the `figure-with-dissection` tag added before the I.45
   and II.14 records use it; the gap catalogue entries for I.45 and II.14, as planned above.

**Stage 3: placement, steps 1–4** (step 0, the spike, is done):
1. **One strong prover:** `Placement.base_choice` and `Placement.dist_strict`
   (`Placement/Strict.lean`), the hardest case.
2. **Codex, best of two, in parallel, on separate files:** the I.20 lemmas
   (`HelpersTriangles.lean`), existence (`Placement/Exists.lean`, by I.22),
   `Prop23.point` (`Prop23.lean`) and `Arc.eq_of_aligned` (`Squares.lean`).
3. **Codex:** uniqueness (`Placement/Unique.lean`: I.7 off the line, the order on it),
   both points on the line (`Placement/OnLine.lean`), and the mixed case
   (`Placement/Mixed.lean`, with the I.20 lemmas).
4. **The strong prover:** the assembly (`Placement.lean`), then III.24, III.26 and III.28,
   then `Arcs.lean`.

Alongside, the stage 3 ground task: `Elements/Figure/Chords.lean` and
`Circumference.add`. If any case needs a fact the axioms lack, work on it stops and Jack
decides (decision 3).

**Stage 3: the migration into `Elements/`,** each step green:
1. the arc words into `DefinitionsIII.lean`, with the lock and a decisions entry;
2. the ground: `Chords.lean`, `HelpersTriangles.lean`, the placement files,
   `Prop23.point`, `Arc.eq_of_aligned`, `Circumference.add`;
3. `Prop24.equalCircles` (today's proof, moved) and `Prop24.equalMeasure`, beside today's
   III.24, both approved here before step 4;
4. III.24 restated; `Prop26.lean`, line 92 switched to III.24 and `Prop24.equalMeasure`;
   `Audit/Overlaps.lean`'s III.24 example pointed at `Prop24.equalCircles`;
5. III.26 upgraded (fix `Prop27.lean`, line 74 and `Prop28.lean`, line 108), with
   `Audit/Overlaps.lean`'s III.26 example replaced by a note that III.26 is no longer
   provable for any two circles; then III.28 upgraded (fix `Prop30.lean`, line 88);
6. `Arcs.lean`;
7. regenerate; the records, mishnah and gaps of III.23, III.24, III.26 and III.28.

**Stage 4:** `Foot` into `DefinitionsIII.lean` (it may ride with stage 3's words);
`Foot.exists` and `Foot.unique`; III.14 and III.15 (they need only the I.20 lemmas and may
ride with stage 2); III.25's core, `complete` and `of_circle` (after `Arc.meets`).

**What the restatements break, and must change in the same step** (WORKFLOW, section 2,
asks a correction to name its consumers):
- `Audit/Overlaps.lean`: the III.24 example (lines 189–192) and the III.26 example (line
  147), as above; `docs/reports/overlaps.md`'s paragraph on III.24, III.26 and III.27.
- `Elements/Foundations/DefinitionsIII.lean`: the docstring paragraph "III.24 proves that
  the circles are equal …".
- `scripts/render.py`: `SUPERPOSITION_NOTE` ("our proof of it compares the radii
  instead"), and `FRONT_LEAN_III`'s lines for Definitions III.4–III.6.
- `mishnah/III/24.md` ("Our statement says less …", and the paragraph on equal radii,
  which becomes the alternative proof's), and the mishnah of III.23, III.26 and III.28.
- `docs/FORMALIZATION.md`, section 3: the rows for a rectilineal figure, a circumference
  and a segment.
- `docs/briefs/0004-book-III.md` (III.24's rows and the stage 3 notes),
  `docs/briefs/book-I.md` and `docs/briefs/book-II.md` (the rows for I.40, I.45, II.1 and
  II.14), and `docs/briefs/0005-astra-review.md`'s lines that this brief withdraws.
- `review/terms.toml`: the new tag, `figure-with-dissection` (not `figure-by-corners`).
- `docs/reports/gaps-book-I.md` (I.45) and `docs/reports/gaps-book-II.md` (II.14): the
  entries planned above.

## Records made stale

Each of these records is read again when its statement or Lean file changes; none is
stamped by anyone who did not review it.

- Stage 2: I.40, I.45, II.1, II.14 (companions added; scope tags change).
- Stage 3: III.23 (companion added), III.24 (restated), III.26 and III.28 (upgraded), III.27
  and III.30 (their Lean files change at the `.1` calls).
- Stage 4: III.14, III.15 (companions added), III.25 (restated).

## The checks at the end of stages 2–4

- Every companion proved and certified; every check of today's statement compiles where it
  moves.
- The `Placement` policy and the superposition check as reworded above; `[axioms]` at 87;
  the vocabulary grown only by the words listed.
- `Audit/` changed as above; `lake build Audit` green.
- Every touched record re-reviewed.

## Open questions for the owner

1. **Figures that no corner divides into triangles, and the records' scope.** The owner's
   decision 1 settles the reading of I.45 and II.14: the figure divided by the straight
   lines from one corner, as Euclid and Byrne divide it, and no claim about another
   division. Every convex figure is so divided from any corner, and so is Euclid's ABCD.
   Byrne's figure (1847, p. 46) is not convex, and both his straight lines start from its
   re-entrant corner, a corner from which the straight lines to all the other corners run
   within the figure. A figure that is not convex may need its first corner chosen, as
   Byrne chose his, and some figures (a comb of narrow teeth, say) have no such corner.
   Nothing asks the straight lines from A₀ to run within the figure: from a corner where
   they do not, the triangles overlap or reach outside it, and together they are not the
   figure, though the statements still hold of them. A figure that no corner divides is not
   taken. Hilbert proved, for his measure of area, that another division gives the same
   sum. Is the records' scope `restricted`, with the hypothesis "the figure divided by the
   straight lines from one of its corners", or `full` in the representation
   `figure-by-corners`? The recommendation is `restricted`, as FORMALIZATION, section 2,
   defines it: Euclid's "given rectilineal figure" is any, and here it is taken as one
   divided from one of its corners, a division supplied by the choice of the first corner
   and not checked (the limit, under Conventions). If the owner decides otherwise, the
   departure is recorded, and the tag's kind is `representation`. A companion for any
   division into triangles would cost little, since `Prop45.append` takes any triangle;
   the withdrawn `Prop45.sum` was a companion for any list of triangles and, like the fan,
   did not check that they divide the figure. Such a companion is not planned.

   **Answered by the owner, 18 October 2026, after Astra's answer: full.** Astra would not
   sign off "full" for the statements as they stood (the revision note at the head of this
   brief), and wrote on #51: "Accepting a **supplied genuine dissection** is defensible ...
   But the pieces must be connected geometrically to the figure". The owner then called for
   two companions each, the checked fan and any supplied division (decision 1, as revised).
   So the division is now checked, in three forms: Euclid's and Byrne's from one corner,
   with the two conditions (`Prop45.fan`, `Prop14.fan`); a figure with one boundary, its
   triangles glued edge to edge in a suitable order (`Prop45.figure`, `Prop14.general`),
   which takes the figures that no corner divides; and, after the challenge to that
   revision, any division, as triangles that lie apart (`Prop45.apart`, `Prop14.apart`,
   `Prop14.square`), so that `full` does not rest on the one-boundary reading of open
   question 2. The records' scope is `full`, by the companions together, with the tag
   `figure-with-dissection`, of kind `representation`; the conditional approval of `full`
   for these statements is Astra's second answer (18 October), which names `Prop45.apart`
   and `Prop14.square` as the decisive companions. The recommendation `restricted` and the
   tag `figure-by-corners` are withdrawn, and the companion for any division, "not planned"
   above, is staged. The owner's first call on #13 asked that a departure from
   FORMALIZATION, section 2's definition of `full` be recorded. With `Apart`, the
   statements leave out no configuration Euclid's words admit, and the supplied division is
   the convention FORMALIZATION, section 4, permits, as Astra's second answer says; so this
   brief records no departure, and the records state the convention with the tag.

2. **A figure with a hole** (new, 18 October 2026). A figure made by gluing is bounded by
   one closed line, with no hole, so a square with a square hole cut from it is not taken
   by `Prop45.figure`, though `Prop45.sum` builds a parallelogram equal to any triangles it
   is cut into, unchecked. Definition I.19 counts rectilineal figures by the straight lines
   that contain them ("trilateral … quadrilateral … multilateral"), and Euclid's figures in
   I.45 and II.14 have one boundary; Definition I.14 allows a figure "contained by any
   boundary or boundaries". The reading taken is that a rectilineal figure of I.45 has one
   boundary, stated in the tag; the alternative, a gluing rule that lets a last triangle
   close a ring round a hole, would cost a second constructor and a weaker form of
   `hmeet`. The recommendation is to keep the reading and state it, as the tag does.

   **Closed by this brief, 18 October 2026, after the challenge to the revision,** on the
   challengers' findings, not by an answer of the owner; Astra's second answer accepted the
   result, and the coordinator approved it with the statements. Both readers held that
   `full` cannot stand while a figure Euclid's words admit is left out: Definition I.14
   allows "any boundary or boundaries", Definition I.19 calls rectilineal those "contained
   by straight lines", and FORMALIZATION, section 2, calls a statement that excludes such
   configurations `restricted`; a tag of kind `representation` cannot carry an excluded
   configuration. The cost estimate above was also wrong: taking a figure with a hole needs
   no second constructor and no new predicate. Triangles that lie apart, no point inside two
   of them, say it with `InsideTriangle`, already in the foundations, and that is exactly the
   condition that makes the sum of the triangles the area of the figure they make up. So
   `Apart`, `Apart.area`, `Prop45.apart` and `Prop14.apart` are staged; `Prop45.figure` and
   `Prop14.general` follow from them by `Fitted.inside_pairwise`; `Prop14.square` takes the
   new form; and the tag's sentence "A figure with a hole is not taken" goes. The one-boundary
   reading is not needed for `full`, and `Fitted` stays as the form for a figure with one
   boundary. A figure in more than one piece is taken too, which only claims more.

## Appendix: the challenges, and what was done

Three readers challenged the staged statements and the draft of this brief: a translator,
who read each statement back into plain words against Heath, and one reader each for
stages 2 and 4 and for stage 3. Every finding that held was applied, in `Staging/` and
here. Rows marked *withdrawn* or *revised* were overtaken by the revision of decision 1.
The revision was challenged in turn, by a reader of I.45 and II.14 as revised; those
findings are the six rows from Byrne's figure to the gap entry, and all were applied, in
the wording only: no statement changed. Astra's answer of 18 October, and the owner's
call after it, overtook some rows again; they are marked *18 October*, and the rows after
the last of the six are the findings of that revision.

| Finding | Done |
|---|---|
| `Prop20.collinear_iff` declared twice, with different statements; the merged library would not build | Stage 3's form kept, as the one statement; stage 2's copy deleted; one home, `HelpersTriangles.lean` |
| III.25's core claims less than the enunciation it carries | The statement declared to be the pair, core with `Prop25.complete`, in this brief and the module doc |
| III.24's route oversold as "Euclid's route" | Module doc and remarks reworded: the application kept, the reductio replaced; passages planned as `different`, route `modified` |
| `Prop24.equalCircles` and `Prop24.equalMeasure` not declared; III.26 cannot follow Euclid without the second | Both staged with `sorry`, plain-words docstrings, companions of III.24; checked against today's type |
| `Prop23.point` and `Arc.eq_of_aligned` each called both companion and shared step | `Prop23.point` a companion of III.23, for `Prop23.lean`; `Arc.eq_of_aligned` a shared step, for `Squares.lean` |
| The dissection limit not in the brief, nor tagged | Stated under Conventions; tag planned; page note planned. *Revised:* the limit is now Euclid's and Byrne's division, tag `figure-by-corners`. *18 October:* the division is checked, in both forms; tag `figure-with-dissection`, kind `representation` |
| "Equal" segments read as congruence, unstated | Stated under Conventions; in the III.24, III.26, III.28 module docs; for their records |
| "keeping every distance" said of the whole plane | "between points of the segment" (Definitions), "between them" (Placement) |
| `Arc` cited Definition III.9 | III.6 on `Arc`, III.9 on `Arc.measure`; III.8 and III.11 where similarity is read |
| `Prop14.sum`'s docstring used other letters | "A₁A₂A₄, A₄A₂A₃ (I.45's ABD, DBC)". *Withdrawn* with `Prop14.sum`; the II.14 check's docstring keeps the letters. *18 October:* `Prop14.sum` restored for any list of triangles; the check still keeps the letters |
| `Foot` with A = B; "Definitions III.4 and III.5" read as covering distance nothing | Docstrings say the foot is then E; "extended" |
| III.28's doc said "as Euclid's does" | The departures for the greater circumferences and the semicircle case disclosed |
| No machine check that `of_circle` is today's III.25, nor for III.26 and III.28 | Three `type_of%` checks added |
| The draft: Book Zero for sums; timebox and fallback; decided questions left open; II.14's route | All revised: words to the foundations; decisions recorded; one route for `Prop14.rectangle` |
| `Prop14.rectangle`'s route unsettled, and one route makes `Prop14.sum` hollow | Decided: Euclid's second part, never citing II.14, in the docstring and here. *Revised:* the other route would now make the II.14 check circular |
| `Fitted`'s content (`hmeet`) used by no theorem | `Fitted.inside_pairwise` added and proved. *Withdrawn* with `Fitted`. *18 October:* restored with it, and `Fitted.fan` now uses the rule too |
| "The axiom lock must not change" | Reworded: `[axioms]` stays at 87; `[vocabulary]` grows, with the words listed |
| The draft did not list every staged declaration, nor homes and owners | Every declaration pasted above; the homes and owners table |
| `Fitted`'s docstring said too little of what the rule accepts | Accepted and rejected figures stated, with what is and is not proved. *Withdrawn* with `Fitted`. *18 October:* restored, with the argument for triangles listed along their shared sides, and the ring round a hole named |
| "exactly" in the checks | "checked by Lean, up to unfolding definitions" |
| The stage 4 files under `Stage2/BookIII` | Moved to `Staging/Stage4/`, with III.25 |
| `Prop14.general` left as `sorry` though it follows in a few lines | Proved from `Prop45.figure` and `Prop14.rectangle`. *18 October:* proved from `Prop14.sum`, itself proved from `Prop45.sum` and `Prop14.rectangle` |
| No statement that congruent segments have equal circumferences before III.26 | `Prop24.equalMeasure` (above) |
| `Prop24.circumference` shadowed the definition `circumference` inside the namespace `Prop24`, so a later declaration there could not name the definition by its short name | Renamed `Prop24.equalMeasure`, its certificate entry "III.24 equalMeasure" |
| `Arc.congr_side` missing | Staged and proved, with `Arc.Congruent.congr_side` |
| `#print axioms placement` can never be free of superposition | The check reworded to direct use, and the lock |
| The list of what the restatement breaks was incomplete | The consumers listed under the order of proof work |
| The draft described placement weakly and with wrong citations; no homes for new modules | `placement` pasted with its clauses; citations corrected; the table |
| `Prop23.point`'s home would put it before III.23 | Its home is `Prop23.lean`, after III.23 |
| III.24's remark did not name III.23; `hang` is not the claim | Remarks reworded; Heath's note on III.23 cited; the passage `grouped` |
| `Prop23.point`'s plan fails at a tangent | Planned through a point between A and B |
| CI never builds `Staging`; the lakefile entry lacked a comment | The comment kept from stage 2's draft; a CI step proposed to the coordinator |
| The policy covers only `placement`; `OnSideOrLine` is a half-plane only when B ≠ C | The policy covers the `Placement` namespace; the docstring says "for B ≠ C" |
| Byrne's I.45 figure (1847, p. 46) is not convex, yet was grouped with the convex figures | Said so, under the figure by its corners, I.45's cases and open question 1: both his lines start from its one re-entrant corner, from which every line to a corner runs within; cited from `references.bib` |
| "Need not be convex, so long as each piece is a triangle" is not enough: every piece can be a triangle while the lines from A₀ run outside | I.45's and II.14's cases: so long as the lines from A₀ run within it, as Byrne's do; the statement asks only that each piece be a triangle |
| "No dissection supplied as input (FORMALIZATION, section 4)": choosing the first corner supplies it, and nothing checks it | The reason given instead: the statement asks nothing of how the triangles lie, so that today's I.45 follows from it; the two conditions that would check it named. *18 October:* the two conditions are hypotheses of `Prop45.fan` and `Prop14.fan`; today's I.45 follows from `Prop45.sum` |
| Scope `full` overstates it | `restricted` recommended, with the hypothesis "the figure divided by the straight lines from one of its corners"; the tag's kind `scope`. *18 October:* the owner decided `full`, once the division is checked and any supplied division is taken; any division is taken by `Apart`, and Astra's second answer accepts `full` |
| Nothing said plainly that the lines from A₀ need not run within the figure | Said in the tag's meaning, the I.45 module doc, under the figure by its corners and in open question 1, with Hilbert's proof for his measure of area |
| The gap entry and open question 1 on credit and on `Prop45.sum` | Hilbert credited, with Gérard, F. Schur and O. Stolz as Hilbert's own note names them, in the I.45 and II.14 entries; `Prop45.sum` described as a companion for any list of triangles that, like the fan, did not check that they divide the figure |
| Astra: the staged fan admits triangles that are not a division of the figure; the pentagon (0,0), (4,0), (4,4), (2,1), (0,4) has area 10, and its triangles from the first corner, all with corners off one straight line, are 8, 2 and 4, summing to 14 | The two conditions added as hypotheses of `Prop45.fan` and `Prop14.fan`: neighbours on opposite sides of the straight line A₀Aᵢ (`hopp`, over the new word `triples`), and the angles at A₀ together less than four right angles (`hA₀`); the pentagon fails the first at its third corner |
| Astra: some figures have no corner from which a fan divides them | `Rectilineal`, `Fitted`, `Prop45.figure`, `Prop14.general` and `Prop14.square` restored, for a figure with one boundary glued edge to edge in a suitable order; *revised:* any division is taken by `Apart` (below) |
| Astra: the pieces must be connected geometrically to the figure | The gluing rule checks it: each triangle across a side of an earlier one, meeting the earlier ones only along it; the figure is the triangles together; `Fitted.fan` connects the fan to the rule, so the companions agree |
| Astra: independence from another division is needed before presenting the sum as the polygon's area, and credit cannot discharge it in Lean | `Rectilineal.area`'s docstring calls it the area of the figure with its division, not a measure of the figure alone; the step stays in the gap catalogue, crediting Hilbert, Gérard, F. Schur and O. Stolz; no statement claims it |
| Today's I.45 and II.14 ask only that ABD and DBC be triangles, and follow from neither checked companion | `Prop45.sum` restored, and `Prop14.sum` in the list form; the `type_of%` checks derive today's statements from them |
| `Fitted.two` duplicated what `Fitted.fan` says of Euclid's figure | Not restored; `Fitted.fan` for the corners D, A, B, C |
| A figure with a hole is not made by gluing | Stated in `Fitted`'s docstring and the tag; open question 2. *Revised:* taken by `Apart` (below) |

The revision of 18 October was challenged in turn by two readers of I.45 and II.14, who
built `Staging` at `fdc56e9` (37 `sorry` warnings and nothing else), ran `check_style.py`
and `check_links.py`, and found `Fitted.fan` true in the plane; both would accept `full`
once open question 2 was closed. Their findings, and what was done:

| Finding | Done |
|---|---|
| Material, both readers: `full` while a figure Euclid's words admit is left out. A square with a square hole is a given rectilineal figure (Definitions I.14, I.19), no list of its triangles is fitted, and a tag of kind `representation` cannot carry an excluded configuration; open question 2's cost estimate overstated the fix | `Apart` and `Apart.area` staged, in the form the first reader proposed, with thanks; `Prop45.apart` and `Prop14.apart` proved from `Prop45.sum` and `Prop14.sum`; `Prop45.figure` and `Prop14.general` now proved from them by `Fitted.inside_pairwise`; `Prop14.square` takes `Apart`; open question 2 closed and its cost estimate corrected; the tag's sentence on a hole removed; the limit, the vocabulary, the homes, the coverage and the cases revised |
| Editorial: the main theorems still take two unchecked triangles, which may overlap, and the brief planned no place for the record note that says so once `two-triangles` goes | The limit, under Conventions, and the I.45 and II.14 coverage now plan a representation note beside the tag in both records, naming the checked case: `Prop45.fan` (`Prop14.fan`) for the corners D, A, B, C, where the condition on neighbours is that A and C lie on opposite sides of DB; the module docs say it too |
| Editorial: `hopp` and `hA₀` carry meaning, not logic; the fan conclusions follow from `htri` by `Prop45.sum` (`Prop14.sum`), yet the certificates wait on `Fitted.fan`, the hardest stub of stage 2 | Said under I.45, II.14's proved items, the proof order, and the docstrings of `Prop45.fan` and `Prop14.fan`: the route through `Fitted.fan` was on purpose, with a fallback from the sums. *Overtaken by Astra's second answer and the coordinator's direction (below):* the fan companions now conclude that the fan fits, so the conditions do logical work, and the fallback is withdrawn |
| Editorial: the fan docstrings speak of a figure "with corners A₀, A₁, …, Aₙ in order round it" and say the triangles are fitted "into the figure", though `Fitted.fan` proves only that they fit together into one figure | The docstrings of `Fitted.fan`, `Prop45.fan` and `Prop14.fan`, the module doc of `Rectilineal.lean`, the plain words and the limit now say that the identification with the polygon by its corners is a reading, true under the two conditions, and not a Lean statement |

Astra's second answer, read-only on `b48640c` (on
[issue #13](https://github.com/jackChallis/stoicheia/issues/13)), is the challenge of the
final statements. It accepts `full` for I.45 and II.14 under the convention that the figure
comes with a checked finite dissection, with `Prop45.apart` and `Prop14.square` the
decisive companions, and found no geometric defect requiring a statement to change. Its
corrections, and what was done:

| Finding | Done |
|---|---|
| `Fitted`'s docstring and the bullet on what the gluing rule accepts: the rule appends exactly (P, Q, X), so a division listed with each later triangle sharing a side with an earlier one is fitted only if each later triangle is named so that its attached side is its first two corners; the square ABCD listed ABC, ADC is a division but not fitted | Astra's words added to both, with the square as the example, and the distinction drawn between "every figure with one boundary has a fitted division" and "every division of it is fitted" |
| "For any division at all" must no longer describe `Fitted`; `Apart` supplies the general interface | "Any division" now belongs to `Apart`, and `Fitted` is described as the form for a figure with one boundary, its triangles fitted in a suitable order: decision 1 as revised, the revision note, open question 1's answer, the limit, the tag, the plain words, the gap entry, the appendix and the docstrings of `Rectilineal.lean`, `Prop45.lean` and `Prop14.lean` |
| The fallback for a stalled `Fitted.fan` proves the fan's construction but not that the fan fits; a `redundant-hypothesis` tag cannot replace the bridge | The fallback withdrawn: the fan companions now conclude that the fan fits (below), so they cannot be proved without `Fitted.fan`; if it stalls, the fitting implication is unformalized and the fan is no longer presented as Lean-checked, under I.45, II.14's proved items and the proof order; `full` rests on the `Apart` companions |
| The revision note's quotation of #51 was not verbatim, and #51 did not approve the new statements as `full` | #51 quoted verbatim in the revision note and open question 1's answer, "as full" dropped, and the conditional approval of `full` credited to the second answer |
| The proof route for `Fitted.fan` describes the earlier triangles as filling "the angle A₁A₀Aᵢ", which cannot be a reflex sector, and misses the running sum of exactly two right angles | The invariant restated as the cumulative sector swept in the orientation the condition on neighbours fixes, with three cases: less than two right angles, exactly two, more than two |
| "Their sum then measures no single figure": the sum theorem itself constructs a single figure of that area | "Their sum need not equal the area of their union", under Conventions and in `Rectilineal.lean` |
| `Sums.lean`'s module doc and the `segments` docstring describe I.45's figure as given by its corners and divided from one of them | Both scoped to the companions for a checked fan |
| The representation note for the unchanged main theorems should call them area-sum theorems, representing Euclid's pictured division when the condition holds, and credit the general companions | The planned record note, the coverage of I.45 and II.14 and the module docs now say so, and name `Prop45.apart`, `Prop14.apart` and `Prop14.square` as what carries `full` |

Two readers for the coordinator reviewed the same revision, one against the documented
rules and one against the owner's words on #13. Their findings that held, and what was
done:

| Finding | Done |
|---|---|
| The orders for a statement wave say "write no proofs in `Staging/`", yet this brief proves companions there from stubs | The rule amended, by the coordinator's decision, in its one home, WORKFLOW, section 2, "What proofs `Staging/` may hold": derivations of one staged statement from others, and an approved prototype's proofs; a staged statement's own proof still waits for its brief's approval. The orders, kind 2, and FORMALIZATION, section 6, point to it, and the staging rule above says so |
| `Prop45.fan` and `Prop14.fan` route through the stubbed `Fitted.fan` while their conclusions follow from `htri` alone, which FORMALIZATION, section 5, treats as a review prompt | At the coordinator's direction, both now conclude, besides the parallelogram (the square), that the fan's triangles are a fitted figure, `∃ R : Rectilineal, R.pieces = …`, proved through `Fitted.fan`; the two conditions are needed for that conclusion. This statement change came after Astra's answer and only adds a conclusion |
| Decision 1 as revised, and open question 1's answer, put the gluing design in the owner's words; the owner asked for the checked fan and any supplied division | Decision 1 quotes the owner, and says that the brief stages three forms to meet it, `apart`, `figure` and `fan`, `figure` and `Fitted.fan` being the brief's choice; open question 2 is marked closed by the brief, not by the owner |
| The fan is the owner's "main one", yet the coverage paragraphs derive it last, "in particular" | The coverage of I.45 and II.14, the names and the module docs call `fan` the main companion, and `apart` the one that carries `full` |
| The owner's first call on #13 asked that a departure from FORMALIZATION, section 2, be recorded, and the brief was silent | Open question 1's answer says why none is recorded: with `Apart`, no configuration is left out, and the supplied division is the convention of section 4 |
| Lean notes carried production: "as revised on 18 October 2026", "Astra's pentagon (brief 0006, the revision of 18 October)" | Dates removed from the module docs of `Rectilineal.lean`, `Prop45.lean` and `Prop14.lean`; the pentagon described by its corners' placing, with a pointer to this brief; the fan docstrings name the hypotheses in words |
