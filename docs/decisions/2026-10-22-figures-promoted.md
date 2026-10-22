- **Brief 0013's figures are promoted into the edition, with I.45 and II.14 full (#116).**
  On 22 October 2026 the owner wrote, of the eight approvals brief 0013 asks for, "as
  propose 1-6,8 as is. 7 with amendment." The coordinator's record of those words is
  [#116's comment of that day](https://github.com/jackChallis/stoicheia/issues/116#issuecomment-6342080363),
  which reads the amendment of approval 7 as one to the sentence of FORMALIZATION, section
  2, that keeps numbers out of statements and proofs, so that it allows counts of a
  figure's corners, since a count is part of what "a figure of n sides" means, with no
  separate exception recorded. This entry claims nothing beyond the owner's words and that
  record of them. The eight approvals are listed in [brief 0013](../briefs/0013-figures.md), section
  10, "Progress, 21 October 2026"; what was done under them, and where each piece now
  stands, is in the same section, under "Promotion, 22 October 2026".

  This entry approves the new file `Elements/Foundations/Figures.lean`, which holds the
  foundations' definitions of brief 0013: convex outlines and their fans, closed lines of
  sides and their rays, outlines with their boundary, inside and region, the cells, and a
  division with the area of an outline.

  This entry approves the change to `Elements/Foundations/Phrases.lean`, whose notes alone
  are rewritten, so that they no longer set aside the division of a figure and the
  independence of its area; not one line of its Lean differs.

  This entry approves the change to `Certificate/axioms.lock`, whose vocabulary gains the
  twenty words that the statements of the three outline companions reach, named as the lock
  names them: `Figures.CompatibleLoops`, `Figures.Covers`, `Figures.Divides`,
  `Figures.GoodRay`, `Figures.LoopBoundary`, `Figures.LoopInside`, `Figures.LoopRegion`,
  `Figures.Outline` with its constructor `Figures.Outline.mk` and its field
  `Figures.Outline.loops`, `Figures.Outline.Boundary`, `Figures.Outline.Inside`,
  `Figures.Outline.Region`, `Figures.Outline.area`, `Figures.Outline.depth`,
  `Figures.RayCrosses`, `Figures.SimpleLoop`, `Figures.crossingCount`, and `Figures.sides`
  with `Figures.sides.match_1`, the auxiliary Lean declares for it. So the vocabulary grows
  from 238 words to 258, and no axiom is added, removed or restated. The lock's header
  comment now says that a change to it is recorded in a decision entry of its own.

  This entry approves the change to `Certificate/FIELDS.md`, where `scripts/render.py`
  fills the vocabulary's count with the new number, 258, and nothing else changes.

  This entry approves the renewed hash in `tests/model/lock.sha256`, with its dated note.
  This entry approves the renewed hash in `model/lock.sha256`, with its dated note. Each
  takes the lock's new hash, since the twenty new words are reached by the companions alone
  and no law of the model changes.

  This entry approves the change to `review/terms.toml`, where the meaning of
  `figure-with-dissection` now describes the older companions that take a figure with its
  division, and no longer says that a division's existence, or its independence, is open.

  This entry approves the changed statement of `convex_diagonal_separates`, which loses its
  hypotheses that both chains have a corner, since its conclusion ranges over the corners
  of the two chains and never needed them.

  This entry approves the changed statement of `outline_cells_cover`, which loses its
  hypothesis that the insides of the cells lie apart, since its proof never used it; its
  two users, `simple_triangulation` and `division_exists`, no longer pass it.

  This entry approves the new names of the twelve predicates that brief 0013 staged in
  lower camel case, now in the UpperCamelCase that FORMALIZATION, section 2, asks of a
  predicate: `LoopInside`, `LoopBoundary`, `LoopRegion`, `Outline.Inside`,
  `Outline.Region`, `Outline.Boundary`, `CellCore`, `CellRegion`, `ConvexCell.Core`,
  `ConvexCell.Region`, `Extract.Cls` and `Extract.TCls`.

  This entry approves the move of the helper definitions `Outline.corners`, staged as
  `CoverFacts.corners`, and `OnChain`, staged as `Diag.OnChain`, into the foundations.

  This entry approves `Prop45.outline`, registered as "I.45 outline" in
  `Elements/Companions.lean`. This entry approves `Prop14.outline`, registered as "II.14
  outline". This entry approves `Prop14.outline_side`, registered as "II.14 outline_side".
  The three are the edition's general statements of I.45 and II.14 for a figure given by
  its outline alone.

  This entry approves the return of `review/I/45.toml` to scope `full` through
  `Prop45.outline`. This entry approves the return of `review/II/14.toml` to scope `full`
  through `Prop14.outline` and `Prop14.outline_side`. Both lose the interim entries of 20
  October, the tag `figure-with-dissection` staying on both for their older companions
  alone, and an independent reader reads and stamps both.

  The amendment as first read, counts of a figure's corners alone, would have been false of
  the promoted Lean, whose definition of a figure also counts the sides a ray crosses
  (`crossingCount`), the contours round a point (`Outline.depth`), the tiles of a division
  and rotation steps. Asked to choose between a wider sentence and another representation,
  the owner wrote on 22 October 2026, about 10:00: "whatever's reasonable and in spirit with
  Euclid. I don't think we need all this, but sure whatever." Under that delegation the
  coordinator chose the wider wording, as
  [#116's comment of that day headed "Item 7, settled"](https://github.com/jackChallis/stoicheia/issues/116)
  records: counts of a figure's corners and of what they make, disclosed as part of how a
  figure is defined, not as Euclid's argument.

  This entry approves the amendment of `docs/FORMALIZATION.md`, section 2: lengths, angles
  and areas stay magnitudes, no coordinates or real numbers appear in a statement or a
  proof, and counts of a figure's corners, and of what they make, may appear.
