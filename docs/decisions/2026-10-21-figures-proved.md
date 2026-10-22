- **Brief 0013's staged statements are proved in `Staging/` (#116).** On 20 October 2026,
  after the owner "approved … decisions for #116, including" decision 5 of
  [brief 0013](../briefs/0013-figures.md), as the decisions page's entry of
  [20 October](../briefs/0002-decisions.md#20-october-2026) records, quoting that
  decision's request, the coordinator assigned the proofs of the
  statements staged with that brief, in place in `Staging/Figures/`, as a prototype the
  coordinator approved (the brief's decision 6; [WORKFLOW](../WORKFLOW.md), section 2). By
  21 October every one was proved, the optional diagonal route and the bridge
  `Prop45.fan_boundary` among them, with no new axiom, no statement or definition changed
  from those assigned for proof, as they stand at `2bbf597d`, and `Certificate/axioms.lock`
  unchanged. Each proof of 21 October was written by one writer and read in full by an
  independent reader who wrote none of it. The prototype proofs of 19 October were read in
  full at `b2c0580a` by a reader who wrote none of them, who approved them with minor
  findings, one of which corrected the order of two rows of the brief's ledger (B0 and B3).
  The readings of the bound, the fan's bridge, the diagonal route and the extraction are
  named in merge commits of `lean/figures-staging`; the others, the reading of the
  prototype among them, are recorded with the work, outside the repository. The reading of
  the bound asked for changes: two module notes were false, and have since been corrected,
  and the import of I.23 bears on the homes, which the brief's section 7 records; the other
  readings approved with minor findings. At `b2c0580a`, the final Lean of these proofs, `#print axioms` reports `sorryAx` for no
  staged theorem, and Postulate 5 and superposition only in `outline_bounded`, whose
  enclosing triangle uses Postulate 5 and copies an angle by I.23, its one citation of the
  *Elements*, which reaches superposition through I.4 and I.8; in `Prop45.fan_boundary`,
  superposition alone, through `Fitted.fan`, which rests on I.13; and in the three
  companions, through Euclid's I.45 and II.14 constructions. Every other staged theorem,
  `division_exists`, `area_eq` and `apart_has_outline` among them, shows neither and cites
  no proposition. The revision that lands merges main into `b2c0580a` and adds the brief's
  revision and this entry; its `Staging/Figures/` is that of `b2c0580a`. At `a68777b5`, a
  merge of main into this work, `lake build Staging` succeeds, with three warnings in
  `Staging/Figures/`, unused hypotheses the brief's section 7 records, and no `sorry` in
  `Staging/Figures/`. The checks of [WORKFLOW](../WORKFLOW.md), section 8, passed at
  `e8db9f89`, an earlier such merge: `scripts/check_acceptance.py`, run on its own, reports
  failing items there by design until promotion, and its comparison with main, the ratchet,
  is CI's gate. They are run again on the revision that lands, before it lands. Where a
  proof departs from the brief's route, the brief records it (section 8, "The routes
  taken"), and the Lean says how the proof goes. Nothing
  moves into `Elements/`, and I.45 and II.14 stay restricted (`figure-with-dissection`),
  until the owner approves promotion. The approvals asked for are listed together in the
  brief's section 10, "Progress, 21 October 2026": moving the statements and proofs into
  `Elements/`, to the homes of the brief's section 7, with the texts that call the outline
  proof pending, `docs/PROGRAM.md`'s account among them; the changes this makes to the
  foundations, which [FORMALIZATION](../FORMALIZATION.md), section 1, reserves to the
  owner: the staged definitions in `Elements/Foundations/Figures.lean`, the vocabulary they
  reach in `Certificate/axioms.lock`, with no axiom changed, and the notes of
  `Elements/Foundations/Phrases.lean` that set division and its independence aside and
  call the sum of a division "not yet a measure of the figure alone"; `outline_bounded`,
  with its citation of I.23 and its use of
  Postulate 5, moved unchanged out of `Outline.lean` to a Book I module of its own after
  I.29, so that `Outline.lean` and the files that import it, the companions aside, import
  no proposition and can go to Book Zero; the outline companions as the edition's general
  claim for I.45 and II.14; the two records' return from restricted to full, once
  reviewed, their interim `[statement]` entries going with the scope, among them the
  hypothesis that existence from an outline "is not yet proved" and the note that coverage
  and independence "remain unproved", which #116's comments say must go too; the removal of
  the two `ALLOWED_LIMITS` entries in `scripts/check_acceptance.py`, in a change to the
  check of its own, with the two rows of
  [ACCEPTANCE's table](../ACCEPTANCE.md#the-limitations-allowed), ACCEPTANCE's sentence on
  I.45 and II.14 in B4 and its paragraph after the table, and the two expected entries and
  three cases of `tests/test_acceptance_limits.py` that take I.45 and II.14 as allowed; for
  the natural-number counts of the brief's decision 3, the amendment of the sentence of
  [FORMALIZATION](../FORMALIZATION.md), section 2, "No numbers, coordinates or real numbers
  appear in a statement or a proof.", or the exception recorded; and the choices the
  brief's section 7 leaves to the approval: whether the unused hypotheses of two staged
  statements are dropped, whether twelve predicates named in lower camel case are renamed,
  which proved staged statements that no staged proof uses are kept, and whether
  `Diagonal.lean` is kept or retired. The points for the change that promotes the work, the
  code review of the whole of `Staging/Figures/` at `b2c0580a` among their sources, are in
  the brief's section 7, "Before promotion". Until promotion the staged copies hold P10 for
  I.45 and II.14, so the release gate holds, as #116 intends.
