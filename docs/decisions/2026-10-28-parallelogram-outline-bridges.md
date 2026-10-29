<!-- entry: id=parallelogram-outline-bridges cards=633 line="The Jev generator supplies Parallelogram.convexOutline and Parallelogram.outline_area as bridges in the rows that measure a parallelogram by quadArea." -->
- **The Jev generator supplies the parallelogram's outline with its area (tooling,
  [#633](https://github.com/dodecaplex-co/stoicheia/issues/633)).** The coordinator, 28
  October 2026, 23:12: "Name #622's two theorems (Parallelogram.convexOutline,
  Parallelogram.outline_area) in scripts/audit/jev_questions.py's AREA_BRIDGES with its
  test, and in docs/FORMALIZATION.md's representation catalogue". #622 proved that a
  parallelogram's corners are a convex outline (`Parallelogram.convexOutline`) and that
  the area of that outline is the parallelogram's `quadArea` (`Parallelogram.outline_area`),
  in `Elements/Figure/Divisions.lean`. The rows of I.34 to I.38 and I.41 to I.48, which
  measure a parallelogram by `quadArea`, now supply both among their bridges, so that a
  reader of a row finds the tie between the measure and the figure. The generator supplies
  the two where the evidence it reads declares them, so the evidence commit of the audit of
  Books I and II, of 19 October, which its tests read again, is read as before.

  `outline_area` ties `quadArea` to the figure's area by itself, so P13's two plants that
  broke only `Parallelogram.quadArea_rotate` would no longer be faults. Each now breaks
  `outline_area` the same way: at I.43 its conclusion is made
  `quadArea A B C D = quadArea A B C D`, at I.36 it is given the premise (hAC : A = C)
  after the binders of its own corners, which `quadArea_rotate` takes from its file's
  variables. Each plant keeps its base, its kind and its expected answer.

  This entry approves the change to `scripts/audit/jev_questions.py`: the two bridges, where
  the evidence declares them, a comment on the list, and the two plants with their
  descriptions.
  This entry approves the change to `tests/test_jev_questions.py`: one new case, which
  checks the bundle, the rows and both plants.
  The order's other half, the two theorems named in `docs/FORMALIZATION.md`'s catalogue, is
  a change of its own, since other changes in flight write the rows beside it.
