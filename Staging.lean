/-!
# Staging: statements on their way to `Elements/`

Nothing is staged now. This library holds the statements that a stage of brief 0005, or of
a later brief, adds or changes, each with `sorry` where its proof is due, until it moves to
`Elements/`. The rules for them, and for the few proofs this library may hold, are in
`docs/WORKFLOW.md`, section 2. A later brief stages a statement in a file of its own under
`Staging/`, which `lake build Staging` builds whether or not this root imports it, and names
its home and owner; a changed main theorem is staged as `Elements.Book<B>.Staging.PropN`
(`docs/FORMALIZATION.md`, section 6).

Everything staged so far has moved home: the statements of brief 0006's stages, of brief
0007's stage 4b, of brief 0008 and of brief 0013, the prototypes of the mixed angles (brief
0011) and of a restricted rule of superposition (brief 0009), and Euclid's routes in Book
III (#125, #126, #127, #129 and #130, moved under #332), the last of them the angle at the
centre of any size, with III.20, III.21 and III.26 by Euclid's argument. The routes report
is `docs/reports/routes-book-III.md`.
-/
