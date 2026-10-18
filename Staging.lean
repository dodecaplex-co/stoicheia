import Staging.Stage3.Prop28
import Staging.Stage3.Arcs
import Staging.Stage4.Foot
import Staging.Stage4.Prop14
import Staging.Stage4.Prop15
import Staging.Stage4.Prop25

/-!
# Staging: statements on their way to `Elements/`

The statements that a stage of brief 0005, or of a later brief, adds or changes, each with
`sorry` where its proof is due, until it moves to `Elements/`. The rules for them, and for
the few proofs this library may hold, are in `docs/WORKFLOW.md`, section 2. Brief 0006 names
the home and owner of each statement of brief 0005's stages; a later brief names those of
its own.

The folders follow the briefs' stages. Stage 2's statements, all proved, have moved to
their homes in `Elements/`, and its folder with them; so have stage 3's words for arcs and
segments, its ground, placement among it, III.24 restated with its companions, and III.26
upgraded. The others:

* `Stage3/`: III.28 upgraded, and the bridge theorems of `Arcs.lean`;
* `Stage4/`: III.14 and III.15 with the foot of the perpendicular, and III.25 restated;
* `Stage4b/`: III.7 and III.8 compared on either side of the diameter, III.17 for a point
  not within the circle, and the point of contact (brief 0007); and a prototype of mixed
  angles for III.16 and III.31, with its proofs, which the coordinator approved on 18
  October 2026 (`docs/reports/mixed-angles-prototype.md`).
-/
