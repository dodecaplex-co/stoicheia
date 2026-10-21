import Staging.Stage3.Definitions
import Staging.Stage3.Degenerate
import Staging.Stage3.Placement
import Staging.Stage3.Chord
import Staging.Stage3.Prop23Point
import Staging.Stage3.Aligned
import Staging.Stage3.CircumferenceAdd
import Staging.Stage3.Prop24
import Staging.Stage3.Prop26
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
their homes in `Elements/`, and its folder with them; so have stage 4b's statements of
brief 0007, III.7, III.8 and III.17 with the point of contact. The others:

* `Stage3/`: the arcs and segments, I.20's degenerate case, placement, III.23 point by
  point, III.24 restated, III.26 and III.28 upgraded, and the bridge theorems of `Arcs.lean`;
* `Stage4/`: III.14 and III.15 with the foot of the perpendicular, and III.25 restated;
* `Stage4b/`: a prototype of mixed angles for III.16 and III.31, with its proofs, which the
  coordinator approved on 18 October 2026 (`docs/reports/mixed-angles-prototype.md`);
* `Centre/`: brief 0008's statements, every circle has a centre, with III.1 kept as
  Euclid's construction and III.5 and III.6 read with crossing and contact within.
-/
