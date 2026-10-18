import Staging.Stage2.Sums
import Staging.Stage2.BookI.Prop40
import Staging.Stage2.BookI.Prop45
import Staging.Stage2.BookII.Prop01
import Staging.Stage2.BookII.Prop14
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
# Staging: statements before their proofs

The statements that a stage of brief 0005 adds or changes, each with `sorry` where its
proof is due, until it is proved and moves to `Elements/`. The rules for them are in
`docs/WORKFLOW.md`, section 2; brief 0006 names each statement's home and owner.

The folders follow brief 0005's stages:

* `Stage2/`: I.40, I.45, II.1 and II.14, with the sums and the points in order they need;
* `Stage3/`: the arcs and segments, I.20's degenerate case, placement, III.23 point by
  point, III.24 restated, III.26 and III.28 upgraded, and the bridge theorems of `Arcs.lean`;
* `Stage4/`: III.14 and III.15 with the foot of the perpendicular, and III.25 restated.
-/
