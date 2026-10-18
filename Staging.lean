import Staging.Stage2.Sums
import Staging.Stage2.Rectilineal
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
# Staging: statements awaiting approval

Statements are settled before proofs (docs/WORKFLOW.md, section 2). Each new or changed
statement of brief 0006 is written here first, with `sorry` where its proof is due, and
reviewed in plain words. Nothing here changes `Elements/`: these files import it, and
nothing imports them. `lake build Staging` checks them. When a statement is proved, it moves
to its home in `Elements/` (brief 0006 names each one's file and owner), a companion joins
`Certificate/Facts.lean`'s companions, and the records it touches are read again.

The folders follow brief 0005's stages:

* `Stage2/`: I.40, I.45, II.1 and II.14, with the sums and the rectilineal figure they need;
* `Stage3/`: the arcs and segments, I.20's degenerate case, placement, III.23 point by
  point, III.24 restated, III.26 and III.28 upgraded, and the bridge theorems of `Arcs.lean`;
* `Stage4/`: III.14 and III.15 with the foot of the perpendicular, and III.25 restated.
-/
