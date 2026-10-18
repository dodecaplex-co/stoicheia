import Staging.Stage2.Sums
import Staging.Stage2.Rectilineal
import Staging.Stage2.BookI.Prop40
import Staging.Stage2.BookI.Prop45
import Staging.Stage2.BookII.Prop01
import Staging.Stage2.BookII.Prop14
import Staging.Stage2.BookIII.Foot
import Staging.Stage2.BookIII.Prop14
import Staging.Stage2.BookIII.Prop15

/-!
# Staging: statements awaiting approval

Statements are settled before proofs (docs/WORKFLOW.md, section 2). Each new or changed
statement of brief 0006 is written here first, with `sorry` where its proof is due, and
reviewed in plain words. Nothing here changes `Elements/`: these files import it, and
nothing imports them. `lake build Staging` checks them. When a statement is proved, it moves
to its home in `Elements/`, and a companion joins `Certificate/Facts.lean`'s companions.

`Stage2/` holds stage 2's statements (I.40, I.45, II.1, II.14, with the sums and the
rectilineal figure they need) and stage 4's III.14 and III.15.
-/
