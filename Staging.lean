import Staging.Routes.Prop08
import Staging.Routes.Prop21
import Staging.Routes.Prop26
import Staging.Routes.Prop27
import Staging.Routes.Touching
import Staging.Routes.AngleOfContact

/-!
# Staging: statements on their way to `Elements/`

The statements that a stage of brief 0005, or of a later brief, adds or changes, each with
`sorry` where its proof is due, until it moves to `Elements/`. The rules for them, and for
the few proofs this library may hold, are in `docs/WORKFLOW.md`, section 2. Brief 0006 names
the home and owner of each statement of brief 0005's stages; a later brief names those of
its own.

The folders followed the briefs' stages; the one left, `Routes/`, follows issues instead
(#125, #126, #127, #129 and #130). The statements of brief 0006's stages 2, 3 and 4,
all proved, have moved to their homes in `Elements/`, and their folders with them; so have
stage 4b's statements of brief 0007, III.7, III.8 and III.17 with the point of contact, and
the mixed-angle prototype for III.16 and III.31 (brief 0011). Brief 0008's centre
restatements have also moved home, and so has III.30's halves (brief 0006), proved on
21 October 2026 as the companion "III.30 halves". The prototype of a restricted
superposition rule (brief 0009) has its production home in
`Elements/Foundations/Superposition/`, where the rule now in the foundations is stated.
The remaining work is in `Routes/`: Euclid's own routes in Book III, proved on the
statements now in `Elements/`: III.8, III.20's special case, III.21, III.26 and III.27 by
his arguments, to replace the proofs there (those of III.20's special case, III.21 and
III.26 rest on the draft angle at the centre, and wait for its approval), and drafts for
the owner's approval of Definition III.3 read at the point, the angle at the centre of any
size with III.20 in general (`Elements.BookIII.Staging.Prop20`), and the angle of contact
after III.18. The coordinator's orders of 21 October 2026 directed these proofs here; they
are not the owner's approval of a prototype, and the files stand here as unfinished work
while an issue labelled `blocks-release` tracks their move into `Elements/`. The report is
`docs/reports/routes-book-III.md`.
-/
