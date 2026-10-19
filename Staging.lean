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

The folders follow the briefs' stages. The statements of stages 2 and 3, all proved, have
moved to their homes in `Elements/`, and their folders with them, save stage 3's meeting fact
for an arc, which rests on III.2 and waits beside III.25, the one proof that uses it. So have
stage 4b's statements of brief 0007, III.7, III.8 and III.17 with the point of contact. The
others:

* `Stage4/`: III.14 and III.15 with the foot of the perpendicular, and III.25 restated, with
  the meeting fact for an arc (`Prop25.meets`);
* `Stage4b/`: a prototype of mixed angles for III.16 and III.31, with its proofs, which the
  coordinator approved on 18 October 2026 (`docs/reports/mixed-angles-prototype.md`);
* `Centre/`: brief 0008's statements, every circle has a centre, with III.1 kept as
  Euclid's construction and III.5 and III.6 read with crossing and contact within;
* `Superposition/`: the prototype of a restricted superposition rule (brief 0009), carried
  as a hypothesis, with its proofs, which the coordinator approved on 18 October 2026.
-/
