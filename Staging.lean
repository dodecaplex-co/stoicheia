import Staging.Routes.Prop21
import Staging.Routes.Prop26

/-!
# Staging: statements on their way to `Elements/`

The statements that a stage of brief 0005, or of a later brief, adds or changes, each with
`sorry` where its proof is due, until it moves to `Elements/`. The rules for them, and for
the few proofs this library may hold, are in `docs/WORKFLOW.md`, section 2. Brief 0006 names
the home and owner of each statement of brief 0005's stages; a later brief names those of
its own.

The folders followed the briefs' stages; the one left, `Routes/`, follows issues instead,
and now holds #129's files alone. The statements of brief 0006's stages 2, 3 and 4,
all proved, have moved to their homes in `Elements/`, and their folders with them; so have
stage 4b's statements of brief 0007, III.7, III.8 and III.17 with the point of contact, and
the mixed-angle prototype for III.16 and III.31 (brief 0011). Brief 0008's centre
restatements have also moved home, and so has III.30's halves (brief 0006), proved on
21 October 2026 as the companion "III.30 halves". So have brief 0013's rectilineal figures
given by their outlines, all proved, and their folder `Figures/` with them: the words to
`Elements/Foundations/Figures.lean`, the facts to Book Zero (`Elements/Figure/`),
`outline_bounded` to Book I after I.29, and the companions to I.45 and II.14. The prototype
of a restricted superposition rule (brief 0009) has its production home in
`Elements/Foundations/Superposition/`, where the rule now in the foundations is stated.
Euclid's own routes for III.8 and III.27 (#125 and #127), proved on the statements in
`Elements/`, have moved home too: on 22 October 2026, under #332, each proof went into its
proposition's file, and its staged copy was deleted. So has the angle of contact after
III.18 (#130): on 25 October 2026 the owner approved the drafts of #126, #129 and #130 as
they stood, and under #332 its seven theorems went into `Elements/BookIII/Prop18.lean`,
after III.18's proof, and its staged file was deleted. So has Definition III.3 read at the
point of contact (#126), approved that day as well: under #332 its four definitions went
into `Elements/Foundations/DefinitionsIII.lean` and its theorems into
`Elements/BookIII/Prop13.lean`, after III.13's proof, and its staged file was deleted. The
remaining work in `Routes/` is #129's: Euclid's own routes in Book III, proved on the
statements now in `Elements/`: III.20's special case, III.21 and III.26 by his arguments, to
replace the proofs there (they rest on the angle at the centre of any size), and the draft
the owner approved with those of #126 and #130, which waits for its move into `Elements/`:
the angle at the centre of any size with III.20 in general (`Elements.BookIII.Staging.Prop20`).
The coordinator's orders of 21 October 2026 directed these proofs here; those orders were
not themselves the owner's approval, which came for the drafts on 25 October 2026, and the
files stand here as unfinished work while an
issue labelled `blocks-release` tracks their move into `Elements/`. The report is
`docs/reports/routes-book-III.md`.
-/
