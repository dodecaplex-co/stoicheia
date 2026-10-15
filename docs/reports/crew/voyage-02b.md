# Voyage 2b: Book I, Propositions 17–24 (15 October 2026)

The second half of the second voyage. The first mate had already read the
statements of I.17–I.24 against Heath and against every later proposition that
leans on them, and had changed I.22 so that I.23 could use it as Euclid does (see
[first-mate-02.md](first-mate-02.md)). Then eight sailors, each in its own
worktree, and a bosun.

| Prop | Result | Helper lemmas in its own file, as the sailors left them |
|---|---|---|
| I.17 | proved | none: Book Zero said everything Euclid reads off the figure |
| I.18 | proved | `part` |
| I.19 | proved | none |
| I.20 | proved | `produced`, `part` |
| I.21 | proved | `through` |
| I.22 | proved | `ne_zero`, `lt_of_add_lt`, `room`, `meet` |
| I.23 | proved | none |
| I.24 | proved | `made_equal`, `side`, `within`, `cases`, `part`, `less` |

**Time.** About 26 minutes for the eight sailors, then about ten for the bosun.

**The bosun's review.** The eight branches merged in order with no conflicts, and
each had touched only its own proof, figure and mishnah. All eight are faithful:
statements unchanged from main, Euclid's citations in Euclid's order, no new
axiom, superposition only through I.4 and I.8, and nothing resting on Postulate 5.
Four small fixes to the mishnah:
- I.18: Porphyry's "Now the angle ABC is greater…" is on p. 284 alone.
- I.21: `crossbar` is described as a theorem of Book Zero.
- I.23: `angle_eq_of_onRay` is Book Zero's, resting on System E's Diagram-angle 4.
- I.24: the bisector proof still has a case of its own, F on EG, where E, H and F
  lie on one straight line.

**Since then.** Before the inspection, the Lean bosun moved most of these helpers
into Book Zero, together with their older cousins from voyage 2a:
- `Prop20.produced` is `produce_longer` (as are `Prop11.produced` and
  `Prop16.beyond`), and `Prop22.room` now cites it after its I.2 step.
- `Prop18.part` and `Prop20.part` are gone: I.18 and I.20 cite
  `angle_add_of_between` and `Triangle.angle_pos`, and keep Common Notion 5 in the
  proof, where Euclid's step is. `Prop24.part` is `angle_lt_of_between`.
- `Prop22.lt_of_add_lt` and `Prop24.less` were one law of magnitudes, now
  `Magnitude.lt_of_add_lt_add_right` and `Magnitude.lt_of_add_lt_add_left`.
- `Prop24.made_equal` is `OnRay.exists_len_eq`, and `Prop24.side` is
  `SameSideOf.of_onRay`.
- Producing the sides of I.5 when only its angles at the base are wanted is
  `Prop5.base`, in `Elements/BookI/Helpers.lean`, since it cites I.5.

What stays home: `Prop21.through`, `Prop22.ne_zero`, `Prop22.room`, `Prop22.meet`,
`Prop24.within` and `Prop24.cases`.

**Lessons.**
- The duplicates voyage 2a asked us to hoist came back, because the hoisting had
  not yet happened when 2b sailed. "Produce far enough to cut from" appeared again
  as `Prop20.produced` and `Prop22.room`, beside `Prop11.produced` and
  `Prop16.beyond`; "a line within an angle" again as `Prop18.part` and
  `Prop20.part`, beside `Prop13.angle_add` and `Prop16.part`; and two sailors each
  wrote the same cancellation law. Hoisting belongs between voyages, before the
  next sailors set out.
- No sailor needed a new tacit rule. `Elements/Foundations/` was untouched from the
  first commit to the end of the voyage, and System E has now carried all of
  I.1–I.24.
- Several proofs cite a proposition Euclid gives no bracket for: I.18 cites I.5,
  I.20 cites I.3, I.22 cites I.2, I.23 cites I.20, and I.24 cites I.21. Each mishnah
  says why.
- Five sailors (I.19, I.20, I.21, I.23 and I.24) finished proofs whose cited
  propositions were still sketched in their own worktrees, and all five came out
  proved once merged. A proof needs only
  the statements it cites, and the plan to prove a book in any order held up.

The gaps the sailors found are collected in [gaps-book-I.md](../gaps-book-I.md).
