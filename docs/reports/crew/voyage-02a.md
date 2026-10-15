# Voyage 2a: Book I, Propositions 9–16 (15 October 2026)

The first voyage with the full ranks. The first mate went ahead: it moved the
facts voyage 1 kept re-proving into Book Zero and reviewed the statements of
I.9–I.24, adjusting I.1, I.9 and I.22 (see [first-mate-02.md](first-mate-02.md)).
Then eight sailors, each in its own worktree, and a bosun. Nine agents in the
voyage itself.

| Prop | Result | Helper lemmas in its own file |
|---|---|---|
| I.9 | proved | `chance_point`, `opposite`, `not_on_arm`, `crossing`, `side` |
| I.10 | proved | none: Book Zero and I.9's statement were enough |
| I.11 | proved | `produced`, `either_ray` |
| I.12 | proved | `onRay_cases` |
| I.13 | proved | `cases`, `within`, `angle_add` |
| I.14 | proved | `opposite`, `sameSide`, `straight` |
| I.15 | proved | `figure`, plus `porism` |
| I.16 | proved | `within`, `part`, `beyond` |

**Time.** About 27 minutes for the eight sailors, then the bosun.

**The bosun's review.** All eight faithful: statements byte-identical to main,
Euclid's citations in Euclid's order, no superposition, nothing new assumed.
Every Heath quotation was checked against the scan, and one page reference was
corrected (I.10).

**Lessons.**
- I.10 needed no helper lemmas at all: the first mate's Book Zero and the
  strengthened I.9 carried it. That is the pattern to aim for.
- Duplicates appeared again, and should be hoisted: "every point of a line
  lies on one of the two rays from a point" (`Prop11.either_ray`,
  `Prop12.onRay_cases`); "produce a line far enough to cut from"
  (`Prop11.produced`, `Prop16.beyond`); "a line within an angle cuts it in two
  parts, each something" (`Prop13.angle_add`, `Prop16.part`); and the
  sides-of-a-line facts in I.9 and I.14.
- No sailor needed a new tacit rule. System E has covered all of I.1–I.16.
