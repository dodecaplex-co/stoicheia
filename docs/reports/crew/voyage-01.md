# Voyage 1: Book I, Propositions 4–8 (15 October 2026)

The shakedown voyage of the crew described in the [plan](../../briefs/0001-plan.md):
one sailor per proposition, each in its own git worktree, then a bosun who merged
the branches, built everything and reviewed each proof for faithfulness. Run with
Claude Code's Workflow tool, six agents in all.

| Prop | Result | Helper lemmas | New tacit rules asked for |
|---|---|---|---|
| I.4 | proved | `coincide`, `on_ray` | none |
| I.5 | proved | `between_inner`, `chance_point`, `beyond`, `triangle`, `angle_along`, `angle_add` | none |
| I.6 | proved | `figure`, `rotate`, `swap`, `angle`, `less` | none |
| I.7 | proved | `sameSideOf_swap`, `sameSideOf_symm`, `produce`, `triangle`, `cross`, `cases`, `figure`, `within` | none |
| I.8 | proved | `triangle`, `coincide`, `sameSide` | none |

**Time.** About 14 minutes for the five sailors working at once, and 9 minutes for
the bosun.

**The bosun's review.** All five proofs were judged faithful: statements
unchanged, Euclid's citations used where he uses them, superposition only in I.4
and I.8, no new axioms. Every quotation of Heath in the mishnah was checked
against the scan, and claims about Beeson, Narboux and Wiedijk were checked against
their paper. Four small wording fixes were made in the mishnah for I.4 and I.8.

**Lessons for the next voyage.**
- No sailor needed a tacit rule beyond System E. The foundations held.
- Helper lemmas repeat across files (same-ray angles, "is a triangle", same side of
  a named line). The common ones should move to Book Zero (`Elements/Figure/`)
  before the next voyage, so later sailors can cite them.
- I.6 moves ten of Euclid's sentences into a sub-proof, which re-indents their
  `--` lines. The wording is unchanged and the check compares words, not
  indentation; CONTRIBUTING now says so.
- The captain must keep the session's working directory inside the repository
  while a worktree voyage runs. Leaving it once stopped the bosun from starting.

The gaps the sailors found are collected in [gaps-book-I.md](../gaps-book-I.md).
