# Voyage 3: Book I, Propositions 25–32, two crews (15 October 2026)

The stretch where the parallel postulate enters, sailed by two crews at once:
Crew A, four Claude sailors, and Crew B, four OpenAI Codex sailors
(`gpt-6-astra`), run by a Claude "Codex bosun" who checked and committed their
work (Codex's sandbox cannot write to the repository's `.git`). Both crews
followed the same orders, word for word ([orders-03.md](orders-03.md)). One
first mate went ahead ([first-mate-03.md](first-mate-03.md)): no statement
needed changing, and Book Zero gained a file of facts about parallels. One bosun
and one enforcer reviewed all eight, writing their verdicts before looking at
which crew had written what.

## The comparison

| Prop | Crew | Proved | Minutes | Bosun: faithful | Bosun: reads as Euclid (1–5) | Bosun fixes | Enforcer: checks failed | Enforcer: edits |
|---|---|---|---|---|---|---|---|---|
| I.25 | A, Claude | yes | 6.1 | yes | 5 | 0 | 1 | 3 |
| I.26 | B, Codex | yes | 3.8 | yes | 4 | 2 | 2 | 4 |
| I.27 | A, Claude | yes | 12.4 | yes | 5 | 0 | 1 | 1 |
| I.28 | B, Codex | yes | 3.8 | yes | 4 | 2 | 2 | 6 |
| I.29 | A, Claude | yes | 11.8 | yes | 5 | 0 | 0 | 0 |
| I.30 | B, Codex | yes | 4.8 | yes | 4 | 1 | 2 | 5 |
| I.31 | A, Claude | yes | 6.8 | yes | 5 | 0 | 0 | 0 |
| I.32 | B, Codex | yes | 3.8 | yes | 5 | 0 | 2 | 5 |

Codex used about 94,000–112,000 tokens per proposition, with no retries and no
repairs by its bosun. The Codex worktrees were built before the sailors started,
while each Claude sailor merged and built its own, so the minutes favour Crew B a
little.

## What it showed

- **Both crews prove.** All eight proofs were complete, correct and faithful to
  Euclid's route on the first attempt. Postulate 5 appears exactly where Euclid
  puts it: I.29 uses it directly, I.30 and I.32 through I.29, and nothing before.
- **Codex is about twice as fast.**
- **Claude's prose needed less work.** The enforcer found Crew A's pages already
  in the house voice. Crew B's came back in "a flatter, defensive register with
  modern words" ("segment", "coincide") and one mishnah claim that the merge made
  false. The bosun and enforcer put all of it right, and the eight pages now read
  as one book.
- **The enforcer earns its place.** With it, a mixed crew keeps one voice. For the
  next voyage the orders will name the commonest drift outright: Euclid's words
  for his things, no defensive asides, and certificate claims checked after the
  merge.

## For the next voyage

The first mate's look-ahead: I.37–I.46 each need "a straight line meeting one of
two parallels meets the other", which rests on Postulate 5, so it should be a
shared lemma citing I.29 or I.30, in `Elements/BookI/Helpers.lean`, before
sailing. (It went instead into a file of its own,
`Elements/BookI/HelpersParallels.lean`, as `Prop30.meet`, since `Helpers.lean` is
imported by I.7; see [first-mate-04.md](first-mate-04.md).)

**Axioms and gaps.** No axiom added; gaps: see [gaps-book-I.md](../gaps-book-I.md).
