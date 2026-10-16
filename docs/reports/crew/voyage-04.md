# Voyage 4: the fleet finishes Book I, Propositions 33–48 (15 October 2026)

The largest voyage so far, and the last of Book I: four ships, each with a
Claude captain, two Claude first mates and four Claude bosuns, and thirty-two
OpenAI Codex sailors (`gpt-6-astra`), two on every proposition. A first mate went
ahead with the groundwork (areas and parallelograms in Book Zero, the shared
parallel steps, three statements adjusted and tested in scratch proofs, which
served the voyage and were removed once the propositions were proved; see
[first-mate-04.md](first-mate-04.md)), and two challengers tried to break it
before anyone sailed.

Each bosun gave the orders ([orders-04.md](orders-04.md)) and its first mate's
chart to two sailors, one at Codex's usual reasoning setting (a) and one at its
highest (b), checked both, and kept the proof that read more like Euclid. First
mates merged and reviewed; captains enforced the house voice.

The first mate's report was written for a fleet of Claude and Codex crews; in the
end every sailor was Codex, two to a proposition. Twelve propositions had a scratch
proof to start from (I.35–I.39, I.41–I.45, I.47, I.48); I.33, I.34, I.40 and I.46
did not. Both sailors on a proposition had the same.

## Results

| Prop | Kept | a: min | b: min | a: tokens | b: tokens | Faithful | Reads as Euclid (1–5) | Enforcer edits |
|---|---|---|---|---|---|---|---|---|
| I.33 | b | 3.0 | 5.0 | 79,645 | 105,365 | yes | 5 | 6 |
| I.34 | b | 3.1 | 5.2 | 78,245 | 94,450 | yes | 4 | 5 |
| I.35 | b | 4.4 | 8.0 | 81,991 | 132,130 | yes | 4 | 8 |
| I.36 | b | 3.3 | 5.1 | 78,353 | 98,390 | yes | 5 | 5 |
| I.37 | a | 3.6 | 4.9 | 77,270 | 103,021 | yes | 4 | 5 |
| I.38 | b | 3.4 | 5.1 | 76,321 | 93,851 | yes | 4 | 5 |
| I.39 | b | 3.3 | 5.3 | 75,319 | 88,606 | yes | 4 | 7 |
| I.40 | b | 3.8 | 5.7 | 97,996 | 94,634 | yes | 5 | 6 |
| I.41 | b | 2.6 | 6.9 | 76,330 | 106,824 | yes | 5 | 6 |
| I.42 | b | 3.8 | 6.2 | 81,583 | 127,608 | yes | 4 | 6 |
| I.43 | b | 3.4 | 5.3 | 74,625 | 92,895 | yes | 5 | 5 |
| I.44 | b | 4.9 | 7.9 | 92,281 | 102,971 | yes | 4 | 8 |
| I.45 | b | 3.2 | 5.0 | 78,774 | 92,218 | yes | 5 | 5 |
| I.46 | b | 2.9 | 4.5 | 80,755 | 106,631 | yes | 5 | 5 |
| I.47 | b | 5.4 | 7.7 | 100,454 | 136,028 | yes | 4 | 5 |
| I.48 | b | 3.6 | 6.0 | 64,678 | 100,240 | yes | 5 | 5 |

## What it showed

- **All thirty-two sailors proved their proposition**, first time, with no
  retries and no usage limits reached. Best of two was insurance that wasn't
  needed for correctness, but it paid for itself in readability.
- **The highest reasoning setting was kept fifteen times out of sixteen.** It took
  about two minutes longer and about 30 per cent more tokens, and the bosuns judged
  its Lean to sit more closely under Euclid's sentences.
- **The voice still needs its keeper.** Captains made five to eight edits per
  page, much as the enforcer did for Codex pages in voyage 3; nothing in the
  mathematics changed.
- **A launch lesson.** The first launch was stopped: a short message from the
  captain's conversation, meant for something else, was read by several agents
  as an order to stand down. Every agent's orders now say what such a message
  means.

With these sixteen, Book I is complete: forty-eight propositions, every one
proved along Euclid's route, with the parallel postulate entering at I.29 and
not before.

**Axioms and gaps.** No axiom added; gaps: see [gaps-book-I.md](../gaps-book-I.md).
