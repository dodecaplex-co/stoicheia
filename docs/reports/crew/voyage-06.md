# Voyage 6: Book III, Propositions 1–19 (16 October 2026)

The first of two fleets on the book of the circle. A first mate went ahead with the
groundwork ([first-mate-III.md](first-mate-III.md),
[0004-book-III.md](../../briefs/0004-book-III.md)). Heath's Book III was merged from four
transcribers' branches, and the scripts and the certificate were taught a third book.
Book III's words were defined in Lean, not assumed: equal circles, a straight line
touching a circle, circles touching one another, and the circumferences Euclid compares,
each measured by twice the angle standing on it at the circumference. Book III's ground was
proved beneath them (the squares on equal straight lines, the perpendicular from the
centre, the circumferences), and III.1–III.37 were stated in Heath's letters and tested
in scratch, eighteen of them in full; the scratch proofs are committed, not built, in
[scratch-III](scratch-III). Twenty-six challenges to that work were answered before
anyone sailed. Artists drew the at-a-glance figures in Byrne's colours.

Then four ships: four Claude captains, eleven first mates and nineteen bosuns, with
thirty-eight OpenAI Codex sailors (`gpt-6-astra`), two on every proposition, one at
Codex's usual reasoning setting (a) and one at its highest (b). Each first mate charted
Euclid's route through its one or two propositions for the sailors, and afterwards merged
and reviewed what its bosuns kept; each bosun ran its two sailors and kept the proof that
read more like Euclid. The orders are in [orders-III.md](orders-III.md). Every sailor's
prompt also carried the common voice guide, written the same day for Books I and II
([voice-01.md](voice-01.md), now [STYLE.md](../../STYLE.md) §1–2), and every captain kept
the pages to it, so Book III was written in that voice from the start. Every agent's
orders began with a note on what the user's latest message meant, so no one stood down.

## Results

| Prop | Kept | a: min | b: min | a: tokens | b: tokens | Faithful | Reads as Euclid (1–5) | Captain's edits |
|---|---|---|---|---|---|---|---|---|
| III.1 | b | 2.8 | 5.2 | 122,022 | 141,739 | yes | 4 | 5 |
| III.2 | b | 3.95 | 5.02 | 112,454 | 126,975 | yes | 4 | 5 |
| III.3 | b | 2.9 | 4.9 | 111,937 | 144,845 | yes | 5 | 4 |
| III.4 | b | 2.4 | 5.9 | 110,708 | 124,579 | yes | 4 | 4 |
| III.5 | b | 3.2 | 4.5 | 115,000 | 117,057 | yes | 4 | 4 |
| III.6 | b | 2.5 | 3.9 | 98,622 | 142,731 | yes | 4 | 5 |
| III.7 | b | 3.2 | 4.5 | 111,784 | 134,077 | yes | 4 | 5 |
| III.8 | b | 4.9 | 7.7 | 129,711 | 166,703 | yes | 4 | 5 |
| III.9 | b | 3.8 | 4.8 | 104,765 | 132,142 | yes | 4 | 6 |
| III.10 | b | 3.15 | 4.55 | 136,630 | 148,062 | yes | 4 | 4 |
| III.11 | b | 3.7 | 5.0 | 114,831 | 128,742 | yes | 4 | 7 |
| III.12 | a | 4.2 | 6.4 | 135,791 | 161,446 | yes | 4 | 8 |
| III.13 | a | 3.3 | 5.2 | 114,350 | 132,803 | yes | 4 | 7 |
| III.14 | b | 3.7 | 4.7 | 107,703 | 127,754 | yes | 4 | 6 |
| III.15 | b | 3.7 | 5.8 | 114,965 | 156,648 | yes | 4 | 8 |
| III.16 | b | 4.1 | 8.1 | 141,888 | 179,385 | yes | 4 | 7 |
| III.17 | b | 3.2 | 4.9 | 99,320 | 139,739 | yes | 4 | 5 |
| III.18 | b | 3.0 | 5.2 | 111,450 | 126,707 | yes | 5 | 6 |
| III.19 | b | 2.1 | 4.1 | 101,222 | 130,724 | yes | 4 | 4 |

## What it showed

- **All thirty-eight sailors proved their proposition**, first time, with no retries.
- **The highest reasoning setting was kept seventeen times out of nineteen.** Sailor a's
  proof was kept for III.12 and III.13, where its Lean followed Euclid's words a little
  more closely, and for III.12 its figure set each letter by its point. Sailor b took
  about two minutes longer (5.3 minutes on average,
  against 3.4) and about a fifth more tokens.
- **Best of two was often best of both.** Four bosuns kept one sailor's proof and took a
  piece of the other's: the figure for III.8, the reading line for III.9 and III.11, the
  mishnah for III.18.
- **Postulate 5 stays out, but for the squares.** Seventeen of the nineteen rest on no
  Postulate 5. III.14 does, because it compares squares through I.46 and I.47, and III.15
  through III.14. No proposition uses superposition directly; it comes in through I.4 and
  I.8, and III.5 and III.6, which cite no proposition, are free of it.
- **The captains still keep the voice.** Every sailor had the guide, and the captains
  still made four to eight edits a page, 105 in all, in the mishnah, the captions, the
  reading and the Lean's remarks; nothing in the mathematics changed.
- **Minutes, not hours.** No sailor needed more than 8.1 minutes, and the whole fleet,
  from the first chart to the last captain, sailed in a little over an hour. The second
  fleet ([voyage 7](voyage-07.md)) set out while this one's captains were still at work.

With these nineteen, III.1–III.19 are proved, and they reached main the same afternoon.

**Axioms and gaps.** No axiom added; gaps: see [gaps-book-III.md](../gaps-book-III.md),
written after the voyage.
