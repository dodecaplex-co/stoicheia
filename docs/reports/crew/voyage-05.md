# Voyage 5: Book II, the whole book (16 October 2026)

The second fleet, and the first voyage on a new book. A first mate went ahead
with the groundwork ([first-mate-II.md](first-mate-II.md),
[0003-book-II.md](../../briefs/0003-book-II.md)): Heath's Book II transcribed from
the same 1908 scan, the scripts taught about more than one book, "the rectangle
contained by AB, BC" and "the square on AB" defined as areas, with every drawn
rectangle proved equal to the rectangle contained by its sides, and II.1–II.14
stated in Heath's letters and tested in scratch proofs (II.2, II.4, II.12, II.13 and
II.14 in full, II.5's case split, and the first steps of the rest), which served the
voyage and were removed once the propositions were proved. Two challengers found
nothing to change in the statements. Artists drew the colour figures in Byrne's manner, each identity as
rectangles and squares fitted together.

Then four ships: four Claude captains, eight first mates and fourteen bosuns, with
twenty-eight OpenAI Codex sailors (`gpt-6-astra`), two on every proposition, one at
Codex's usual reasoning setting (a) and one at its highest (b). The orders are in
[orders-II.md](orders-II.md). Every agent's orders began with a note on what the
user's latest message meant, so no one stood down.

## Results

| Prop | Kept | a: min | b: min | a: tokens | b: tokens | Faithful | Reads as Euclid (1–5) | Captain's edits |
|---|---|---|---|---|---|---|---|---|
| II.1 | b | 3.9 | 6.6 | 83,075 | 114,761 | yes | 4 | 5 |
| II.2 | b | 3.5 | 5.4 | 98,275 | 109,591 | yes | 5 | 5 |
| II.3 | b | 3.1 | 5.1 | 105,035 | 116,335 | yes | 4 | 5 |
| II.4 | b | 3.8 | 5.7 | 96,345 | 119,541 | yes | 4 | 5 |
| II.5 | b | 3.2 | 5.6 | 114,848 | 117,013 | yes | 4 | 5 |
| II.6 | b | 4.2 | 5.1 | 111,983 | 114,764 | yes | 5 | 4 |
| II.7 | b | 3.7 | 7.1 | 98,756 | 129,396 | yes | 4 | 5 |
| II.8 | b | 8.0 | 9.9 | 124,999 | 157,373 | yes | 4 | 5 |
| II.9 | b | 3.5 | 5.4 | 114,653 | 137,424 | yes | 4 | 5 |
| II.10 | b | 4.1 | 6.1 | 103,382 | 123,255 | yes | 4 | 5 |
| II.11 | b | 4.7 | 6.0 | 123,722 | 141,061 | yes | 4 | 6 |
| II.12 | b | 4.4 | 6.1 | 121,499 | 122,848 | yes | 4 | 5 |
| II.13 | b | 4.4 | 5.5 | 114,005 | 115,817 | yes | 4 | 6 |
| II.14 | b | 5.3 | 6.7 | 120,078 | 135,221 | yes | 4 | 5 |

## What it showed

- **All twenty-eight sailors proved their proposition**, first time.
- **The highest reasoning setting was kept fourteen times out of fourteen**, after
  fifteen of sixteen in voyage 4. It is now the default worth choosing.
- **Shared ground pays.** Book II's propositions lean on Book I throughout (I.4,
  I.29–I.31, I.34, I.46, I.47), and the defined `rect` and `sq` let every
  proposition be stated as Euclid states it: as a sum of areas.
- **Book I stayed whole.** Its pages are byte-identical to the `book-I` release,
  and CI now guards Book II the same way.

With these fourteen, Book II is complete.

**Axioms and gaps.** No axiom added; gaps: see [gaps-book-II.md](../gaps-book-II.md),
written after the voyage.
