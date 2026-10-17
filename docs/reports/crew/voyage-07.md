# Voyage 7: Book III, Propositions 20–37 (16–17 October 2026)

The second fleet on Book III, sailing on the same groundwork
([first-mate-III.md](first-mate-III.md), [0004-book-III.md](../../briefs/0004-book-III.md)).
This is the stretch of the angles at the centre and in a segment, and of the
circumferences they stand on. From III.23 on every proposition imports Book III's ground
for those,
`Circumferences.lean`: a circumference is measured by twice the angle standing on it at
the circumference, and Lean proves once, from III.21, that every such angle gives the
same measure. Ten of the eighteen had a full scratch proof behind them. Three of those
(III.26, III.27, III.30) went by that measure alone, which shows the statement true but
is not Euclid's route, and the orders asked for his.

Again four ships: four Claude captains, ten first mates and eighteen bosuns, with
thirty-six OpenAI Codex sailors (`gpt-6-astra`), two on every proposition, one at Codex's
usual reasoning setting (a) and one at its highest (b), under the same orders
([orders-III.md](orders-III.md)) and the same common voice guide
([voice-01.md](voice-01.md), now [STYLE.md](../../STYLE.md) §1–2), which every sailor
carried and every captain kept. The fleet set out on the afternoon of 16 October, while
the captains of [voyage 6](voyage-06.md) were still at work, and every agent's orders
again began with a note on what the user's latest message meant. Its work reached main
the next morning, 17 October, with Book III complete.

## Results

| Prop | Kept | a: min | b: min | a: tokens | b: tokens | Faithful | Reads as Euclid (1–5) | Captain's edits |
|---|---|---|---|---|---|---|---|---|
| III.20 | b | 2.6 | 4.5 | 85,514 | 134,264 | yes | 4 | 6 |
| III.21 | b | 3.3 | 5.0 | 102,262 | 114,666 | yes | 4 | 4 |
| III.22 | b | 2.65 | 3.67 | 106,444 | 117,484 | yes | 5 | 4 |
| III.23 | b | 3.75 | 4.18 | 117,623 | 116,141 | yes | 4 | 5 |
| III.24 | a | 2.7 | 4.6 | 94,116 | 121,338 | yes | 3 | 5 |
| III.25 | b | 3.1 | 6.0 | 103,303 | 141,009 | yes | 4 | 6 |
| III.26 | b | 3.2 | 5.1 | 117,049 | 135,202 | yes | 4 | 5 |
| III.27 | b | 3.4 | 4.3 | 117,167 | 122,574 | yes | 4 | 4 |
| III.28 | b | 2.5 | 5.2 | 95,934 | 142,053 | yes | 4 | 4 |
| III.29 | b | 2.75 | 3.57 | 114,147 | 131,693 | yes | 4 | 5 |
| III.30 | a | 2.5 | 4.5 | 116,881 | 123,002 | yes | 4 | 5 |
| III.31 | b | 2.7 | 3.9 | 98,212 | 136,168 | yes | 5 | 4 |
| III.32 | b | 2.9 | 4.4 | 119,048 | 125,729 | yes | 4 | 5 |
| III.33 | b | 4.7 | 6.6 | 122,793 | 154,067 | yes | 4 | 8 |
| III.34 | b | 3.0 | 4.4 | 117,626 | 132,652 | yes | 4 | 5 |
| III.35 | b | 4.5 | 5.8 | 110,722 | 145,388 | yes | 4 | 7 |
| III.36 | b | 3.75 | 10.13 | 125,115 | 148,729 | yes | 5 | 5 |
| III.37 | b | 2.6 | 5.0 | 91,339 | 154,977 | yes | 5 | 7 |

## What it showed

- **All thirty-six sailors proved their proposition**, first time, with no retries: with
  voyage 6, seventy-four sailors out of seventy-four.
- **The highest reasoning setting was kept sixteen times out of eighteen**, and
  thirty-three times out of thirty-seven across Book III. Sailor a's proof was kept for
  III.24, for its figure and its file's docstring, and for III.30, where it put Lean under
  two of Euclid's sentences that b had left bare. Sailor b took about two minutes longer
  (5.0 minutes on average, against 3.1) and about a fifth more tokens, though at III.23
  it used a few fewer.
- **Best of both, six times.** The bosuns took the other sailor's mishnah and reading
  line for III.24 and III.30, its mishnah for III.27, its figure for III.29, a sentence
  for III.33, and Heath's italics as sailor a set them for III.25.
- **Postulate 5 is under all of it.** Every proposition from III.20 on rests on the
  parallel postulate. Fourteen come to it through I.32, the angles of a triangle, which
  III.20 uses to compare the angle at the centre with the angle at the circumference;
  III.35–III.37 come to it through the squares, I.46 and I.47, as III.14 does; and III.25
  calls on the postulate itself. So does III.33: both need two straight lines to meet
  where Euclid takes the meeting for granted, and Heath says of III.33, "of course there
  is no difficulty in satisfying ourselves of this" (vol. 2, p. 70).
- **No superposition, even in III.24.** Euclid proves III.24 by applying one segment to
  the other. The Lean compares the radii instead, case by case as the centres fall (III.20,
  III.22), so under Euclid's "applied" and "coincide" it does the same work in another
  shape. Its first mate added remarks there to say how, and read the page as a 3, the one
  3 in Book III: faithful to what Euclid proves, by a different argument. As in voyage 6,
  superposition comes in through I.4 and I.8 alone.
- **The captains still keep the voice**: four to eight edits a page, 94 in all, and 199
  across Book III. Again nothing in the mathematics changed.
- **Minutes, not hours.** The sailors took 2.5 to 10.13 minutes each, III.36's sailor b
  the longest, and the fleet sailed from the first chart to the last captain in about two
  hours.

With these eighteen, Book III is complete: thirty-seven propositions, every one found
faithful to Euclid by its first mate, with Postulate 5 entering at III.14 through the
squares and holding from III.20 on. CI now keeps all three books whole.

**Axioms and gaps.** No axiom added; gaps: see [gaps-book-III.md](../gaps-book-III.md),
written after the voyage.
