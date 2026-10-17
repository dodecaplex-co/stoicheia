# Voice 1: Books I and II in one voice (16 October 2026)

The [read-through](../read-through-01.md) of Books I to III ended with a judge's
verdict: one voice in manners, but a drift in register. I.1 to I.4 read like light
essays. From I.5 the mishnah turned into a ledger, and by I.33 to I.48, and above all
in Book II, it read like a form being filled in: the same few sentences about Lean's
shared steps on page after page ("I.4 and I.34" in 12 of 14 Book II mishnahs, Proclus
"under I.31" in 11, "Postulate 5 comes in through…" closing 16 paragraphs), leads that
were labels, not hooks, and certificate bookkeeping that the table already shows. The
owner's answer was plain: Books I and II are not frozen at their release tags; rewrite
them in one common voice. Book III's crew will write in that voice from the start.

## The guide, in brief

The captain wrote a voice guide, now folded into [STYLE.md](../../STYLE.md):

- **The register.** A friend who knows Euclid well, talking over his figure with a
  curious reader. I.1 to I.5, I.29 and I.47 set the tone.
- **The shape.** 250 to 450 words, three to five paragraphs, each opening on a hook:
  a question, a claim, or Euclid's or Heath's own words. Euclid first, then Heath,
  Proclus and the history, then at most one paragraph on what Lean made us say, told
  as a discovery, then "The modern way".
- **"We"** is the project, two to four times a page; "Lean" is the machine.
- **Bookkeeping** belongs to the table and the line under it. Each book's shared steps
  are told once, in its introduction, and a page says "the Lean cites" only where the
  reason is its own story.
- **Words and quotations.** Euclid's words for Euclid's things, full names at first
  mention, every quotation exact, with Heath's italics and his page.

## How it was done

Rewriters took the pages a few at a time, each from the read-through's findings, and
an integrator merged their work, with the two book introductions,
`mishnah/intro/I.md` and `mishnah/intro/II.md`, which `render.py` now sets on each
book's index. Three blind readers then read Books I and II, not told who wrote what,
and listened for more than one hand. A polisher worked through their 52 findings, and
wrote this.

## What the blind readers heard

- **Book I, 1–24.** One voice in the commentary: "I could not reliably hear two
  writers." The seam was in the Lean notes, where some pages set every letter in code
  font and wrote in fragments. The register still drifted from I.10 on: a Lean
  paragraph repeating the notes above it, citation bookkeeping, Postulate 4 and `∟`
  explained about nine times across I.11 to I.15, `Prop5.base` five times,
  `produce_longer` five times.
- **Book I, 25–48.** One voice in the mishnah, two hands in the notes (code-font
  letters against clipped plain ones, with stock phrases such as "Book Zero …" and
  "which cites I.30 for the meeting"). Two "what Lean made us say" paragraphs on many
  pages; "which side" told six pages running; I.47, the book's most famous theorem,
  spending half its words on mechanics. One attribution slip: Proclus "under I.31"
  in an I.47 note.
- **Book II.** "One voice in tone and almost one voice in register": the judge's form
  had largely gone, "we" ran at two to four a page, and every quotation checked. What
  was left was a citation tail ("the Lean cites X, which Euclid does not") in 9 of 14
  mishnahs, two factual slips (II.11's "Our title", Clavius named under II.3), a few
  facts told three times, and some dense Lean paragraphs.

Every quotation the readers checked against the 1908 OCR matched its words and page,
scanning errors aside; the one stretch was a gloss in II.1.

## What changed

**The Lean notes.** One convention for both books: Heath's letters plain, backticks
only for Lean names (1,265 code-font letters in 39 files became plain), full sentences
in place of fragments, Heath's bracket form for a justification Euclid leaves out. A
shared step is explained once (`Prop5.base` at I.7, `produce_longer` and Postulate 4 at
I.11, which side at I.27) and pointed to elsewhere; the stock phrases are gone; the
I.47 note no longer puts Proclus' lemma under I.31; Book II's notes on the side a
square stands on and on Proclus are left to the introduction. Where a note and the
mishnah said the same thing, the note now says how and the mishnah why (I.6, I.16,
I.18, I.27, I.39, I.46, II.12).

**The mishnah.** Every page the readers could attribute was brought into the common
voice, and every finding was dealt with:

- The refrains came out: "Lean wants it said" and its kin from 11 to 2 (I.1 and I.5,
  with I.22's "Lean is exactly that dull" as the payoff); "the Lean cites" from 16 to
  1 (II.12, the guide's own example); "we give the argument once" from 4 to none
  (I.17 keeps its "in any manner"); paragraphs ending on "our statement asks …" kept
  only where the hypothesis is the story (I.31, I.33, I.37).
- The freed words went to Euclid, Heath and the history. I.47 now opens on Proclus and
  the ox, says plainly what the windmill does, and gives Heath's *tour de force* and
  Schopenhauer's mouse-trap their paragraph. I.36 gains the lost end of Proclus' note
  and the describers of countries; I.37, Polybius and his camps; I.16, more of Heath on
  straight lines that return on themselves; I.19, Heron's direct proof; I.21, Proclus'
  right-angled illustration; I.24, Heath's "We have already seen one instance in I. 7"
  in place of a third telling of "the most difficult"; II.9, Heath's second proof,
  "still effective".
- Leads became hooks: **Slide the vertex, halve the parallelogram.** (I.41), **Half
  the base does it.** (I.42), **Two bases that touch.** (I.40), **Four places for D.**
  (I.7), **"Without regard to sense."** (I.36), **A circle finds the root.** (II.6).
- The slips: II.11 now says "Book VI has a name for this cut"; II.3's reading line
  puts Clavius under II.4; II.1 says only what Heath says of ὑπό; I.45 gives "half of"
  the base in both places and drops "re-entrant"; II.13 refers to II.12 rather than
  repeating it; II.5 and II.6 no longer share a modern way; II.8's parabola reads in
  plain order.
- Every page is 250 to 450 words, says "we" two to four times, and names four Lean
  things at most, each checked with `#check`; every new quotation was found in the
  OCR and its page read from the running head.

**The pages.** The Book I introduction now maps the whole page, says what System E's
Intersection and Intersections rules are, tells `Prop5.base` once, and lets the table
carry the citations; the Book II introduction names `Rectangle.eq_rect`, the step the
pages' lines name, and points to II.10 for Postulate 5. `render.py` prints a key under
the index's count, a line under the table where Euclid cites a definition that is a
Lean definition rather than an assumption (Def. 10 in I.11 to I.13, Def. 23 in I.27),
a full statement for I.47's subtitle, and a line under Euclid's figure where our drawing
follows the proof rather than Heath (I.23, I.39, I.40); STYLE §4 now sends such notes
there, not to the mishnah. I.34's caption says "diagonal". The reading lines describe a
book once, at its first appearance, and later say only what the chapter adds; I.42
gains a second line, and the "scoreboard" is gone.

## Still open

- **I.23's letters.** The statement puts F on the ray AB and G off it; Heath has them
  the other way about. Swapping them is a change of statement, which needs the
  captain; for now a line under the figure says so. (Closed 17 October; see
  [0002-decisions](../../briefs/0002-decisions.md).)
- **A fresh blind read** would show whether the notes now sound like one hand. The
  register, by the readers' own account, was the larger problem, and the counts above
  are the measure of this pass, not a reader's ear.
- **Four reading lines on the geometric-algebra quarrel** (II.2, II.4, II.6, II.7)
  might move to a Book II reading list, if there is to be one.

**Checks.** `lake build`, `lake env lean Certificate/Facts.lean`,
`scripts/check_fidelity.py`, `scripts/render.py` and `scripts/negative_tests.py` all
pass. No axiom added, no statement changed.
