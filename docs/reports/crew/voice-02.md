# Voice 2: Book III in the common voice (17 October 2026)

[Voice 1](voice-01.md) rewrote Books I and II in one common voice. Book III was then
drafted from the same guide by Codex sailors, enforced by eight captains in two fleets and
given a voice pass of its own, but no one had yet read it beside Books I and II. The
owner asked for Book III to be kept in the common voice as well. Three blind readers read
pages mixed from all three books, not told who wrote what, and listened for a second hand.
A polisher worked through their 33 findings, and wrote this.

## What the blind readers heard

- **The commentary is one voice.** None of the three could reliably tell Book III's
  mishnah from Books I and II. Its leads are hooks of the same kind, "we" and "our
  statement" are used the same way, credit is warm, and every habit one reader measured
  (words and paragraphs a page, Heath cited, Lean names) falls within Books I and II's
  range. Every quotation they checked against the 1908 OCR matched, page numbers included.
- **The margins were a second hand.** Book III's further reading never pointed back to a
  work already met ("met under" on 0 of 37 pages, against 26 of 62 in Books I and II).
  It described Benno Artmann's Book III chapter afresh on 12 pages and Kiran Kedlaya's
  book on 10, and most lines ended on a verb ("explains", "follows", "offers").
- **Shared steps were proved again.** The only verbatim duplicate lemmas in the
  repository were Book III's: `Prop16.one_perp` was `Prop1.perpendicular`, and III.26
  copied `half_lt` and `angle_type` from III.24. III.19 worked the same argument a third
  time inline, and four mishnahs explained it.
- **The Lean notes were impersonal.** One note in 190 said "we", against 27 in 380 in
  Book I; several named local hypotheses (`hout`, `hnearer`); and III.16 left its
  horn-like angle and Porism without a word.
- **The modern ways used TeX.** III.20, III.23, III.29, III.32, III.33 and III.34 wrote
  e^{iθ} and long range clauses that no Book I or II page uses.
- **Smaller things:** stiff sentences in III.4, III.10, III.12, III.13 and III.22; III.12's
  caption repeating its first paragraph; "Def. 11" on Book III's tables with no book; an
  introduction dense with Lean names; I.40 closing a bracket it never opened.

## The letters rule

Heath's letters are plain everywhere, inside his quotations too, and his italics are kept
for his emphasis and his titles. Book III's own voice pass had already done this in the
mishnah: the readers found no italic letters in any quotation. This pass carried the rule
into the files every page links to: the shared-step files (`Squares.lean`,
`Circumferences.lean`, `Rectangles.lean`, `HelpersParallels.lean`, `Helpers.lean`) and the
tacit rules, whose docstrings make each page's list of rules. 541 letters in code font
became plain there; backticks stay on Lean names alone.

## What changed in Book III

- **Further reading.** A work is described once and then pointed back to: 34 of 37
  pages now say "met under". Artmann's chapter stays on III.1, as the guide to the book;
  Kenneth Manders' essay is cited one way, on three pages; each line ends on a phrase
  saying what the reader will find. Where a generic line went, a specific one came from
  the reading list: Felix Klein's *Famous Problems* for IV.16's fifteen-angled figure
  (III.30), Ptolemy's theorem and table of chords (III.22, III.29), Glen Van Brummelen's
  Greek chord tables (III.15).
- **One proof of each shared step.** III.16 and III.19 call `Prop1.perpendicular`, with
  "as in III.1"; III.26 calls `Prop24.angle_type`, and III.26's table now shows it on the
  "Brought in by shared steps" line. III.16's Lean says why the horn-like angle has no
  Lean beneath it and where the Porism is proved.
- **The Lean notes** read as Book I's: 33 of 155 now say "we" (6 before), hypotheses are
  said in words, and "the Lean" is no longer a noun. Notes that retold a mishnah
  paragraph (III.23, III.26, III.29) are cut to the step; III.35's E = G case is told
  once in the Lean and pointed to after.
- **The mishnah.** Every modern way is in Book I's notation, cos θ + i sin θ and words.
  III.20, III.23, III.29 and III.32 open on their idea, not a retelling of the proof;
  III.12 leads with Heron's "But I will show how."; III.26 says plainly where the equal
  circles do their work. The readers' stiff sentences are rewritten.
- **The introduction** names 11 Lean things where it named 18, leads its definitions with
  **Words, not axioms.**, and says why every statement keeps "in equal circles": the
  measure of a circumference would call arcs of unequal circles equal.
- **The tables** write Book III's definitions with their book, "Def. III.11", and the
  footnote under them names what each is in Lean, in one wording for every book.

**Elsewhere.** A few clipped Book I and II notes became sentences (I.7, I.13, I.14, I.17,
I.19, I.20, I.24, I.44, II.8, II.9); I.39's reading points back to Descartes and
Velleman; II.6 leads with **A rectangle that runs past its line.** and says what
"applied" meant. I.40's heading carries Heath's opening bracket, so I.40 and III.12 share
one caption. STYLE now asks for Book I's notation in the modern way, "met under" in the
reading, and no copied helpers.

## Still open

- **A fresh blind read** would show whether the seam is gone; the counts above measure
  this pass, not a reader's ear.
- **Book III's reading is still thin**, 46 lines for 37 pages against about two a page
  in Books I and II. The cause is fewer apt works on the list, not repetition, and a new
  checked work would mend it best.
- **Book Zero** (`Elements/Figure/`) still sets letters in code font. No page shows its
  docstrings.

**Checks.** `lake build`, `lake env lean Certificate/Facts.lean`,
`scripts/check_fidelity.py`, `scripts/render.py` and `scripts/negative_tests.py` all
pass. No axiom added, no statement, `--` line or main docstring changed; the certificate
changes only in III.26's shared steps.
