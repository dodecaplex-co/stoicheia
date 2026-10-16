# Inspection 2: Book I, Propositions 25–48, and closing the book (15 October 2026)

With all forty-eight propositions proved, Book I was closed in three parts. One
bosun carried the [gap catalogue](../gaps-book-I.md) on from I.25 to I.48. A
Lean bosun wrote the shared steps of the area section once each, moved I.29's
corollaries to follow I.29, and removed the scratch proofs of voyage 4 (see the
[decisions](../../briefs/0002-decisions.md)). Inspectors read I.25–I.48 again, as
the first inspection read I.1–I.24, and changed nothing themselves. They reported
28 findings, all marked to fix; a few of them were the same finding seen twice,
in different words. Then the docs bosun merged the two branches, dealt with
the findings, and wrote this.

## What they looked at

- **The mishnah.** Every sentence about the certificate, checked against
  `facts.json`; every reference to Heath followed to its page; names, page cites
  and repeated sentences across I.25–I.48.
- **The figures.** Every figure in I.25–I.48 rendered, letters and strokes drawn
  apart and measured for clearance, and each file's root and fonts set beside the
  other 47.
- **The docs.** README, CONTRIBUTING, the decisions, the gap catalogue, the crew
  logs and orders, and every relative link among them.
- **The pages and CI.** The front page, the Book I index and the certificate,
  `render.py`, and what `check_fidelity.py` would let through.

## What was fixed

**The mishnah.**
- Seven pages (I.37–I.39, I.42, I.44, I.46, I.47) said that Heath reports Proclus
  drawing "a straight line meeting one of two parallels meets the other" under
  I.31. What Heath reports there is Proclus drawing the uniqueness of the parallel
  from I.30 (vol. 1, p. 316); Proclus states the lemma itself in the note on
  Postulate 5, and argues it from distances (vol. 1, p. 207). I.37 now says it
  precisely, once: otherwise two parallels to BE would pass through A, which
  Proclus rules out by I.30, as Heath reports under I.31. The other six refer to
  I.37 or say nothing more.
- Five pages (I.30, I.31, I.41, I.43, I.44) said that the proof uses a postulate
  and left out cited propositions that bring it in as well, as STYLE §2 asks. In
  I.44, superposition comes in through every proposition cited but I.2, not
  through I.4 and I.23 alone.
- Modern people in full on first mention: Bernhard Friedrich Thibaut, Heinrich
  Christian Schumacher and Carl Friedrich Gauss in I.32, Paul Tannery in I.37.
- I.45 calls `quadArea` ours, not Book Zero's: it is defined in
  `Elements/Foundations/Phrases.lean`.
- I.33 and I.34 cite Heath as "(vol. 1, p. N)", like every other page.
- I.36's third paragraph ended with a sentence of pointers to other pages' notes,
  on a lacuna in Proclus and on the converses left to the reader. Neither is about
  the cases the paragraph is on, and the sentence is gone.
- Every page changed is 384 to 450 words, with paragraphs of at most 148.

**The figures.**
- I.47: the A sat on the side AH of the square on AC. It moves left 6 units and
  now clears AH by about 5.
- I.37: the root, card and font stack now match the other 47 figures. It renders
  pixel for pixel as before.
- I.48's idea figure is "the converse of the theorem of Pythagoras", as its
  Euclid figure and I.47's are.

**The gap catalogue.**
- Entries for I.25–I.48 (from the docs bosun's branch).
- The introduction names where the shared steps live as the code now has them:
  `Prop5.base` in `Helpers.lean`, the steps that cite I.28, I.30 or I.31 in
  `HelpersParallels.lean`, and corollaries such as `Prop29.alternate`,
  `Prop34.bisect` and `Prop46.side_eq` after their proposition.
- The postulates section gains Postulate 5 (used directly only in I.29 and I.44,
  where Euclid brackets it; every proposition after I.29 but I.31 rests on it
  through what it cites), and, under Postulate 2, I.30's own producing
  (`Prop30.point_on_side`) beside Book Zero's parallel figures.
- Two helpers from I.1–I.24 that fill a gap are named: `Prop9.side`, and for
  I.14's "Therefore CB is in a straight line with BD", Book Zero's
  `OnRay.between`. Four rule names gain STYLE's comma: "System E, Intersection 2".

**The pages and CI.**
- The front page said that words with no Lean partner are never used in a proof.
  "Diameter" (Def. 17) and "trapezium" (Def. 22) are, and four-sided rectilineal
  figures (Def. 19); each now has `quadArea` as its partner.
- The Book I index shows only the marks it uses, now ✅ alone, and the certificate
  says "What the proofs show" and "29 propositions never need it" now that the
  book is complete. Two pieces of dead code in `render.py` are gone.
- `check_fidelity.py` now fails if any proposition of a completed book is not
  proved, or has lost a figure or its mishnah. Before, a proof put back to `sorry`
  would pass CI once its pages were regenerated. Tried on a scratch copy with I.17
  sketched and two files removed: three failures, as it should be.

**The docs.**
- README: "Join in" points to Book II and to the corrections Book I still welcomes,
  and "How it was made" credits OpenAI's Codex, whose sailors proved I.26, I.28,
  I.30, I.32 and all of I.33–I.48.
- CONTRIBUTING no longer asks for a 🚧 proposition in Book I; it says how each new
  book starts, and welcomes corrections to Book I.
- The scratch proofs are linked at commit 54a08e6, where they were added and never
  changed, from the decisions, the first mate's report and the orders, and the
  decisions record their retirement.
- Voyage 4's log says that every sailor was Codex, though the first mate planned
  for Claude crews too; which twelve propositions had a scratch proof to start
  from; and "about 30 per cent more tokens" (1,675,862 against 1,294,620), not "a
  quarter". The decisions say so too.
- Voyage 3's look-ahead notes where the shared lemma went: `Prop30.meet`, in a file
  of its own.
- The orders of voyages 3 and 4 no longer print a local path; they name
  `$HEATH_OCR`, as STYLE §6 does.

Every relative link in README, CONTRIBUTING, `docs/`, `book/`, the certificate and
the graph resolves (3,220 of them), and every Lean name in backticks on the pages
changed is one Lean knows.

## Where the wording differs from the findings

- **Duplicates.** Where two findings gave different wording for one fix (README's
  "Join in" and "How it was made", CONTRIBUTING, the catalogue's introduction, the
  scratch-proof links), the two are combined.
- **The commit for the scratch proofs.** One finding linked them at `fa7b481`, one
  at `54a08e6`. Both are on `main`; `54a08e6` is where the folder was added, so it
  is the one used.
- **I.14 in the catalogue.** The finding named `Prop14.straight`, which the Lean
  bosun replaced with Book Zero's `OnRay.between`; the entry names that.
- **I.37 and I.38.** To keep I.37 within 450 words its new sentence reads "two
  parallels to BE would pass through A", and "F is found likewise" becomes "F
  likewise". I.38's paragraph already opens "As in I.37", so its Proclus clause is
  dropped rather than replaced by a second "as in I.37". I.34 loses one "that" to
  stay at 450.
- **CONTRIBUTING** does not name `scaffold_book.py`: it holds only Book I's
  statements, and a new book's statements are settled before anyone proves.
- **The front page** reads "`quadArea A B C D` cuts the figure by its diameter
  `AC`", for "cuts by".

Nothing marked for fixing was declined.

## For the captain

1. **The `book-I` release.** A tag and short release notes are public-facing, and
   are left to you, with the push of this branch.
2. **I.47 and I.48** say what "the certificate records directly" and do not name
   the cited propositions that bring the same postulates in, the pattern the five
   pages above were fixed for. I.47: every proposition cited brings in Postulate 1,
   and all but I.4 Postulate 2. I.48: I.8, I.11, I.28, I.34, I.46 and I.47 bring in
   Postulates 1, 2 and 3 and Definition 15, I.3 all but Postulate 2, and I.4 Postulate 1. A
   bracketed clause on each would do; both pages have room (413 and 417 words).
3. **I.34 and I.37 stand at 450 words**, the top of the range the inspection
   asked for. A later change to either should take a sentence out.
4. **The scratch proofs at `54a08e6`.** That each still compiles there with
   `lake env lean` is the inspector's check; it was not repeated here.
