# Inspection 1: Book I, Propositions 1–24 (15 October 2026)

With I.1–I.24 proved, inspectors read everything again and changed nothing
themselves: the mishnah, the figures, the docs and the generated pages, and what
voyage 2b had left unwritten. They reported 35 findings, a few of them the same
finding seen twice. Each was marked either to fix, or to discuss, when it needs
the captain's judgement. A Lean bosun dealt with the Lean first, moving the
helpers that the voyages had each written for themselves into Book Zero (see
[voyage-02b.md](voyage-02b.md)). Then the docs bosun dealt with the rest, and
wrote this.

## What they looked at

- **The mishnah.** Every sentence about the certificate, checked against
  `facts.json`; formulas and letters against Heath's text and the Lean; names,
  spellings and rule numbers against Heath and the foundations; length and
  repetition against CONTRIBUTING.
- **The figures.** Every Heath figure in I.1–I.24 rendered and checked for letters
  crossed by a stroke, drawing that runs to the frame, points off the lines they
  belong on, and size beside the others.
- **The docs.** README, CONTRIBUTING, the plan, the gap catalogue, the crew logs,
  the references and the credits, and which of them link to which.
- **The pages.** `CERTIFICATE.md`, `GRAPH.md`, the front page and every page footer.

## What was fixed

**The mishnah.**
- Six sentences (I.3, I.8, I.9, I.14, I.15, I.24) said that a step in the proof
  was *why* a postulate is on the certificate. But the certificate counts
  everything a proof rests on, through the propositions it cites, and in each case
  a cited proposition brings that postulate in anyway. They now say that the proof
  uses the postulate there, and name the proposition that brings it in as well.
  The Lean bosun had already put I.5 and I.16 right.
- I.2: Euclid's L lies on DA produced, so it is not the point A + (C − B), which
  is only as far from A as C is from B. The modern way now says just that.
- I.15: the letters AEC first appear where Euclid says what he will prove, not in
  the enunciation.
- I.10 cites the diagram rule Intersection 1, not the construction rules'
  Intersections 1.
- I.17 and I.24: an-Nairīzī, "Proclus'" and "van Pesch", as Heath and the other
  pages have them.
- I.21: the three side facts are named, not counted, so it is clear which does
  what.

**The figures.**
- I.2: C, G and L moved clear of the two circles, and the figure brought to the
  sizes the others use (letters 17, dots 2.6, lines 1.6 and 1.3).
- I.3: the frame enlarged, so that the circle DEF is no longer clipped at the left
  edge, and F lowered clear of the circle.
- I.6: D moved onto AB, where the proof puts it, so that the red DB lies along AB.
- I.24: the second triangle moved left and the frame narrowed from 500 to 440, so
  that its letters print at the same size as the others'.

**The pages.**
- The propositions cited are listed by number, I.3 before I.10, in the
  certificate and on every page.
- The graph follows the [I. 20] in I.22's enunciation as well as the brackets in
  the proofs.
- The front page no longer shows an empty table above "Let the following be
  postulated".
- The footers no longer say "Source:" twice, and fourteen of Heath's source notes
  give a single page as "p. 244; scan leaf n264" rather than "pp. 244–244".
- The Book I index links the gap catalogue.

**The docs.**
- The [gap catalogue](../gaps-book-I.md) has entries for I.17–I.24. It names the
  formalizers it thanks, and ends with a table of the postulates each proof uses
  where Euclid gives no bracket, and the brackets the Lean has no use for, taken
  from `facts.json`.
- A log for [voyage 2b](voyage-02b.md).
- README: the I.1 excerpt keeps our own words out of Euclid's `--` comments; the
  figures and docs rows say what is there, and link the plan, the catalogue, the
  crew logs and the notes on earlier work; and the section on what Euclid takes for
  granted ends with a link to the catalogue.
- CONTRIBUTING: an idea figure's caption may be one or two short sentences, as six
  of them are, among them `47-idea.svg`, which CONTRIBUTING itself points to. A
  rule that holds only with the parallel postulate is declared in the namespace
  `Elements.Tacit.Euclidean`, which is what CI looks for before I.29; and
  `render.py` now reads each rule's namespace from its file, so such a rule will
  show its gloss on the pages.
- The plan says, where a reader can see it, that it is the plan the project
  started from, kept as written, and that where it differs from the code the code
  is right.
- `references.bib` gains J. L. Heiberg's *Euclidis Elementa*, Alfred Tarski and
  Steven Givant's *Tarski's System of Geometry*, and GeoCoq, with its authors named
  from its own AUTHORS file. `CITATION.cff` gains synthetic_euclid_4 and the paper
  by Tadd Mao and his colleagues.
- `assets/CREDITS.md` lists every file in `assets/`, the three square logos among
  them.

## Not done

Nothing marked for fixing was declined. One suggestion is left for later: to
generate the catalogue's table of postulates from `facts.json` and Heath's
brackets, so that it can't go stale. For now it is written out by hand for
I.1–I.24.

## For the captain

1. **The mishnah has grown long.** CONTRIBUTING asks for "a few short paragraphs";
   I.1–I.3 run 188 to 355 words, I.9–I.24 run 700 to 1,230, with single paragraphs
   of up to 367 words (I.22, the circles that must meet). Some of it is repeated
   from page to page: Todhunter on Post. 4 in I.13, I.14 and I.15 (italicised
   differently, and I.14 and I.15 share a heading), Heath's datum rule and
   Todhunter's memory aid in I.18 and I.19, Dodgson's hinged rods in I.7 and I.8,
   Proclus' "fore-arming the learner" in I.5 and I.7, and the thanks to System E
   and LeanEuclid, almost word for word, in about twelve files. One way: keep each
   quotation on the page of the proposition Heath's note belongs to (Todhunter in
   I.14, the datum rule in I.18, Dodgson in I.7, fore-arming in I.5) and refer back
   to it elsewhere; one typography for each; the thanks once per page in a set
   closing form, or left to the README and the rule docstrings; and paragraphs of
   more than about 200 words split.
2. **The plan is public.** It is linked from the README, but lines 27–28 compare
   coverage with other projects and say this is never to be claimed publicly, and
   lines 18, 23, 47 and 105 are notes on a private setup (`~/lean-demo`,
   `~/dev/stoicheia`, elan not on the PATH, workflow sizes). Either take those lines
   out with a visible note, such as "(scoping notes removed before publication)", or
   move the brief out of the public tree.
3. **Credits that never reached the README.** The plan thanks Robert Simson (on
   whose added sentence I.24's mishnah builds), the Nuprl formalization of Book I
   (Ariel Kellison, Mark Bickford and Robert Constable, *Annals of Mathematics and
   Artificial Intelligence* 85, 2019, to be checked), Patrick Massot's leanblueprint
   and the Verso team, Cornell Library, and the Distributed Proofreaders volunteers
   by name. Some may have been dropped on purpose. The README also doesn't say how
   the proofs were made, while the crew logs say the voyages ran with Claude Code's
   Workflow tool; one plain line pointing to `docs/reports/crew/` would do.
4. **Captions.** CONTRIBUTING now allows one or two short sentences, which fits the
   captions as they are. If you'd rather keep strictly one sentence, put the line
   back and merge each pair in `02-`, `06-`, `07-`, `22-`, `26-` and `47-idea.svg`.
5. **Two parts of the planned page.** The plan promised "Also formalized in" links
   and a "Euclid cites" row beside what the Lean needs; neither was built, and no
   brief says they were dropped. The second would help now, since the Lean cites
   more than Euclid brackets in I.6, I.9, I.18, I.20, I.22, I.23 and I.24. Either
   build both in `render.py`, or write a short brief saying they were set aside.
6. **The square logos.** `stoicheia-logo.png` and its 512 and 128 versions are used
   nowhere in the repository. `assets/CREDITS.md` now says what they are; keep them
   or remove them.
