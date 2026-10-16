# Sailing orders, Book II: Propositions 1–14

Every sailor, Claude or Codex, follows these orders word for word. Your proposition
is II.N; NN is N in two digits.

**The job.** Prove II.N in Lean along Euclid's route, his steps in his order,
citing what he cites where he cites it; draw his figure; write the mishnah. Thirteen
others are proving the rest of Book II at once, so cite any proposition of Book II by
its statement. Book I is proved: cite it as `BookI.PropN`, under Euclid's "[I. N]".

**Read first.** `docs/STYLE.md` and `CONTRIBUTING.md`; `docs/briefs/0003-book-II.md`,
how Lean says "the rectangle contained by AB, BC", "the square on AB" and "the gnomon";
`heath/II/NN.md` and `Elements/BookII/PropNN.lean`; your note under "For the sailors"
in `docs/reports/crew/first-mate-II.md`, and the scratch proof it names, if the captain
gives you one; `Elements/BookII/Rectangles.lean` (Book II's ground) and
`Elements/Figure/Rectangles.lean`; Book Zero from `Elements/Figure/Basics.lean`, above
all `Areas.lean` and `Parallelograms.lean`; `Elements/BookI/HelpersParallels.lean`; and,
as models of a proof under Euclid's sentences, `Elements/BookI/Prop46.lean` and
`Prop47.lean`.

**Rectangles and squares.**
- "The rectangle contained by AB, BC" is `rect A B B C`; "the square on AB" is `sq A B`;
  "twice" a magnitude is that magnitude added to itself.
- A rectangle in the figure is `Rectangle P Q R S`: a parallelogram with one right angle
  is one (`Rectangle.of_right`). "BH is the rectangle A, BC, for it is contained by GB,
  BC, and BG is equal to A" is `Rectangle.eq_rect`, given the two sides at its first
  corner.
- "Let the square ADEB be described on AB [I. 46]" is `BookI.Prop46` (a side from
  `exists_off_line` when every point so far is on one straight line); "AE is the square
  on AB" is `Square.described`. A square that is a parallelogram: `Square.eq_sq`.
- The names follow the lengths: `rect_congr`, `sq_congr`, `sq_symm`, `rect_comm`.
- The gnomon is the sum of its three `quadArea`s; its letters (NOP, KLM, STU) label it
  and are not points.

**Shared steps: cite them, never copy them.** The certificate walks through a step,
so the propositions inside it become citations of yours; each is shown after the step
("adds").
- A rectangle drawn is the rectangle contained by its sides: `Rectangle.contained`,
  `Rectangle.eq_rect`, `Square.eq_sq` (add I.4, I.34); `Square.described` (adds I.4, I.28,
  I.34). One right angle makes a rectangle: `Rectangle.of_right` (adds I.29).
- "Let the figure be drawn": `Parallelogram.figure` (adds I.30, I.31). The complements
  are parallelograms: `Parallelogram.complements`; the parallelograms about the diameter
  and the complements are the whole: `Parallelogram.about_diameter` (each adds I.30).
  In square areas the parallelograms about the diameter are squares:
  `Square.about_diameter` (adds I.5, I.6, I.29, I.34).
- I.47 for the squares on straight lines: `BookI.Prop47.sq` (adds I.4, I.28, I.34, I.46,
  I.47).
- From Book I: `BookI.Prop29.alternate`, `.interior`, `.exterior` (add I.29);
  `BookI.Prop30.meet` for every point where a parallel you drew meets another straight
  line, and `BookI.Prop30.parallel` (add I.30); `BookI.Prop28.square` (adds I.28);
  `BookI.Prop5.base` (adds I.5); `BookI.Prop34.bisect` (adds I.34). Write Book I's names
  with `BookI.` and don't `open BookI`: in a Book II file a bare `Prop4` means II.4.
- Book Zero adds nothing: `quadArea_add_of_parallelograms`, `quadArea_reverse`,
  `quadArea_rotate₂`, `Parallelogram.quadArea_rotate`, `Parallel.between`,
  `Between.of_inside`, `exists_off_line`, `produce_longer`, `OnRay.exists_len_eq`.
  Close sums with `ac_rfl`.

**Citations Euclid doesn't bracket.** Your note lists the ones to expect, and the
mishnah explains each (STYLE check 19). When a shared step brings it in, one sentence
naming the step is enough. For the ground, for instance: that the rectangle drawn is the
rectangle contained by its sides rests on rectangles with equal sides being equal, which
Lean proves once from I.4 and I.34 (`Rectangle.contained`); Euclid takes it for granted
every time he names a rectangle. For `Prop30.meet`: that a straight line meeting one of
two parallels meets the other comes from I.30 (`Prop30.meet`), as Heath reports Proclus
drawing it under I.31; refer to that note in a clause, don't quote it.

**The rules.** Edit only `Elements/BookII/PropNN.lean`, `figures/II/NN.svg`,
`mishnah/II/NN.md`; the ground (`Elements/BookII/Rectangles.lean`), Book Zero and Book I
stay as they are. Import `Elements.Figure.Basics`, `Elements.BookII.Rectangles`, every
proposition you cite (`Elements.BookI.PropNN` for Book I, `Elements.BookII.PropNN` for
Book II), and `Elements.BookI.HelpersParallels` when you cite a step from it. Keep every
`--` line word for word, Lean under it, your remarks in `/- … -/`. Never change the
statement; never add an `axiom`. If the statement seems wrong or too weak, stop and say
so in your report; do not work around it. No `native_decide` or `superposition`.
Postulate 5 is free in Book II. Your helpers are `PropN.something`, before `PropN`, with
a docstring. Cite nothing after II.N.

**The voice: last voyage's faults, and Book II's.**
- Euclid's words: "straight line", never "segment" outside his own "segments"; "the
  rectangle contained by AB, BC", "the square on AB", never "AB times BC", "AB²" or "the
  area of", except in the modern way.
- No defensive asides ("note that", "strictly speaking"). Say the thing.
- Quote a note of Heath's only on its own proposition's page. His notes on Book II's
  definitions and on geometrical algebra (vol. 1, pp. 370–374) are quoted once, where
  they matter most; elsewhere refer to them in a clause.
- The mishnah is 200 to 500 words. The modern way is the identity in a sentence, exactly
  right: II.4 is (a + b)² = a² + b² + 2ab.
- Certificate claims must hold after the merge, when all fourteen are proved: your
  `cites` and `direct_axioms` in `facts.json` are final; anything further comes through
  a cited proposition, so name it. Never write "pending" or "sorry".

**The figure.** Heath's letters, all and only, each point where your proof puts it;
STYLE §4; title "Euclid II.N: …"; no `<desc>`. `figures/II/NN-idea.svg` is not yours:
the artists draw it later. In STYLE check 20, read `heath/II` and `figures/II` for
`heath/I` and `figures/I`; the letters inside the shared steps don't count; a point
Heath leaves without a letter gets a name in the Lean and none in the figure; a
gnomon's letters, II.1's straight line "A" and II.14's figure "A" are drawn as Heath
draws them, and the Lean names them otherwise (a sum of areas, `A₁ A₂`, `A₁ A₂ A₃ A₄`).

**Verify.**
```sh
export PATH=$HOME/.elan/bin:$PATH
lake build Elements.BookII.PropNN
lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py
rsvg-convert -w 800 figures/II/NN.svg -o "${TMPDIR:-/tmp}/figNN.png"   # then look at it
```
Then STYLE §6, with `$HEATH_OCR` at
`/private/tmp/claude-501/-Users-johnchallis/68e6b57d-6355-42a6-8303-c463406f082f/scratchpad/heath-src/heathV1.ocr.txt`
(Book II is pp. 370–410 of the same volume; page N is scan leaf N + 20). No
`lake update` or `lake clean`. The generated pages are rendered after the merge, so
CI's "generated pages up to date" step fails on your branch until then; that is
expected.

**Finish.** Commit your three files by name, "II.N: proof, figure and mishnah"; not
`facts.json`, `book/`, `CERTIFICATE.md`, `GRAPH.md`. Codex sailors: your sandbox
cannot write to `.git`, so leave the three files for your bosun to commit. Don't
push, merge or rebase.

**Report:** proved or where the `sorry` is; your helpers; citations beyond Euclid's
brackets, each with the step that brings it in; what Lean made you say; what II.N
rests on; checks run; anything in the statement, the ground or these orders that got in
your way.
