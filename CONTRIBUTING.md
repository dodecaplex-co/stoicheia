# Joining in

Thank you for wanting to help carry Euclid into Lean. Everything here is meant to be
picked up by anyone: a proof, a page of commentary, a figure, a correction to the
transcription. A few house rules keep the whole thing honest and readable.

## Proving a proposition

Every proposition of Book I is already stated in Lean, with Euclid's sentences in
place as comments and a `sorry` at the end. Pick any 🚧 proposition in
[Book I](book/I/index.md); you can prove it before the ones it cites are finished,
because a proof only needs their statements.

1. **Euclid's words go in `--` comments, ours go in `/- … -/`.** Keep the words
   of every `--` line exactly as they are: CI checks that, read in order, they
   still spell out Heath's text word for word. (Indentation may change, for
   instance when a few sentences move into a sub-proof.) Put the Lean for each
   sentence directly under it. Anything you want to say in your own voice
   ("Euclid doesn't say why…") goes in a `/- … -/` block.
2. **Follow Euclid's route.** Use the propositions he cites, in the order he cites
   them. If Lean needs something he never says, that's a discovery: prove it as a
   small `PropN.figure`-style lemma in the same file, and tell us in the mishnah.
   Helpers go before the proposition, porisms and corollaries after it. A step
   that several proofs share goes in Book Zero; if it cites a proposition, in
   [`Elements/BookI/Helpers.lean`](Elements/BookI/Helpers.lean), or, if it cites
   I.28, I.30 or I.31, in
   [`Elements/BookI/HelpersParallels.lean`](Elements/BookI/HelpersParallels.lean);
   and if it is a consequence of one proposition that later proofs share, after
   that proposition as a corollary (`Prop34.bisect`). Import the files you cite.
3. **Never add an `axiom`.** All assumptions live in `Elements/Foundations/`. If you
   believe Euclid needs a rule that isn't there, open an issue; new rules come from
   System E (or LeanEuclid's corrections of it), with a citation. A rule that holds
   only with the parallel postulate is declared in the namespace
   `Elements.Tacit.Euclidean`, and CI checks that nothing before I.29 rests on it.
4. **Don't change a statement** without opening an issue first: other propositions
   are written against it.
5. **No `native_decide`, and nothing in `Elements/Figure/` may cite a proposition.**
   Book Zero is for facts every figure needs, proved from the foundations alone.

## Writing commentary or drawing figures

[docs/STYLE.md](docs/STYLE.md) has the rules for the voice, the mishnah and the
figures. In short:

- `mishnah/<book>/NN.md`: 200 to 500 words, in the same voice as the rest. What
  does Euclid take for granted? What did Lean make us say? How does the result look
  with coordinates, vectors or complex numbers? Quote Heath (public domain) freely,
  credit everyone, and keep it friendly.
- Each proposition has two figures, both on the parchment background:
  - `figures/<book>/NN-idea.svg`, the "at a glance" figure: no letters, Byrne's
    red (#d0312d), yellow (#f2b705), blue (#1f5aa6) and black, equal things in the
    same colour, and a caption of one or two short sentences in the SVG's `<desc>`
    (it is shown on the page). See `01-idea.svg`, `05-idea.svg`, `47-idea.svg`.
  - `figures/<book>/NN.svg`, Euclid's figure, with Heath's letters, drawn to match
    the proof.

## Before you open a pull request

```sh
lake build
lake env lean Certificate/Facts.lean
python3 scripts/check_fidelity.py
python3 scripts/render.py
```

Commit the regenerated `book/`, `CERTIFICATE.md`, `GRAPH.md` and `facts.json`; CI
checks that they match.
