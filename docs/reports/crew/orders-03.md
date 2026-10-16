# Sailing orders, voyage 3: Book I, Propositions 25–32

Every sailor on this voyage, Claude or Codex, follows these orders word for word.
Your proposition, I.N, comes with them; NN is N in two digits (`Prop29.lean`,
`heath/I/29.md`). This is the stretch where the parallel postulate enters: I.29 is
the first proposition that may use Postulate 5.

**The job.** Prove I.N in Lean along Euclid's own route: his steps, in his order,
citing what he cites where he cites it. Then draw his figure with Heath's letters,
and write the mishnah. You work alone in your own git worktree; other sailors are
proving the neighbouring propositions at the same time, so cite any proposition by
its statement, finished or not.

**Read first.**
1. `docs/STYLE.md`, all of it, and `CONTRIBUTING.md`.
2. `heath/I/NN.md` and the sketch `Elements/BookI/PropNN.lean`: the statement,
   and Euclid's sentences as `--` lines above a `sorry`.
3. The note on your proposition under "For the sailors" in
   [first-mate-03.md](first-mate-03.md).
4. The best finished work: `Prop16.lean` (a helper for the figure, and one argument
   written once for Euclid's "similarly"), `Prop24.lean` (cases) and `Prop23.lean`
   (a construction); `mishnah/I/01.md`–`03.md` and `16.md`; `figures/I/16.svg` and
   `24.svg`.
5. Book Zero, `Elements/Figure/`, starting from `Basics.lean`: above all the new
   `Parallels.lean`, and the new lemmas at the ends of `Sides.lean` and `Rays.lean`.
   Then `Elements/BookI/Helpers.lean`.

**The rules.**
- Edit only `Elements/BookI/PropNN.lean`, `figures/I/NN.svg` and `mishnah/I/NN.md`.
- Keep every `--` line word for word (indentation may change), with its Lean
  directly under it. Your own remarks go in `/- … -/`.
- Never change the statement of `theorem PropN`, and never add an `axiom`. If the
  statement seems wrong or too weak, stop and say so in your report.
- No `native_decide`, and no `superposition` (it is for I.4 and I.8 only).
- Postulate 5 only from I.29 on: nothing in I.25–I.28 may rest on `Postulate5`.
- Search Book Zero before writing a helper, and cite its lemma rather than prove a
  copy. Your own helpers are named `PropN.something`, come before `theorem PropN`,
  and each has a docstring saying what Euclid takes for granted; corollaries come
  after it.
- Cite no proposition after I.N. Import `Elements.Figure.Basics` and every
  proposition you cite; if you cite one Euclid gives no bracket for, the mishnah
  says why.
- To cite I.29, let Book Zero draw its figure. With `hpar : AreParallel P G H Q`
  and `hPQ : OppositeSidesOf P Q G H`,
  `obtain ⟨B, C, E, F, h₁, h₂, h₃, h₄, hpar', hside⟩ := hpar.figure_alternate hPQ`
  and then `(Prop29 hpar' h₁ h₂ h₃ h₄ hside).1 : ∠ P G H = ∠ G H Q`. When `P` and
  `Q` lie on one side of `GH`, `figure_interior` does the same.

**The figure.** `figures/I/NN.svg`, Euclid's figure with Heath's letters, all and
only, each point where your proof puts it, in the house style of STYLE §4: 400
wide (440 at most), the parchment card, Georgia italic letters at 17, ink
`#3b2f2f`, what the proposition is about in `#a0522d` drawn heavier, a title
"Euclid I.N: …" and no caption. Heath's own figure is on the scan leaf named in the
first line of `heath/I/NN.md`: `https://archive.org/download/thirteenbookseu02heibgoog/page/n<leaf>.jpg`.
The "at a glance" figure `NN-idea.svg` is already drawn; leave it alone.

**The mishnah.** `mishnah/I/NN.md`, by STYLE §2: 200 to 500 words in three to five
paragraphs, each opening with a short bold lead; "The modern way" last. Say what
Euclid takes for granted, what Lean made us say (exact Lean names in backticks),
and one or two of Heath's best notes. Quote Heath exactly, with the page, checked
against `$HEATH_OCR`, the OCR text of the Internet Archive scan
`thirteenbookseu02heibgoog` (the captain gives the path; volume 1's page N is
scan leaf N + 20), or failing that against the page image.
Quote a note of Heath's only on the page of
the proposition it belongs to. One warm, plain voice: "we", no "I", no crew talk,
no comparisons, no em dashes.

**Verify.**
```sh
export PATH=$HOME/.elan/bin:$PATH
lake build Elements.BookI.PropNN
lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py
rsvg-convert -w 800 figures/I/NN.svg -o "${TMPDIR:-/tmp}/figNN.png"   # then look at it
```
Then run the checklist of STYLE §6 on your three files. Don't run `lake update`
or `lake clean`.

**Finish.** Commit your three files, adding them by name, on your own branch, with
the message "I.N: proof, figure and mishnah" (and any attribution line your
harness asks for). Don't commit `facts.json`, `book/`, `CERTIFICATE.md` or
`GRAPH.md`; don't push, merge or rebase.

**Report**, in your final message:
1. I.N proved, or not; if not, where the `sorry` is and what stopped you.
2. Your helpers, one line each, and any you think belong in Book Zero.
3. Propositions cited beyond Euclid's brackets, and why.
4. What Euclid takes for granted that Lean made you say, and who noticed it first,
   if Heath says.
5. What I.N rests on (`facts.json`), and whether Postulate 5 is among it.
6. The checks you ran, and what they printed.
7. Anything in the statement, Book Zero or these orders that got in your way.
