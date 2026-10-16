# Sailing orders, voyage 4: Book I, Propositions 33–48

*The scratch proofs these orders name were removed once Book I was proved; they are
at commit 54a08e6
([scratch-04 at 54a08e6](https://github.com/jackChallis/stoicheia/tree/54a08e61a69c3b643590f1c7758c7b8058c9c7aa/docs/reports/crew/scratch-04)).*

Every sailor, Claude or Codex, follows these orders word for word. Your proposition
is I.N; NN is N in two digits.

**The job.** Prove I.N in Lean along Euclid's route, his steps in his order,
citing what he cites where he cites it; draw his figure; write the mishnah. Fifteen
others are proving the rest of I.33–I.48 at once, so cite any proposition by its
statement.

**Read first.** `docs/STYLE.md` and `CONTRIBUTING.md`; `heath/I/NN.md` and
`Elements/BookI/PropNN.lean`; your note under "For the sailors" in
`docs/reports/crew/first-mate-04.md`, and the scratch proof it names, if any;
`Prop16.lean` and `Prop30.lean` (Euclid's case, then the others); Book Zero from
`Elements/Figure/Basics.lean`, above all `Areas.lean` and `Parallelograms.lean`;
`Elements/BookI/HelpersParallels.lean`.

**Scratch proofs.** `docs/reports/crew/scratch-04/` holds proofs written against
the statements to test them. They are not built; check one with
`lake env lean docs/reports/crew/scratch-04/T35.lean`. They follow Euclid's route
but not his sentences. Borrow from yours freely; your proof is still written
under Euclid's sentences, in `PropNN.lean`.

**Shared steps: cite them, never copy them.** The certificate walks through a
step, so the propositions inside it become citations of yours; each is shown
after the step ("adds").
- I.29's angles: `Prop29.alternate`, `.interior`, `.exterior` (adds I.29).
- Where a parallel you drew [I. 31] meets another straight line: `Prop30.meet`
  (adds I.30). Cite it, not `Prop30.unique`, which is a step inside I.30's own
  proof. I.30 for named lines: `Prop30.parallel` (adds I.30).
- "The diameter bisects it" [I. 34]: `Prop34.bisect` (adds I.34). "The halves of
  equal things are equal": `Magnitude.eq_of_add_self_eq` (Book Zero, adds
  nothing).
- A given square is a parallelogram: `Prop28.square` (adds I.28). Squares on equal
  straight lines, and back: `Prop46.square_eq` (adds I.4, I.28),
  `Prop46.side_eq` (adds I.3, I.4, I.28, I.34, I.46).
- I.44's "let it be placed": `Prop44.place` (adds I.2, I.4, I.23, I.30, I.31,
  I.34). Where I.47's squares fall: `Prop47.within` (adds I.13).
- Cutting areas: `area_cut`, `area_lt_of_cut`, `quadArea_add_of_parallelograms`.
  Turning a figure round: `quadArea_reverse`, `quadArea_rotate₂`,
  `Parallelogram.quadArea_rotate`. Close sums with `ac_rfl`.
- Where points fall: `AreParallel.cross_or`, `AreParallel.sameSideOf_or`,
  `Parallelogram.cross`; `Between.of_inside` (a point of a straight line joining
  two parallels, inside both, lies between them); `Between.of_sameSide` (order
  carried across a straight line).

**Citations Euclid doesn't bracket.** Your note lists the ones to expect, and the
mishnah explains each (STYLE check 19). When a shared step brings it in, one
sentence naming the step is enough. For `Prop30.meet`, for instance: that a
straight line meeting one of two parallels meets the other comes from I.30
(`Prop30.meet`), as Heath reports Proclus drawing it under I.31. Refer to that note
in a clause; don't quote it.

**The rules.** Edit only `PropNN.lean`, `figures/I/NN.svg`, `mishnah/I/NN.md`; the
helpers already in `Prop34.lean`, `Prop44.lean`, `Prop46.lean` and `Prop47.lean`
stay. Import `Elements.Figure.Basics`, every proposition you cite, and
`Elements.BookI.HelpersParallels` when you cite a step from it. Keep every `--`
line word for word, Lean under it, your remarks in `/- … -/`. Never change the
statement; never add an `axiom`. If the statement seems wrong or too weak, stop
and say so in your report; do not work around it. No `native_decide` or
`superposition`. Your helpers are `PropN.something`, before `PropN`, with a
docstring. Cite nothing after I.N.

**The voice: last voyage's faults.**
- Euclid's words: "straight line", never "segment"; "coincide" only where he says it.
- No defensive asides ("note that", "strictly speaking"). Say the thing.
- Quote a note of Heath's only on its own proposition's page.
- The mishnah is 200 to 500 words.
- Certificate claims must hold after the merge, when all sixteen are proved: your
  `cites` and `direct_axioms` in `facts.json` are final; anything further comes
  through a cited proposition, so name it. Never write "pending" or "sorry".

**The figure.** Heath's letters, all and only, each point where your proof puts it;
STYLE §4; title "Euclid I.N: …"; no `<desc>`. Leave `NN-idea.svg` alone. In STYLE
check 20, the letters inside the helpers named above don't count, and a point
Heath leaves without a letter gets a name in the Lean and none in the figure.

**Verify.**
```sh
export PATH=$HOME/.elan/bin:$PATH
lake build Elements.BookI.PropNN
lake env lean Certificate/Facts.lean && python3 scripts/check_fidelity.py
rsvg-convert -w 800 figures/I/NN.svg -o "${TMPDIR:-/tmp}/figNN.png"   # then look at it
```
Then STYLE §6, with `$HEATH_OCR` (the OCR text of the Internet Archive scan
`thirteenbookseu02heibgoog`; the captain gives the path; page N is scan leaf
N + 20). No `lake update` or `lake clean`. The generated pages
are rendered after the merge, so CI's "generated pages up to date" step fails on
your branch until then; that is expected.

**Finish.** Commit your three files by name, "I.N: proof, figure and mishnah"; not
`facts.json`, `book/`, `CERTIFICATE.md`, `GRAPH.md`. Codex sailors: your sandbox
cannot write to `.git`, so leave the three files for your bosun to commit. Don't
push, merge or rebase.

**Report:** proved or where the `sorry` is; your helpers; citations beyond Euclid's
brackets, each with the step that brings it in; what Lean made you say; what I.N
rests on, and whether Postulate 5; checks run; anything in the statement, Book Zero
or these orders that got in your way.
