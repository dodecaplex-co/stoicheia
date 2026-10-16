# Sailing orders, voyage 4: Book I, Propositions 33–48

Every sailor, Claude or Codex, follows these orders word for word. Your proposition
is I.N; NN is N in two digits.

**The job.** Prove I.N in Lean along Euclid's route, his steps in his order, citing
what he cites where he cites it; draw his figure; write the mishnah. Fifteen others
are proving the rest of I.33–I.48 at once, so cite any proposition by its statement.

**Read first.** `docs/STYLE.md` and `CONTRIBUTING.md`; `heath/I/NN.md` and
`Elements/BookI/PropNN.lean`; your note under "For the sailors" in
[first-mate-04.md](first-mate-04.md); `Prop16.lean` and `Prop30.lean` (Euclid's case,
then the others); Book Zero from `Elements/Figure/Basics.lean`, above all
`Areas.lean` and `Parallelograms.lean`; `Elements/BookI/HelpersParallels.lean`.

**Shared steps: cite them, never copy them.**
- I.29's angles: `Prop29.alternate`, `.interior`, `.exterior`.
- Where a parallel you drew [I. 31] meets another straight line: `Prop30.meet`. I.30
  for named lines: `Prop30.parallel`.
- "The diameter bisects it" [I. 34]: `Prop34.bisect`.
- A given square is a parallelogram: `Prop28.square`; squares on equal straight
  lines, and back: `Prop46.square_eq`, `Prop46.side_eq`.
- Cutting areas: `area_cut`, `area_lt_of_cut`, `quadArea_add_of_parallelograms`.
  Turning a figure round: `quadArea_reverse`, `quadArea_rotate₂`,
  `Parallelogram.quadArea_rotate`. Close sums with `ac_rfl`.
- Where points fall: `AreParallel.cross_or`, `AreParallel.sameSideOf_or`,
  `Parallelogram.cross`, `Between.of_sameSide`.

**The rules.** Edit only `PropNN.lean`, `figures/I/NN.svg`, `mishnah/I/NN.md`; the
helpers already in `Prop34.lean`, `Prop44.lean` and `Prop46.lean` stay. Keep every
`--` line word for word, Lean under it, your remarks in `/- … -/`. Never change
the statement; never add an `axiom`; no `native_decide` or `superposition`. Your
helpers are `PropN.something`, before `PropN`, with a docstring. Cite nothing after
I.N; a citation Euclid doesn't bracket is explained in the mishnah.

**The voice: last voyage's faults.**
- Euclid's words: "straight line", never "segment"; "coincide" only where he says it.
- No defensive asides ("note that", "strictly speaking"). Say the thing.
- Quote a note of Heath's only on its own proposition's page.
- The mishnah is 200 to 500 words.
- Certificate claims must hold after the merge, when all sixteen are proved: your
  `cites` and `direct_axioms` in `facts.json` are final; anything further comes
  through a cited proposition, so name it. Never write "pending" or "sorry".

**The figure.** Heath's letters, all and only, each point where your proof puts it;
STYLE §4; title "Euclid I.N: …"; no `<desc>`. Leave `NN-idea.svg` alone.

**Verify.** `lake build Elements.BookI.PropNN`, `lake env lean Certificate/Facts.lean`,
`python3 scripts/check_fidelity.py`, `rsvg-convert` and look; then STYLE §6, with
`$HEATH_OCR` at
`/private/tmp/claude-501/-Users-johnchallis/68e6b57d-6355-42a6-8303-c463406f082f/scratchpad/heath-src/heathV1.ocr.txt`
(page N is scan leaf N + 20). No `lake update` or `lake clean`.

**Finish.** Commit your three files by name, "I.N: proof, figure and mishnah"; not
`facts.json`, `book/`, `CERTIFICATE.md`, `GRAPH.md`. Don't push, merge or rebase.

**Report:** proved or where the `sorry` is; your helpers; citations beyond Euclid's
brackets; what Lean made you say; what I.N rests on, and whether Postulate 5;
checks run; anything that got in your way.
