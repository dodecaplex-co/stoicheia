# Decisions since the plan

*What has changed since [the plan](0001-plan.md), and why. Newest at the bottom.*

## 15 October 2026

- **One voice, and thanks where they are due.** The plan promised an "Also
  formalized in" box on every page, linking the same proposition in other
  formalizations. It was dropped. The pages speak in one voice, and the people
  whose work a page draws on are thanked warmly where it draws on them: in the
  mishnah, in the [gap catalogue](../reports/gaps-book-I.md) and in the README.
- **"Euclid cites" beside "Lean needs".** The certificate line now sets what
  Euclid cites, read from Heath's brackets, beside what the Lean needs, as the plan
  first intended.
- **Captions.** The caption of an "at a glance" figure may be one or two short
  sentences.
- **Porisms and corollaries come after.** A porism, or any other corollary, follows
  its proposition in the same file; the helpers a proof needs come before it.
- **Shared steps that need a proposition.** Book Zero may not cite a proposition, so
  a small step that several proofs share and that does cite one lives in
  [`Elements/BookI/Helpers.lean`](../../Elements/BookI/Helpers.lean).
- **Three statements made stronger.** I.1 takes an optional side for its triangle;
  I.9 says that its bisector lies within the angle; and I.22 builds its triangle at
  a given corner. The first mate's reasons are in
  [first-mate-02.md](../reports/crew/first-mate-02.md).
- **The mishnah has a length.** Each mishnah is held to 200 to 500 words, and
  [docs/STYLE.md](../STYLE.md) is its style guide.
- **System E and LeanEuclid, thanked once a page.** The thanks to Jeremy Avigad,
  Edward Dean and John Mumma for System E, and to Logan Murphy and his colleagues
  for LeanEuclid, is carried once on every page, in its footer.
- **The square logos stay**, for avatars and icons.
- **A wider crew.** From voyage 3 the crew includes OpenAI Codex sailors alongside
  Claude ones, and an enforcer who keeps the voice one voice. In voyage 4 every
  sailor was Codex, two to a proposition, at its usual and its highest reasoning
  setting.
- **The area section's ground.** Book Zero gains `Areas.lean` and
  `Parallelograms.lean`. The shared steps that cite I.28–I.30 (the angles of
  parallels, "a straight line meeting one of two parallels meets the other", a
  square is a parallelogram) live in
  [`Elements/BookI/HelpersParallels.lean`](../../Elements/BookI/HelpersParallels.lean),
  since `Helpers.lean`, imported by I.7, cannot import them.
- **Three statements changed for voyage 4.** I.38's two triangles may share their
  vertex, as I.42 needs, and I.37 now reads "in the same parallels" the same way,
  so that I.39 and I.41 need no case for it; each of I.48's three squares lies on
  one side of the side it is described on. I.42 is unchanged, and I.44 carries out
  Euclid's "let it be placed" itself (`Prop44.place`). That squares on equal
  straight lines are equal, and the converse, which Euclid assumes in I.48, are
  corollaries of I.46, as Heath reports Proclus proving them there. The first
  mate's reasons are in [first-mate-04.md](../reports/crew/first-mate-04.md).
- **Scratch proofs in the open.** The proofs written to test the statements before a
  voyage are committed, but not built, in
  [`docs/reports/crew/scratch-04/`](https://github.com/jackChallis/stoicheia/tree/54a08e61a69c3b643590f1c7758c7b8058c9c7aa/docs/reports/crew/scratch-04),
  so that both crews start from the same ground.
- **Closing Book I: I.29's corollaries follow I.29.** `Prop29.alternate`,
  `Prop29.interior` and `Prop29.exterior`, I.29 said of any straight line falling on
  two parallels, move from `HelpersParallels.lean` to follow I.29 in its own file,
  as a consequence of one proposition that later proofs share. I.30 and I.32 now
  cite them instead of setting out I.29's figure by hand. `HelpersParallels.lean`
  keeps the shared steps that cite I.28, I.30 or I.31.
- **Closing Book I: shared steps written once.** Book Zero gains
  `OnRay.eq_of_area_eq`, the "greater to the less" of I.39 and I.40. I.31 gains
  `Prop31.line`, the parallel through a point as a named straight line, and
  `HelpersParallels.lean` gains `Prop31.parallelogram`, the parallel drawn, the
  point where it meets the far parallel, and the parallelogram it makes; I.37–I.47
  cite them where each wrote the same steps out by hand. I.14 cites Book Zero's
  `OnRay.between` instead of its own copy, and two Book Zero lemmas that nothing
  used are gone. No statement changed, and the certificate is the same for all
  forty-eight.
- **Scratch proofs retired.** With Book I proved under Euclid's sentences, the
  scratch proofs of voyage 4 are removed from `docs/reports/crew/scratch-04/`. They
  stay in the history at commit `54a08e6`
  ([scratch-04 at 54a08e6](https://github.com/jackChallis/stoicheia/tree/54a08e61a69c3b643590f1c7758c7b8058c9c7aa/docs/reports/crew/scratch-04)),
  where each still compiles with `lake env lean`.
- **Book I must stay whole.** `check_fidelity.py` now fails if any proposition of a
  completed book is not proved, or has lost a figure or its mishnah, so a proof
  that slips back to `sorry` cannot pass CI with its pages regenerated.
