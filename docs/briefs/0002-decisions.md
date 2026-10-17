# Decisions since the plan

*What has changed since [the plan](0001-plan.md), and why. Newest at the bottom.*

## 15 October 2026

- **One voice, and thanks where they are due.** The plan promised an "Also
  formalized in" box on every page, linking the same proposition in other
  formalizations. It was dropped. The pages speak in one voice, and the people
  whose work a page draws on are thanked warmly where it draws on them: in the
  mishnah, in the [gap catalogue](../reports/gaps-book-I.md) and in the README.
- **"Euclid cites" beside "Lean cites".** The certificate line now sets what
  Euclid cites, read from Heath's brackets, beside what the Lean cites, as the plan
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
- **Book II's magnitudes.** "The rectangle contained by AB, CD" is `rect A B C D` and
  "the square on AB" is `sq A B`, areas defined from Definition II.1, and proved once to
  be the area of any rectangle drawn with those sides (from I.4 and I.34). The gnomon is
  the sum of its three parallelograms. The shared steps that cite Book I live in
  [`Elements/BookII/Rectangles.lean`](../../Elements/BookII/Rectangles.lean). The design
  is in [0003-book-II.md](0003-book-II.md), and the first mate's reasons for each
  statement in [first-mate-II.md](../reports/crew/first-mate-II.md).
- **Two books in one certificate.** The scripts and `Certificate/Facts.lean` take a list
  of books; Book I's pages are unchanged by it. Postulate 5 is held back until I.29 in
  Book I only: Book II comes after all of Book I, and II.10 cites the postulate by name.
  `check_fidelity.py` fails if `facts.json` misses a book of `heath.BOOKS`, or if a
  proposition cites one that does not come before it. Heath's "[I. Post. 5]" in II.10
  is kept as he prints it and read as Post. 5; outside Book I, Book I's definitions are
  written with their book (Def. I.15).
- **`Parallel.between` back in Book Zero.** The closing of Book I removed it as unused;
  Book II's ground uses it six times (`Parallelogram.figure`), so it is restored in
  `Elements/Figure/Parallelograms.lean`, unchanged.
- **Book II's scratch proofs in the open.** As for voyage 4, the proofs that tested
  Book II's statements are committed, not built, in
  [`docs/reports/crew/scratch-II/`](https://github.com/jackChallis/stoicheia/tree/19279eb/docs/reports/crew/scratch-II), and the orders name
  that path, so a Codex sailor reads the same ground as a Claude one. T02 draws its
  parallel with `Prop31.parallelogram`, as the orders ask. They are retired when Book II
  is proved.

## 16 October 2026

- **Book III's words.** Equal circles (`EqualCircles`), a straight line touching a circle
  (`Touches`), and circles touching within or without (`TouchesInternally`,
  `TouchesExternally`, `CirclesTouch`) are definitions, in
  [`DefinitionsIII.lean`](../../Elements/Foundations/DefinitionsIII.lean). Circles touching
  is read of the whole circle, the reading Heath reports as Todhunter's (vol. 2, p. 3),
  with "do not cut" made precise by Heath's inside and outside. Heath prefers a local
  reading, at the point of contact, which Lean cannot say without neighbourhoods; so the
  definition carries what Heath says Euclid assumes without stating in III.11–III.13, that
  touching circles do not cross anywhere. III.13 is still a theorem: the definition does
  not say they meet at one point only. The design is in
  [0004-book-III.md](0004-book-III.md), and the first mate's reasons for each statement in
  [first-mate-III.md](../reports/crew/first-mate-III.md).
- **Circumferences measured, not assumed.** Euclid compares circumferences only in one
  circle or in equal circles. Lean measures one by the angle that stands on it at the
  circumference, taken twice (`circumference`, and `standing` for the one on which a given
  angle stands); the facts he takes for granted about them are proved from III.20–III.22 in
  [`Elements/BookIII/Circumferences.lean`](../../Elements/BookIII/Circumferences.lean). A
  magnitude of their own, with tacit rules for adding and applying them, is left to the
  captain; the statements would not change.
- **Circles carry their centres by hypothesis.** A circle in a Book III statement comes with
  `∃ O, Centre O α` unless the setting-out names its centre, or the enunciation measures
  from it (III.14, III.15), and the proofs take it by III.1 where Euclid does, III.14
  included. III.1 finds, by its construction, the centre of a circle that has one.
- **Mixed angles to the mishnah.** The angle of a semicircle and of a segment (III.16, III.31)
  are not angles of ours. The statements carry the rectilineal facts Euclid proves them by.
- **Porisms cited before they are proved.** `Prop1.porism` and `Prop16.porism` are stated now,
  after their propositions. The scripts read "[III. 1, Por.]" as citing III.1, and so does the
  certificate: a citation of `Prop1.porism` is recorded as one of III.1, without walking
  into the porism, and III.1 is not proved until its porism is. I.15's Porism, which
  nothing cites, keeps its record.
- **Three books in one certificate.** The scripts and `Certificate/Facts.lean` take Book III;
  Books I and II render byte for byte as at their tags. Book III may rest on Postulate 5
  throughout. On a Book III page its own definitions are "Def. 11", Book I's "Def. I.10".
- **Book III's scratch proofs in the open**, in
  [`docs/reports/crew/scratch-III/`](../reports/crew/scratch-III), not built: III.1, III.5, III.6, III.11,
  III.13, III.16, III.18–III.22, III.24, III.28, III.29 and III.31 in full, and the first steps of the
  rest. They are retired when Book III is proved.
- **The first mate's statements, challenged.** Twenty-six challenges were answered before the
  voyage (the list is in [first-mate-III.md](../reports/crew/first-mate-III.md)). III.9 no
  longer asks that the point be within, which Euclid's proof does not use and III.25
  cannot supply; III.31 says the angle in the greater segment of every point of it, as
  IV.5 cites it; Book III's ground gains `foot_between`, the perpendicular from the centre
  falling within the straight line, for III.14, III.35 and III.36; Book Zero's straight
  lines in a circle are `Elements/Figure/OnCircles.lean`; and the certificate reads a
  porism as its proposition. III.14, III.15, III.26 and III.27 keep their statements, and
  `circumference` stays an angle, for the captain to decide.
- **Book II's scratch proofs retired.** With Book II proved under Euclid's sentences, the
  scratch proofs that tested its statements are removed from
  `docs/reports/crew/scratch-II/`, as voyage 4's were. They stay in the history at commit
  `19279eb`
  ([scratch-II at 19279eb](https://github.com/jackChallis/stoicheia/tree/19279eb/docs/reports/crew/scratch-II)).
- **A gap catalogue may follow its book.** Book II was released without its gap
  catalogue; [`gaps-book-II.md`](../reports/gaps-book-II.md) follows its book, and Book
  II's index page links it.
- **Where the axioms live, checked from Lean.** `Certificate/Facts.lean` records the module
  of every axiom the project declares and of every axiom a proposition rests on, and the
  `opaque` words, and `check_fidelity.py` reads them: every axiom is in
  `Elements/Foundations/`, there are 87 (5 postulates, Definition 15 and 81 tacit rules),
  and the 17 primitive words and magnitudes of `Words.lean` and `Magnitudes.lean` stay
  `opaque`. A change to either number is a decision for this page. The checks also refuse
  `decide +native`, `set_option debug.…`, `run_cmd` and the other commands that could get
  round the kernel, and CI's page check now sees new and deleted pages too.
- **Negative tests in CI.** The breaks the plan asked for, run once at the start, are now
  `scripts/negative_tests.py`, a CI job of their own: an edited Heath word, the README's
  wrong radii in I.1, and Postulate 5, a planted Euclidean-only rule and an axiom hidden
  after a docstring, all in I.16. Each must be caught, and is.
- **Books I and II in one voice.** Books I and II are not frozen at their tags: `book-I`
  and `book-II` keep the released text, and main carries the pages in one voice. The
  mishnah follows one register (STYLE §1 and §2); each book's shared steps, and where
  Postulate 5 comes in, are told once, in the book's introduction
  (`mishnah/intro/<book>.md`, set on its index page); the line "Brought in by shared
  steps" under each table replaces the sentences STYLE's check 19 used to ask for; the
  titles are in Euclid's words, and the tacit list says "tacit rules". So Books I and II
  no longer render byte for byte as tagged; their statements and proofs are unchanged.
- **Common Notions counted like the other rows.** The owner chose to count the Common
  Notions on each certificate as the postulates, definitions and tacit rules are
  counted, with those of the propositions a proof cites. Until now they counted only
  those named in the proof and its shared steps, so I.5 showed C.N. 3 and 5 but not
  the C.N. 1 and 4 that I.3 and I.4 bring in. `Certificate/Facts.lean` finds them by a
  walk that goes everywhere `collectAxioms` goes; 76 of the 81 proved propositions gain
  Common Notions, and nothing else in `facts.json` changes. The line under each
  page's table now gives one rule for every row.
