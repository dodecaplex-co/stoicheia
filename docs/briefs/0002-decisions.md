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
  [`docs/reports/crew/scratch-III/`](https://github.com/jackChallis/stoicheia/tree/81d72f5/docs/reports/crew/scratch-III), not built: III.1, III.5, III.6, III.11,
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
  no longer render byte for byte as tagged; their statements and proofs were unchanged
  then.
- **Common Notions counted like the other rows.** The owner chose to count the Common
  Notions on each certificate as the postulates, definitions and tacit rules are
  counted, with those of the propositions a proof cites. Until now they counted only
  those named in the proof and its shared steps, so I.5 showed C.N. 3 and 5 but not
  the C.N. 1 and 4 that I.3 and I.4 bring in. `Certificate/Facts.lean` finds them by a
  walk that goes everywhere `collectAxioms` goes; 76 of the 81 proved propositions gain
  Common Notions, and nothing else in `facts.json` changes. The line under each
  page's table now gives one rule for every row.

## 17 October 2026

- **Book III complete.** All 37 propositions are proved under Euclid's sentences, by two
  fleets (III.1–III.19, then III.20–III.37), and `check_fidelity.py` now keeps Book III
  whole, as it keeps Books I and II. On the certificate 17 propositions never need
  Postulate 5. It comes in at III.14 and III.15, through the squares of I.46 and I.47,
  and lies beneath every proposition from III.20 on: through I.32 for most, through the
  squares again for III.35–III.37, and by name in III.25 and III.33, where Euclid takes
  for granted that two straight lines meet. None uses superposition directly; III.24,
  where Euclid applies one segment to another, compares the radii of their circles. The
  README, CONTRIBUTING and `CITATION.cff` say so.
- **I.23 in Heath's letters.** I.23 now puts G on the ray from A through B and F on P's
  side of AB, as Heath's figure has them (vol. 1, p. 294), and the line under its figure
  is gone; its proof hands I.22 the lengths CD, CE, DE in the order of Euclid's
  sentence. Its callers (I.24, I.31, I.42, I.44, III.7, III.8, III.25, III.27, III.33,
  III.34) turn its angle FAG round with `angle_symm`, for Euclid names each of their
  angles from the arm on the given straight line. The `book-I` tag keeps the old letters.
- **Book III's scratch proofs retired.** With Book III proved under Euclid's sentences, the
  scratch proofs that tested its statements are removed from
  `docs/reports/crew/scratch-III/`, as Book II's were. They stay in the history at commit
  `81d72f5`
  ([scratch-III at 81d72f5](https://github.com/jackChallis/stoicheia/tree/81d72f5/docs/reports/crew/scratch-III)).

The precision pass of [brief 0005](0005-astra-review.md), stages 1 and 1b, answering
Astra's [outside review](../reports/outside-review-01.md), with our thanks:

- **Porisms are entries of the certificate.** "I.15 Por.", "III.1 Por." and "III.16 Por."
  each have an entry of their own in `facts.json`, with `kind`, `of` and `statement`, and
  their proposition names them in `attached`; a `companions` list, empty for now, is ready
  for stage 2's general theorems. Every policy (later citations, superposition, Postulate 5
  before I.29) now runs over every entry, a porism entry must be one of Heath's porisms,
  and a proposition counts as complete only when everything attached to it is proved. So
  III.1 rests on 56 tacit rules and III.1 Por. on 57, `centre_unique` among them, and
  `tests/certificate_expectations.json` pins that. `facts.json` lists the propositions,
  then the porisms, then the companions; [FIELDS.md](../../Certificate/FIELDS.md) says to
  read the entries by `ref`, so the order carries no meaning.
- **One dependency walk, with a self-check.** `Certificate/Facts.lean` finds what a
  declaration uses with one walk, `mentions`, which reads its type as well as its value
  (opaque values and constructors included), and the direct axioms, the Common Notions and
  the shared steps all come from it. Before it writes `facts.json` it checks itself against
  Lean: each entry's `#print axioms`, less Lean's own foundations, must be its direct axioms
  together with those of everything it cites, or the run exits 1, which fails CI's
  certificate step. The `axioms` list of every proposition is byte for byte what it was. A
  negative test plants a later proposition in a helper's statement only, and the walk
  catches it.
- **The axiom lock.** [`Certificate/axioms.lock`](../../Certificate/axioms.lock) holds the
  exact statement of each of the 87 axioms, as Lean prints them with full names and no
  notation, and the 37 definitions, instances and opaque words those statements reach.
  `check_fidelity.py` compares it with `facts.json` in both directions and takes the
  number of Euclid's assumptions from it, and [tests/model/lock.sha256](../../tests/model/lock.sha256)
  pins its hash, so a changed axiom also sends someone back to the model. The lock changes
  only with an entry on this page, and then only through
  `python3 scripts/check_fidelity.py --write-lock`. It was first written today. Words that
  only the propositions' statements use, such as `Touches` or `Parallel`, are not yet in
  it; that question is open in [PROGRAM.md](../PROGRAM.md).
- **Review records, keyed to a commit.** Every proposition has a review record,
  `review/<book>/NN.toml`, in the form [review/SCHEMA.md](../../review/SCHEMA.md) gives:
  the scope of its statement (full, restricted or partial), the route of its proof, what
  the representation adds, any overlap with a rule, and the passages where the Lean does
  not sit beneath Euclid's sentences one for one. Each record carries a fingerprint of the
  statements it read, a hash of its Lean file and the commit it was read at, written by
  `scripts/review_stamp.py` after a reading and never to quiet the check; a changed
  statement or file makes the record stale, and `check_fidelity.py` fails. The records are
  at stage "exceptions" now and become "full" in stage 5. The pages read them: a line under
  each enunciation says what the Lean proves, a table under "In Lean" gives the details,
  and the passage notes stand above the listing. The completion summaries in CERTIFICATE.md,
  the index pages and README's rows (between its `<!-- scope:… -->` markers) are generated
  from them, and CI checks README with the other generated pages.
- **"Heath's references" and "this proof uses".** The square brackets in Heath's text are
  his editorial references, not Euclid's citations: "such specific quotations of earlier
  propositions are rare in Euclid" (Heath, vol. 1, p. 83). The pages and the certificate
  now call them "Heath's references", and a bracket missing does not mean Euclid gave no
  reason. We say that a proof uses Postulate 5, or does not, never that a proposition needs
  it, and "Euclid calls on" only where his own sentence states what he calls on.
  CERTIFICATE.md keeps three things apart: Heath's references, the Lean's dependencies, and
  the reconstruction of the argument in the review records and gap catalogues. GRAPH.md
  draws two graphs for each book, from Heath's references and from the Lean, and names the
  references the Lean does not cite. A check rejects the old phrases on the summary pages.
  This supersedes the wording of the 15 October entry "'Euclid cites' beside 'Lean cites'"
  and the "never need" of the entry "Book III complete" above.
- **Helpers folded, the main proof open.** A page's Lean listing shows the main theorem
  open, with the helpers before it folded into one `<details>` that names them and counts
  their lines, and the corollaries and porism proofs after it in another. Jump links stand
  under the title, the previous and next links are repeated at the foot, the footers link
  the scan leaves of Heath's text and figure, and `scripts/check_links.py` checks every
  relative link and anchor in CI.
- **The model harness lives in the repository.** The programs that test the axioms in the
  plane, and the weakened axioms they must catch, are in [tests/model/](../../tests/model/),
  with [MODEL.md](../../tests/model/MODEL.md) giving the reason each axiom holds. CI runs
  `tests/model/run.py --fast` as a job of its own; `results/` is rewritten only by
  `python3 -I tests/model/run.py --full --write`; and any change to the axiom lock means
  MODEL.md is read again and `lock.sha256` updated in the same change.
  `tests/model/hyperbolic.py`, which checks numerically that every axiom but Postulate 5
  holds in the hyperbolic plane, is the evidence any page must name if it ever claims a proposition
  cannot do without Postulate 5; until then the pages keep to "this proof uses". A formal
  model in Lean with Mathlib, as a separate package, is a later milestone, defined in
  MODEL.md.
- **The overlap catalogue.** [docs/reports/overlaps.md](../reports/overlaps.md) lists where
  one of System E's rules already says what Euclid proves (I.7, I.23, III.2, III.5, III.6)
  or carries one of his steps: the rule, where it first enters, what brings it in, what our
  proof does, and an audit lemma. The lemmas, in `Audit/Overlaps.lean`, each have the
  proposition's own type and are proved from the rules alone; nothing imports them, and CI
  builds them with `lake build Audit`. A page with an overlap says so in its top line. The
  audit also shows that Diagram-angle 3 (`adjacent_eq_of_right`) follows from the other 86
  axioms by I.13; it stays an axiom, as System E has it. Deriving such propositions from
  weaker assumptions is an optional workstream of its own, not part of this plan.
- **Voice rules are defaults.** The voice rules are now defaults, each with a reason, not
  quotas: no count of "we"; a mishnah of usually 250 to 450 words, an exception having its
  reason; bold leads where they help; a modern method may recur where it is clearest.
  "Nothing hedged" becomes "state facts directly; qualify uncertainty precisely". A proof
  in Lean is an argument, so no dummy citations and no artificial uses of a hypothesis: the
  crew orders no longer ask that every hypothesis be used or that every bracket be cited.
  Further reading describes a work in full at its first appearance in each book. This
  supersedes the 15 October entry "The mishnah has a length".
- **The layered standards, after Astra's guide.** [AGENTS.md](../../AGENTS.md), which
  `CLAUDE.md` imports, opens with Astra's ten rules and the order of priorities, and links
  each rule to its one home: [CONTRIBUTING.md](../../CONTRIBUTING.md) for people,
  [STYLE.md](../STYLE.md) for what a reader sees, [FORMALIZATION.md](../FORMALIZATION.md)
  for the Lean, [WORKFLOW.md](../WORKFLOW.md) for how the work is run, with the
  [templates](../templates/), [reviewed examples](../examples.md) and a brief for each
  book ([I](book-I.md), [II](book-II.md), [III](0004-book-III.md)). `scripts/check_style.py`
  fails on STYLE's hard rules and reports its defaults without failing.
- **Book III's further reading.** Ivor Thomas's Loeb *Selections* is linked to Harvard
  University Press and not marked free, since the translation is still in copyright;
  Koshkin's article is linked to its free arXiv preprint, with its DOI in the text; Tom
  Davis's handout on inversion is linked over http, which is the address that works.

The follow-ups to the precision pass, from its integrator's notes and the readers'
findings:

- **Two more kinds of passage, and what "argued another way" means.** A record's passages
  may also be `case`, a case Euclid's figure leaves aside, or leaves to the reader, which
  the Lean takes as well (II.14's ED the greater, III.2's AB through the centre), and
  `given`, a step the statement or our representation already gives, so that no Lean
  stands beneath it (I.5's D and E). A `different` passage, one the Lean argues another
  way, changes Euclid's route, so its record's route is `modified` or `alternative`, never
  `euclid`, and `heath.load_review` refuses the pair. I.39 and I.40, whose Lean makes the
  end of Euclid's reductio direct, are therefore "one step changed" on their pages and in
  Book I's summary. [review/SCHEMA.md](../../review/SCHEMA.md) gives the kinds.
- **A short line beside the badge.** `[statement] short`, at most 70 characters and
  required when a statement is restricted or partial, is the few words beside the badge
  under each enunciation ("bases that meet end to end"); the `note`, of up to 160
  characters, stays in the page's table under "In Lean".
- **Records with the statements.** A new book's review records are written at the stage
  "exceptions" together with its statements ([WORKFLOW](../WORKFLOW.md), section 10, step
  3), so that the scope, the route expected, the representation and every exception known
  are challenged before any proof is assigned. Each is read again when its proof lands,
  and brought to the stage "full" before the book's acceptance. Books I–III, whose records
  came after their proofs, reach "full" in brief 0005's stage 5.
- **One home for the line between the crew and the reader.** [STYLE](../STYLE.md), section
  1, "Production stays out of the mathematics", is the one home of the rule that readers
  meet Euclid, Heath and the proof, not the people and agents who made the page.
  AGENTS.md, the [orders template](../templates/orders.md) and every fleet prompt point
  to it instead of restating it, and `check_style.py` (S2) checks its words.
- **I.47 and I.43 stay whole.** I.47's statement takes the squares standing outward, as
  Euclid describes them; squares on one straight line are equal whichever side they stand
  on (`Prop46.square_eq`, after Proclus), and `Prop47.sq` says it of any squares. A choice
  of figure backed by a proved equality counts as full. I.43's parallelograms about the
  diameter meet at a point of it, as Heath reads Euclid's words (vol. 1, p. 341); Proclus's
  cases, with the parallelograms apart or overlapping, are commentary, not scope, and the
  mishnah tells them. SCHEMA's "full" says both.
- **When a route is "one step changed".** A record's route is `modified` when the Lean
  argues another way a real case within Euclid's statement, or one of his steps. When a
  case is trivial, or lies beyond his statement, the route stays `euclid`, and the case is
  declared as a passage. SCHEMA's `[route]` says so.
- **Overlaps: I.7 and I.23 supply a step.** The shortest proofs we found of I.7 and I.23
  from System E's rules alone take seven and eight of them: Circle 4 and superposition do
  the work, and the rest draw a figure the statement never mentions and tell its parts
  apart. That is more than "at once", so [the overlap catalogue](../reports/overlaps.md)
  lists both as supplying a step, and "gives it at once" now means a proof from at most
  three rules. Their records keep their `[overlap]`, since each rule still carries its
  proposition's content. Diagram-angle 3 (`adjacent_eq_of_right`) follows from the other
  86 axioms by I.13 (`Audit.adjacent_eq_of_right`), and stays an axiom, as System E has
  it. This corrects the list "I.7, I.23, III.2, III.5, III.6" in the entry "The overlap
  catalogue" above: III.2, III.5 and III.6 are the rows a rule states or gives at once.
- **The order of facts.json.** `facts.json` lists the propositions of every book, then the
  porisms, then the companions, each group in `heath.prop_key` order, and
  [FIELDS.md](../../Certificate/FIELDS.md) asks every reader to find an entry by its
  `ref`, so nothing depends on the order.
- **The statements' words in the lock.** The axiom lock now holds every word that the
  statement of a proposition, a porism or a companion reaches, as well as those the
  axioms' statements reach: 24 more, 61 in all. They are `AreParallel`, `CirclesTouch`,
  `Contain`, `EqualCircles`, `Equilateral`, `InsideTriangle`, `IsAcute`, `IsObtuse`,
  `OnRay`, `OppositeSidesOf`, `Parallel`, `Parallelogram`, `Rectangle`, `SameSideOf`,
  `Square`, `Touches`, `TouchesExternally`, `TouchesInternally`, `circumference`,
  `instNonemptyMagnitude`, `quadArea`, `rect`, `sq` and `standing`. A statement prints
  such a word by name, so a new definition of `Touches` would have changed no printed
  statement and no review fingerprint; now it fails `check_fidelity.py`, as a changed
  axiom does, until it is a decision recorded here. `Certificate/Facts.lean` walks from
  the entries' statements as well as the axioms', and reads every word's type; the 87
  axioms and the 37 words they reach are byte for byte as they were, so
  [MODEL.md](../../tests/model/MODEL.md) stands, and
  [lock.sha256](../../tests/model/lock.sha256) is renewed. The lock was rewritten with
  `python3 scripts/check_fidelity.py --write-lock`; [FIELDS.md](../../Certificate/FIELDS.md)
  says how the vocabulary is found, and a negative test gives `Touches` another meaning
  in a copy of facts.json and checks that the lock catches it. This settles the question
  PROGRAM.md left open.
- **PROGRAM.md's status table, generated.** `render.py` writes the status table of
  [PROGRAM.md](../PROGRAM.md) between its `<!-- status -->` markers: the propositions
  proved from `facts.json`; the records, how many are current and how many stand at "full"
  and at "exceptions", from `review/`; and the stage, the outside score and the release
  from [program.toml](../program.toml), which the coordinator keeps by hand. CI's check of
  the generated pages covers it, and the integrator commits it with the other generated
  files. Acceptance reads "—" until the acceptance report of brief 0005's stage 6.
- **Pushing to main, safely and without asking.** The owner, on 17 October: "you definitely
  don't need my push for every one; build a harness that makes pushes safe." The coordinator
  pushes to main without asking, and only through [`scripts/safe_push.py`](../../scripts/safe_push.py),
  which checks the exact commit from end to end before it pushes: a fast-forward of main, a
  secret scan, the statement, lock, Heath and directory guards, the full CI sequence including
  the planted breaks, and then GitHub's CI. A pre-push hook refuses any other push to main.
  Tags, releases, release notes, the GitHub description and anything sent outside the
  repository still need the owner's OK.
- **Landing work: pull requests, judged by origin/main's harness.** The owner, on 17
  October: "Seems like it should have some proper PR discipline already ... maybe we need
  a little more discipline around that." This supersedes the entry "Pushing to main,
  safely and without asking" above: nothing is pushed to main any more, by the coordinator
  or anyone. Work lands on main only as a pull request, merged with a merge commit,
  through [`scripts/safe_push.py`](../../scripts/safe_push.py) alone:
  `safe_push.py --branch <name>` checks the exact commit, pushes it to its branch and
  opens or updates its pull request, and `safe_push.py --merge <n>` merges it only when
  the secret scan and the guards pass again on its head, CI is green, the required boxes of
  `.github/pull_request_template.md` are ticked and the coordinator's sections written,
  the pull request carries a label for its kind and is not a draft, and a protected change
  carries `security-review`. A check change lands in a pull request of its own: when
  origin/main's copies of the checks fail on a pull request that also changes what they
  judge, the pre-flight refuses it, unless the only check inputs it changes are the values
  pinned to the edition (the axiom lock, the model's hash of it, and the counts and
  values of the certificate's expectations, none of them dropped or loosened), which move
  with the content they pin. `scripts/hooks/pre-push` refuses
  every push to main, and scans, with origin/main's copy of the scan whichever remote it
  goes to, a push to any other branch and a tag the owner allows; and the ruleset on main
  is on: a pull request, the checks `check`, `model` and `negative`, and no force push or
  deletion. The pre-flight and the merge run as `git safe-push`, the launcher
  `scripts/hooks/safe-push`, which `scripts/install_hooks.sh` installs outside the tracked
  tree with the hook, and which runs origin/main's copy of the harness, so that a branch
  cannot judge itself. A false positive of the scan goes in
  `scripts/safe_push_allow.toml`, pinned to its value (held in its match, or named by its
  SHA-256), and `scripts/test_safe_push.py` plants a bad commit for every guard, gate and
  edge case, the reviewers' notes among them. Agents never push, or open, merge or approve
  a pull request; tags, releases, release notes, the GitHub description and anything sent
  outside the repository still need the owner's OK ([WORKFLOW](../WORKFLOW.md), section
  10, "Landing work: pull requests").

## 18 October 2026

- **The phrase rules read across a line break.**
  [`scripts/check_style.py`](../../scripts/check_style.py) now finds a phrase of its tables
  however a line or a comment wraps it: the words of a phrase may stand apart by spaces,
  tabs or one line break, and a blank line ends the phrase. This covers S2 to S7, S9, S11
  and D7 to D10 ([STYLE](../STYLE.md), section 8). Nothing is loosened: S3 catches at least
  what it caught before, and the self-check holds a case for each rule, run on every
  check. It lands after the wording sweep, on whose text it passes.
- **Staging: statements before their proofs, built by CI.** Statements are settled before
  proofs ([WORKFLOW](../WORKFLOW.md), section 2), and a stage's new or changed statements
  are now written first in a library of their own, `Staging`, each with `sorry` where its
  proof is due, then challenged and approved before any proof is assigned. A statement
  leaves Staging when it is proved. The library is a `[[lean_lib]]` in `lakefile.toml`,
  beside Audit and like it outside `defaultTargets`, with its root
  [`Staging.lean`](../../Staging.lean). Unlike Audit's, its `globs` take every file under
  `Staging/`, so a staged file is built whether or not the root imports it, and
  `Staging/.gitkeep` keeps the directory when nothing is staged. Its files import
  `Elements`, and nothing outside `Staging/` imports them, so nothing staged reaches a
  proof or the certificate. CI's `check` job builds it after `lake build Audit`
  (`.github/workflows/ci.yml`), so that a change to main which breaks a staged statement
  fails at once, not when the statement moves. It is a build check, not a check that
  anything is proved: `sorry` warnings do not fail it. The step joins the full sequence of
  [WORKFLOW](../WORKFLOW.md), section 8, and the `CHECKS` list of
  [`scripts/safe_push.py`](../../scripts/safe_push.py), which runs that sequence. The
  library lands empty, as a change of its own, before any statement is staged in it.

- **The companions list, in the edition.** The list of companions the certificate reads,
  each declaration with its reference ("I.40 general"), moves out of
  `Certificate/Facts.lean` and into the edition, as `Elements.companions` in
  [`Elements/Companions.lean`](../../Elements/Companions.lean), which `Elements.lean`
  imports last. `Certificate/Facts.lean` now reads that list, and checks every entry
  exactly as before: declared, in a proposition's namespace, listed by the reference its
  name gives, and never a porism. The reason is the pull-request discipline. A check change
  travels alone, in a pull request of its own, while a companion's listing must travel with
  its proof and with its record's stamp; with the list inside a check, listing a proved
  companion would have been a check change. Now it is a change to the edition, made by the
  integrator in the commit that moves the companion beside its proposition, and the
  checks stay where they were. The list is still empty, and `facts.json` is byte for byte
  as it was. This moves the list of the 17 October entry "Porisms are entries of the
  certificate"; [FORMALIZATION](../FORMALIZATION.md), section 2, WORKFLOW, section 4, and
  AGENTS.md say where it lives and whose it is.

- **Heath's letters at a glance: the rule, with its switch off.** The owner, on 17 October:
  "Proof without words is one thing - proof without Point labeling is quite another!" A
  figure at a glance may now carry Heath's letters, the names Euclid's figure and the Lean
  use, so that a reader passes from Byrne's colours to the proof by the same A and B
  ([STYLE](../STYLE.md), sections 2, 7 and 8). On the owner's word,
  [`scripts/check_style.py`](../../scripts/check_style.py) drops S14's ban on a letter in a
  figure at a glance, and checks the letters instead: S20, each letter one that Euclid's
  figure draws, italic, at 14, in the ink of what it stands on; S21, each point the figure
  shows lettered within 30 of it, or marked `data-unlettered` with its reason. Its switch,
  `IDEA_LETTERS_REQUIRED`, is `False` for now: S21 holds a figure only once it carries a
  letter, and D14 lists the figures with none yet. The figures are lettered in a change of
  their own, and the switch is turned on once every figure passes S21.
- **Heath's letters at a glance: required.** Every figure at a glance now carries Heath's
  letters, 598 on the 99 figures of Books I to III, and passes S21, so the switch
  `IDEA_LETTERS_REQUIRED` in [`scripts/check_style.py`](../../scripts/check_style.py) is
  `True`: S21 holds every figure at a glance, and D14 is empty. [STYLE](../STYLE.md),
  sections 2, 7 and 8, say so now. The switch is never turned back to quiet a figure: the
  figure is lettered. This supersedes the line "no letters in idea figures" of
  [brief 0005](0005-astra-review.md), in stage 1b's list of what `scripts/check_style.py`
  enforces, and "the idea figures have no letters" in item 7 of its planned acceptance
  checklist (stage 6).
- **Every proof checked again, by Lean's kernel and by nanoda.** A cold Claude review of
  18 October contributed [`scripts/check_kernel.py`](../../scripts/check_kernel.py), with
  thanks. After `lake build`, it has `leanchecker --fresh` replay the whole environment of
  `Elements`, Lean's own declarations included, through Lean's kernel, and has nanoda, a
  type checker written separately, check the whole export that `leanexport` writes,
  admitting only the axioms of [`Certificate/axioms.lock`](../../Certificate/axioms.lock)
  and Lean's three. Its self-test withholds Postulate 5, and nanoda must then fail, naming
  it. All three programs come with the pinned toolchain, and each is the generous work of
  others: leanchecker is Kim Morrison's and Sebastian Ullrich's, and began as Kim
  Morrison's [lean4checker](https://github.com/leanprover/lean4checker); leanexport is
  Henrik Böving's, for the Lean FRO; nanoda is Chris Bailey's
  [nanoda_lib](https://github.com/ammkrn/nanoda_lib). We are grateful to them all.
  The script is a check added, never a check weakened; the files it changes are
  [`scripts/check_kernel.py`](../../scripts/check_kernel.py) (new),
  [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) (a step in the `check` job,
  after the certificate), [`scripts/safe_push.py`](../../scripts/safe_push.py) (the same
  step in its sequence), [WORKFLOW](../WORKFLOW.md), section 8, and
  [FORMALIZATION](../FORMALIZATION.md), section 9 (a row of its table of evidence); the
  README's table of checks and its "Run it" list follow in a docs pull request of their
  own, after this one. At `f17b427` nanoda checks all 59,902 declarations of the export,
  and the script runs in about a minute on a laptop, with leanexport, its largest step,
  at about 1.3 GB of memory at most. Its time in CI is still to be measured, on this pull
  request's first run there, and recorded on #62, with the choice that follows from it:
  the `check` job, or a job of its own if it is slow.

- **Brief 0006 frozen; I.45 and II.14 full; the definitions approved as a class; Staging's
  proofs.** Astra's second answer (read-only, at `b48640c`, on [issue
  #13](https://github.com/jackChallis/stoicheia/issues/13)) is the challenge of the
  statements of [brief 0006](0006-statements.md) as they stood at `b48640c`. It accepts
  `full` for I.45 and II.14 as stated there, under the convention that the figure comes with
  a checked finite dissection, with `Prop45.apart` and `Prop14.square` the decisive
  companions, and asked only for wording corrections, which are applied. After that answer,
  at the coordinator's direction, `Prop45.fan` and `Prop14.fan` gained a conclusion: that
  the fan's triangles are a fitted figure, besides the parallelogram (the square), so that
  their two conditions do logical work. Astra did not read that change, which only adds a
  conclusion; the independent review of `9c89bfe`, after the freeze, read it, found it
  correct, and is its challenge. `full` rests on the `Apart` companions, which that change
  leaves as they were. The coordinator approved the statements and froze brief 0006 on 18
  October 2026; a later change is a revision of it (WORKFLOW, section 2, "Correcting a
  frozen brief"). The owner's calls: I.45 and II.14 are `full`, by the checked fan and by
  supplied divisions; and, as the tracking issue ([issue
  #50](https://github.com/jackChallis/stoicheia/issues/50)) records them, "the definitions
  the frozen briefs name are approved for the foundations, each recorded in its pull
  request", and "the coordinator freezes briefs after their challenge". So the definitions
  of every frozen brief, this one's and later ones', are approved as a class; each moves
  with the first approved statement that uses it, and the pull request that moves it records
  it. The rule on proofs in `Staging/` is amended, in its one home,
  [WORKFLOW](../WORKFLOW.md), section 2, "What proofs `Staging/` may hold": besides the
  checks of today's statements, `Staging/` may hold proofs that derive one staged statement
  from others, which test their interfaces, and the proofs of a prototype the coordinator
  has approved; a staged statement's own proof still waits for its brief's approval. The
  coordinator added one sentence to the amended rule: a derivation from a stub proves
  nothing until the stub is proved, and says so in its docstring or its brief. On the
  independent review of `9c89bfe`, after the freeze and before landing, one more was added,
  at the coordinator's direction: once its brief is approved, a staged fact whose proof
  rests on no stub may be proved in place, and waits in `Staging/` until the definitions it
  uses reach the foundations and the task its brief names for its home moves it (brief
  0006's `Fitted.inside_pairwise`, `chord_cases` and `Placement.unique_off` are such facts).
  On the same review, `Prop14.general` was renamed `Prop14.figure` ("II.14 figure"), as in
  I.45, its statement unchanged, and `Rectilineal.toApart` and `Rectilineal.area_toApart`,
  which no statement uses, were added for proofs. Staging also serves the stages of briefs
  after 0005, the first being stage 4b of brief 0007, in draft when this was decided; the
  module doc of [`Staging.lean`](../../Staging.lean) and the comment on the `Staging`
  library in `lakefile.toml` say so, and that comment is the only change to
  `lakefile.toml`. The orders for a statement wave ([orders](../templates/orders.md),
  kind 2) and [FORMALIZATION](../FORMALIZATION.md), section 6, point to the rule.
- **Overlaps: I.2 and I.3 supply a step, as I.23 does.** A cold Claude review of 18
  October found it, with thanks: superposition lays a triangle down at A along AB, and so
  carries a length. The shortest proofs we found of I.2 and I.3 from the rules alone use
  ten and twenty-two of them (`Audit.I_2`, `Audit.I_3`); the rest draw a triangle and a
  point off AB that the statements never give, and, for I.3, put the new point between A
  and B. The catalogue lists both as supplying a step, and their records gain an
  `[overlap]` on `Tacit.superposition`; our I.2 and I.3 are Euclid's constructions and
  never use the rule. After Argon's second review of the Book III release, the catalogue
  also says that its "First enters" column reads `direct_axioms`, which counts a rule a
  proof reaches through a Book Zero lemma or a shared step, and its notes name that lemma
  until #65 keeps the two apart; II.14 and III.15 join the III.2 entry. This extends the
  list in "The overlap catalogue" above.

- **A sentence is carried only by the Lean beneath it.** Argon's second review of the
  book-III release found a hole in `uncarried_runs`, in
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py), and we thank Argon
  warmly for reading the check so closely: a run of `--` lines counted as carried by any
  Lean after it, and a `/- … -/` remark joined the runs on either side of it into one, so
  a sentence with no Lean of its own could pass. Now a run is carried only by a line of
  Lean after it and before the next run, and a remark ends a run without carrying it.
  Lean after a remark, before the next run, still carries the run before the remark, so
  a remark may stand between a sentence and its Lean, while one between two sentences
  that share one step leaves the first with none. A closing `exact` is such Lean too, so
  of Argon's two examples the rule finds the one in III.10; the one in III.31 stands
  above the closing `exact`, and its record declares it all the same. The check is
  strengthened, never weakened: every sentence the old rule found with no Lean, it still
  finds, and a passage now declares only the run it begins in.
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) gains a test that plants
  a remark in I.5 between two sentences sharing one step of Lean, and expects the first
  caught and the second not; the old rule misses it.
  [`review/SCHEMA.md`](../../review/SCHEMA.md#two-stages), "Two stages", tells
  contributors in one clause where a remark goes, and [FORMALIZATION](../FORMALIZATION.md),
  section 5, points to it. On main's records the rule finds 15 runs not yet declared, in
  I.5, I.6, I.13, I.14, I.21, I.23, I.39 to I.42, I.47 and II.10. The records' pull
  request, [#82](https://github.com/jackChallis/stoicheia/pull/82), declares them, and
  this change lands after it ([#61](https://github.com/jackChallis/stoicheia/issues/61)).
- **Book I's definitions map, from Argon's second review.**
  [`scripts/render.py`](../../scripts/render.py) changes what it writes and nothing it
  accepts or checks: `FRONT_LEAN_I`, the Lean column of Book I's front page, now says what
  the Lean has for each definition (I.17 and I.18 as III.15 and III.31 state them;
  `Isosceles` and `RightAngledTriangle` defined but used by no statement or proof, as their
  docstrings in `Elements/Foundations/Definitions.lean` now say; the oblong a `Rectangle`,
  the rhomboid a `Parallelogram`; "none" where nothing stands for a word), and every front
  page says that words with no Lean partner are never used in a Lean proof. It is not a
  check change (WORKFLOW, section 10); the regenerated pages show it. III.15's record
  becomes `restricted` until #26, and brief 0004's table of exceptions gains its row
  ([#64](https://github.com/jackChallis/stoicheia/issues/64)).

- **Mixed angles: the prototype approved, its proofs kept in Staging.** The owner approved
  stage 4b on 18 October
  ([the approval on issue #51](https://github.com/jackChallis/stoicheia/issues/51#issuecomment-6252155076)),
  with a prototype of mixed angles first for III.16 and III.31: if it holds, they go full,
  and if not, they stay partial with Astra's wording. The prototype is
  [`Staging/Stage4b/MixedAngles.lean`](../../Staging/Stage4b/MixedAngles.lean), with its
  account in [the report](../reports/mixed-angles-prototype.md)
  ([issue #56](https://github.com/jackChallis/stoicheia/issues/56)): Astra's representation
  from issue #51, a mixed angle as a geometric object, compared with a rectilineal angle by
  containment near its vertex, in plain Lean on the existing foundations. It adds no axiom:
  the report's census finds every theorem resting only on axioms already in
  `Certificate/axioms.lock` and on Lean's own, and none on `sorry`. It was re-challenged and
  verified on 18 October by readers who did not write it; the verifier read `dfb9291` and
  handed back at `4705a9c` with a fix of its own. The coordinator takes placement in the
  form the prototype proves, the invariance of the comparisons (`Segment.congruent`,
  `Prop16.semicircle_congruent` and `Prop16.horn_congruent`, the report's section 3), as the
  check of congruent placement that #56 asks for: no motion of a mixed angle is proved, and
  III.16 and III.31, which compare at one vertex, need none. The coordinator approves the
  prototype, and its proofs stay in `Staging/Stage4b/MixedAngles.lean` until
  [issue #57](https://github.com/jackChallis/stoicheia/issues/57) decides their move into
  `Elements/`: once brief 0006's pull request lands, that is what
  [WORKFLOW](../WORKFLOW.md), section 2, "What proofs `Staging/` may hold", allows for the
  proofs of a prototype the coordinator has approved. The approval is of the prototype
  alone. The words it defines, the statements of III.16 and III.31 that would use them, and
  their records wait for #57, on the conditions of the report's section 5; nothing in
  `Elements/` changes.

- **The forbidden-command scan reads `Staging/` and `Audit/`, and knows `#eval`.** The
  security review of the Staging library noted two gaps in the source scan of
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py), `check_rules`, and we
  are grateful for the close reading
  ([#39](https://github.com/jackChallis/stoicheia/issues/39)). The scan read `Elements/`
  alone, so in `Staging/` and `Audit/`, which the certificate never reaches, "no axiom and
  no forbidden command" rested on review. And its list lacked `#eval`, which runs a
  program while a file is built: on Lean 4.35 an `#eval` can declare an axiom through
  `addDecl` with no `axiom` in the source, or write any file. Now the scan reads every
  `.lean` file under `Elements/`, `Staging/` and `Audit/`, and the roots `Elements.lean`,
  `Staging.lean` and `Audit.lean`. Its list gains `#eval`, `#exit`, `run_tac`, `by_elab`,
  `initialize`, `builtin_initialize`, and the attributes that stand behind `elab`, `macro`
  and `initialize`: `command_elab`, `term_elab`, `tactic` and `init`. It gains, too, every
  way Lean 4.35 has of evaluating natively and admitting the result as an axiom:
  `bv_decide` and `bv_check`, and `decide` with its `native` option, which
  `decide +zetaReduce +native`, `decide (native := Bool.true)` and a whole configuration,
  `(config := ⟨false, true, true, false⟩)`, set without the words the list had; so the
  word `native`, wherever it stands, and `(config := …)` are refused. `set_option debug.…`
  already covered `debug.skipKernelTC`, and with it `debug.byAsSorry`,
  `debug.proofAsSorry` and `debug.terminalTacticsAsSorry`. The source check for an axiom
  outside `Elements/Foundations/` now finds the word anywhere in a line, not only at its
  start: Lean reads `example : True := trivial axiom planted : False` as two commands, the
  second an axiom, which the old check missed (in `Elements/` the certificate caught it
  all the same). Each finding names its file and line. Nothing is loosened but the text of a
  literal (below): the scan refuses all else it refused before, in more places, and on main
  it refuses nothing.
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) gains test 8, which
  plants every forbidden command, and an axiom twice, once after another command on its
  line, in a new file of each of the three folders (Staging's in a folder of its own), and
  `#exit` at the end of each root, and expects each caught on its own line. origin/main's
  scan misses every one of them in `Staging/` and `Audit/`, and in `Elements/` the
  commands the list gains and the axiom after another command.
  [FORMALIZATION](../FORMALIZATION.md), section 7, the list's one home, names every
  command the scan refuses (`run_meta`, `elab_rules` and `macro_rules`, which it refused
  unnamed, among them), says why each is forbidden, and drops the known gap. The review of
  this branch found more routes the list lacked, and we thank it warmly: the simproc
  commands (`simproc`, `dsimproc`, `simproc_decl`, `dsimproc_decl` and their kin) and
  `set_library_suggestions`, whose code `simp` and the suggestion tactics run in the same
  file; attributes beyond `tactic` and `init` that register code Lean runs while a file is
  built or printed (`@[simproc]`, `@[doElem_elab]`, `@[grind_tactic]`, `@[delab]`,
  `@[app_unexpander]`, `@[quot_precheck]`, `@[cpass]`, `@[term_parser]`, `@[doc_role]`,
  `@[try_suggestion]` and others); and the escaped spelling `set_option «debug».…`, which
  Lean reads as `debug.…`. The scan now refuses these commands and the attributes whose
  names it lists, known by the end of the name or, for the `doc_` attributes, its start,
  and test 8 plants each command, ending and prefix in all three folders; again nothing is
  loosened. A later round of the review found two routes more, and we thank it for them
  too. With `doc.verso` on, Lean 4.35 reads a docstring as Verso and runs the Lean in its
  code blocks, an `#eval` among it, while the scan took docstrings out with the comments;
  and the handler `@[missing_docs_handler]` registers runs on every command of its kind.
  The scan now refuses `set_option doc.…`, spelled `doc.` or `«doc».`, so that every
  docstring stays inert, and, from a reading of Lean 4.35's attributes, those whose names
  end in `macro`, `check`, `handler`, `provider`, `fn`, `module`, `hooks` or `Attr`
  (`builtin_macro`, `package_code_quality_check`, `missing_docs_handler`,
  `code_action_provider`, `unused_variables_ignore_fn`, `widget_module`,
  `run_parser_attribute_hooks`, `simprocAttr`), and `builtin_doc` with the
  `builtin_doc_` attributes; test 8 plants each, and a Book Zero file that imports a
  proposition. The findings for `native_decide` and for Book Zero's imports, which named
  the file alone, now name the line as well, so every finding of the scan names its file
  and line. The last round found that the scan did not know Lean's string literals: on
  Lean 4.35 a `]` in a string ended an attribute's brackets early, so
  `@[deprecated "]" (since := …), tactic …]` registered a tactic unseen, and a `"/-"`
  opened a comment that hid the `#eval` after it. The scan now reads comments and string
  and character literals as Lean's tokenizer does, raw strings, escapes and the `{…}`
  holes of interpolated strings among them: a literal's text never opens or ends a
  comment, an attribute or a command, and the code in a hole is still read. A string
  whose braces Lean could read either as text or as holes of code, one not just after
  `s!`, `m!`, `f!` or `throwError` whose two readings end in different places, is
  refused, since the scan cannot tell which Lean will do. The one thing the scan now
  refuses less is a forbidden word inside a literal's text, which Lean never runs as
  code. Test 8 plants each disguise the review found, one behind a raw string and one
  behind a character literal, a command in an interpolated string's hole, and a string
  of the kind refused. A list of names trails the attributes each Lean release adds, so this one may
  not be complete, and review still reads every staged file and audit lemma. What would
  hold for good, an allowlist of the attributes the edition uses (main's Lean uses only
  `@[simp]` and `@[inherit_doc]`) or refusing imports from outside the project (each of
  the attribute and simproc routes needs an import of Lean's own modules, and on Lean
  4.35 `simproc` and `set_library_suggestions` fail without one; the docstring route
  needs none, and refusing the `doc.` options closes it), is left for the owner's
  decision. The
  protected files it changes are [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py) and
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py). The README's table of
  checks, and the name of CI's step for the negative tests, can follow in a pull request
  of their own.

- **The voice rules loosened, and `$…$` in "the modern way".** On 18 October, after
  Argon's second review of the book-III release, the owner decided, with thanks to Argon
  ([#70](https://github.com/jackChallis/stoicheia/issues/70)): drop the reports of length,
  paragraph count and bold leads; make "the modern way" optional; let the reading lines
  vary; allow `$…$` in "the modern way"; write angles in radians throughout; and give the
  letters one style in the text and in the figures. [STYLE](../STYLE.md) and its script
  change in stage 5, in a pull request of their own, with the `$…$` rendering checked on
  GitHub and a decisions entry naming each file it changes; the language and notation
  passes ([#46](https://github.com/jackChallis/stoicheia/issues/46),
  [#48](https://github.com/jackChallis/stoicheia/issues/48)) then rewrite the pages under
  the new rules. Until that pull request lands, STYLE's present rules hold.
- **The Lean notation, settled once before Book IV.** On 18 October, after the same
  review, the owner decided, with thanks to Argon
  ([#69](https://github.com/jackChallis/stoicheia/issues/69)): settle the notation in a
  short brief (keep, rename, or add readable notation) and apply it once, between the
  consolidation release and Book IV, so that the records of Books I to III are re-stamped
  once. Argon's examples: `‖A B‖` reads as a norm; `△ A B C` is an area while
  `Triangle A B C` says that the points are not in line; `circumference` and `standing`
  take their arguments in different orders; circles are named `ABCD` beside points A, B,
  C, D; and Euclid's straight line C is written as points `C₁ C₂`. The old names stay as
  deprecated aliases for one release, so that nobody's code breaks without warning, and
  [FORMALIZATION](../FORMALIZATION.md)'s vocabulary changes with them.
- **The reviews of 18 October, approved for publication, with responses.** On 18 October
  the owner approved `docs/reports/outside-review-02.md`
  ([#71](https://github.com/jackChallis/stoicheia/issues/71)): Astra's two answers, Argon's
  two reviews of the book-III release, and a cold Claude review with its scorecard and ten
  fixes. Each reviewer is credited warmly, each finding is answered with its issue or pull
  request, and a claim that does not hold is answered plainly and politely. It is merged
  after the owner has read it, with every response linking a real issue or pull request.
- **Every circle has a centre: approved, to land after #40 and brief 0008.** On 18
  October, after Astra's third answer
  ([#59](https://github.com/jackChallis/stoicheia/issues/59)), the owner decided, with
  warm thanks to Astra: "approved, as Astra recommends.
  `axiom exists_centre (α : Circle) : ∃ O, Centre O α`; III.1 keeps its
  construction-rich conclusion and drops the existence hypothesis, with a circle-only
  entry point for users; the statements that only assume a centre exists drop that
  hypothesis, those that name the centre keep it; III.1 gains an overlap note for bare
  existence; its page says the foundations assume a centre and the proposition proves
  that Euclid's construction finds it." Uniqueness keeps its own axiom, `centre_unique`.
  The rule is a real addition, not a restatement: Astra's hand argument adds to the plane
  one circle with no centre, and every present law still holds there, on the laws'
  intended plane reading (a hand argument, not yet a Lean countermodel); and System E
  itself allows a circle to be given without its centre (§4.2). III.1's conclusion stays
  the centre F found by bisecting the perpendicular chord, with the bisections and the
  perpendicular it certifies, and the entry point beside it takes only the circle and
  chooses two points on it. A centre that a statement names stays, since the existence of
  some centre does not identify the point named; and the existential centre clauses
  inside definitions such as `EqualCircles` stay, since their witnesses compare the radii.
  III.1's overlap note says that the rule assumes bare centre existence and that the
  construction goes beyond it, and its page says, in Astra's words: "Our foundations
  assume that every circle has a centre. This proposition proves that Euclid's
  construction finds it: bisecting the perpendicular chord gives the centre F." The tag
  `centre-given` is retired where it only explained the missing rule; any other
  restriction a record carries stays. The owner set the order: "#40 first (a new axiom
  needs the model's law names pinned as data), then a short brief with every statement
  changed, challenged and frozen, then the axiom with its lock entry, model law and
  decisions entry, then the restatements and their records." The law names #40 pins are
  those of `tests/model`, and the short brief is brief 0008. Nothing lands yet: the axiom
  comes only in the coordinator's own pull request, in that order, and until then the
  hypothesis stays, disclosed as now.
- **Superposition: a restricted rule prototyped now, our rule disclosed meanwhile.** On 18
  October, after Astra's third answer
  ([#75](https://github.com/jackChallis/stoicheia/issues/75)), the owner decided, with
  thanks to Astra: "prototype now, disclose meanwhile, as Astra recommends. A design brief
  and a Staging prototype of a genuinely restricted rule (a checked inference over
  represented derivations, with I.4 and I.8 proved from it, a restriction theorem, and the
  model's justification). It lands before the consolidation release only if all of that
  is complete; the owner decides then. Meanwhile the overlap catalogue and the I.4 and I.8
  pages say plainly that our rule is stronger, as a construction principle, than System
  E's restricted inference." The limit to I.4 and I.8 controls where
  `Tacit.superposition` is used, not its strength: it returns the placed corners as
  points. Astra checked in Lean that the tempting replacements, a continuation into any
  proposition or into conclusions with no fresh points, give back the existential rule,
  the second by way of classical logic; so the prototype's inference ranges over
  explicitly represented geometric formulas and derivations, in which a hypothetical
  placement proves facts about the triangles already given and never returns its corners
  as constructed points. Complete means, as Astra set it out: the checked inference
  itself; I.4 and I.8 proved from it, with their statements and Euclid's coincidence
  arguments; a restriction theorem, that the represented derivations cannot export a
  placed corner or construct inside the restricted branch; and the model's justification
  of the rule, reflections included. A claim that I.2, I.3 or I.23 no longer follow from
  the rule, if one is made, is scoped to a stated fragment of the rules and proved, not
  read off a failed compilation. Until then the edition says, in Astra's words: "Our
  superposition axiom asserts that a congruent triangle can be placed on a given ray and
  side. The edition permits its direct use only in I.4 and I.8. This axiom is stronger as
  a construction principle than System E's restricted inference rule." Its home is the
  module docstring of
  [`Elements/Foundations/Tacit/Superposition.lean`](../../Elements/Foundations/Tacit/Superposition.lean),
  where it replaces the sentence that the checks' limit respects System E's restriction;
  the axiom, its statement and the lock are unchanged, and the docstring keeps its length,
  so the pages' links to the axiom's line still hold. The I.4 and I.8 pages, the I.23
  section of [the overlap catalogue](../reports/overlaps.md#i23), Book I's introduction,
  the README, [FORMALIZATION](../FORMALIZATION.md), section 3, and
  [Book I's brief](book-I.md) point to it.
- **The formal model: begun now, in `model/`.** On 18 October, after Astra's third answer
  ([#73](https://github.com/jackChallis/stoicheia/issues/73)), the owner decided, with
  thanks to Astra: "start now, in `model/`, as Astra recommends. A Lake package of its own
  inside this repository, with a pinned Mathlib and a required CI job once it builds; the
  main library stays plain Lean. A separate parameterized signature and laws generated
  from the elaborated declarations, with translation checks; the hardest laws prototyped
  first (circle intersections, angle transfer, Postulate 5, superposition, areas, finite
  avoidance); the hyperbolic model afterwards. MODEL.md's conclusions are softened now, to
  say what the evidence is until the proof is complete." The package lands in a pull
  request of its own; until it does, the pages speak of `model/` as being built. The
  translation checks are Astra's: specialized back to the original words, each law must
  be exactly the locked statement, no word of the project may stay untranslated, and the
  vocabulary is pinned with the statements. The signature carries the magnitudes'
  carriers, zero, addition and order among them, and the plane is
  `EuclideanSpace ℝ (Fin 2)`; the proofs of Books I to III are unchanged, and no axiom of
  the project and no `sorryAx` may lie beneath the model's proofs. Until the model is
  complete, the edition claims what Astra gave: "The axioms have an informal
  interpretation in the ordinary plane, supported by numerical and exact finite tests. A
  kernel-checked proof that this interpretation satisfies every locked law is in
  progress." So [`tests/model/MODEL.md`](../../tests/model/MODEL.md), a protected file,
  softens to that claim the conclusions of its hyperbolic section, of its milestone
  section, now "A formal model: in progress", and of "What this shows, and what it does
  not", and says plainly that numerical tests establish neither consistency nor
  non-derivability; the README's table of checks and [FORMALIZATION](../FORMALIZATION.md),
  sections 3 and 9, follow, and [PROGRAM.md](../PROGRAM.md)'s link to the milestone moves
  with its heading.
  A release made before the model is complete names the milestone as incomplete, as Astra
  advised. This supersedes "a later milestone" in the 17 October entry "The model harness
  lives in the repository".
- **The case a figure shows, said under it.** Argon's second review found that the
  `[figure] case` of a review record, which eleven records give, was never printed, so a
  figure drawn for one case of several did not say so on its page; we thank Argon warmly for
  reading the renderer and the records side by side.
  [`scripts/render.py`](../../scripts/render.py) now prints it under Euclid's figure, before
  the figure note, and in the figure's alternative text: "Drawn for one case: the bases BC and
  CE meeting at C, as in Heath's figure." That is what
  [review/SCHEMA.md](../../review/SCHEMA.md) already says of the key ("The caption names it")
  and what [STYLE](../STYLE.md), section 7, asks of a figure drawn for one case. The
  alternative text of both figures also writes a double quotation mark as `&quot;`, so that
  a record's or a caption's words cannot end the attribute early; none has one today. It
  changes what render.py writes and nothing it accepts or checks, so it is not a check change
  ([WORKFLOW](../WORKFLOW.md), section 10); the regenerated pages of I.30, I.35 to I.38,
  I.40, I.41, II.5, II.9, II.14 and III.6 show it, and no other page changes. The one
  protected file it changes is
  `scripts/render.py` ([#30](https://github.com/jackChallis/stoicheia/issues/30)).
- **An axiom lands with its law: the model's law names, a pinned value.** Under the rule
  that keeps a check change apart from what it checks, a change of axioms could land in no
  order ([#40](https://github.com/jackChallis/stoicheia/issues/40)): the model's law names
  lived in its code, so a pull request moving the lock, its hash and the law together was
  a check change made with content, and a law landed first would name an axiom the lock
  did not hold. The names move into a data file,
  [`tests/model/laws.toml`](../../tests/model/laws.toml): a line for each axiom, under the
  lock's name, with the name of its law in the harness, and the laws that must fail in the
  hyperbolic plane (Postulate 5), which
  [`tests/model/hyperbolic.py`](../../tests/model/hyperbolic.py) and
  [`tests/model/run.py`](../../tests/model/run.py) now read from it, through `read_laws`
  in [`tests/model/model.py`](../../tests/model/model.py). Before anything runs, `run.py`
  checks the file against the axiom lock and against `facts.json` in both directions, and
  `search.py` and `hyperbolic.py` against it; `run.py --ties` runs those checks alone, in
  a second; and a law that a program reports twice, or a program that stops before its
  last line, now fails the run. The number of axioms is no value of the harness, which
  takes it from the lock, so nothing else had to move; the docstrings that named 87 and 86
  now name no number.
  [`scripts/safe_push.py`](../../scripts/safe_push.py) counts the file as a value pinned
  to the edition, beside `Certificate/axioms.lock` and
  [`tests/model/lock.sha256`](../../tests/model/lock.sha256), while each line it changes
  moves with its axiom: the same pull request adds, removes or restates that axiom's entry
  in the lock. A law's code in `tests/model/search.py` and `tests/model/hyperbolic.py`,
  the two programs that check every law, moves the same way, while it keeps to itself (a
  function `_` under its one decorator `@axiom('<name>', …)`, using only what an
  allow-list names, below, and changing no container but one it made in its own body,
  through the name it gave it) and nothing else in the file changes but comments and its
  docstring. The model's account, [`tests/model/MODEL.md`](../../tests/model/MODEL.md)
  and `tests/model/results/`, which no check reads, moves with its content as well. A law
  changed while its axiom stands, a helper or tolerance of the harness, and every other
  change to the checks are kept apart as before.
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) plants an
  axiom added with its entry in the lock, the new hash, its line of `laws.toml`, its law's
  code in both programs and a line of MODEL.md: it lands as content, and the model's ties
  hold on it. With another law loosened beside it, the same change is kept apart, and a
  table of twenty-five loosenings and five moves checks each way round. An axiom removed
  or restated moves the same way when no other program names its law. `structured.py` and
  `exhaustive.py` run some laws by name, so they must drop or re-key such a law first, in
  a pull request of its own. The independent verifier of the change found two gaps, and
  we thank them for it: a new law could change a shared container under a second name
  (`d = DEN`, then `d[:] = [2]`), and a missing laws.toml or lock gave a traceback before
  Python 3.14, not the refusal. A law now changes a container only through a name that
  every binding in it gives a container it made itself, and a missing file reads as
  nothing; each has its tests. The no-mistakes review found a third, and we thank it too:
  a law could end the structured run early with `SystemExit(0)`, and the run still passed,
  so each program that runs the laws must now reach its last line, and a test holds it
  there; and as it found that a law could forge that line through `help`, the pre-flight
  refused the builtins that print or end a run.
  Then the change's independent reviewer found that the check was still a deny-list, which
  reflection escaped, and we thank them for it: a frame's globals, say, or `random._os`,
  through which a law could coarsen the decimal context every law of the hyperbolic plane
  computes in, or print a forged result. As every change to a law was kept apart before,
  the change as it stood weakened that rule against a determined bypass. So the check
  (`self_contained` in `scripts/safe_push.py`) is now an allow-list, sound by
  construction: a law's code may use its own parameters and the names it binds; by name,
  and each in one role, the helpers of its program that the 87 laws call, and the
  builtins, `math` functions, table (`SEEDS`), value (`RA`) and attributes they use
  (`append`, on a container of its own, and the draws of the random numbers it is handed,
  never a reseeding); and plain syntax, with no import, `global`, `lambda`, `try`, `with`,
  class or default argument. What the list does not name is refused, so a route nobody
  thought of is refused too. The lists are collected from the laws: every law passes, a
  test shows that each entry is one some law needs, and each route the reviewer named has
  its test; widening a list is a check change, in a pull request of its own. One thing a
  law still shares with the laws after it is the random numbers: how many it draws moves
  which configurations they see, never what they check. MODEL.md, "Changing the axioms",
  is now the one home of the steps for changing an axiom, or a word of the lock, and the
  comment in `tests/model/lock.sha256`, [FORMALIZATION](../FORMALIZATION.md), section 7,
  the [orders](../templates/orders.md) and [brief 0006](0006-statements.md) point to it;
  [WORKFLOW](../WORKFLOW.md), section 10, step 4, gives the rule for landing them. Adding
  an axiom stays the owner's decision: this lets one land, and adds none.
- **The voice rules loosened, and `$…$` in the modern way: the check change.** The owner's
  decisions of 18 October, after Argon's second review of the book-III release, as
  [#70](https://github.com/jackChallis/stoicheia/issues/70) records them: "drop the
  length, paragraph-count and bold-lead reports; make 'the modern way' optional; let
  reading lines vary; allow `$…$` in 'the modern way'; radians throughout; one style for
  letters in text and figures"; and as
  [#48](https://github.com/jackChallis/stoicheia/issues/48) records them: "S10 is relaxed
  so that 'the modern way' may use `$…$` (III.20 can then write $e^{i\theta}$); angles
  are in radians throughout …; letters take one style in text and figures, written once
  in STYLE". Our warm thanks to Argon, whose counts across the 99 pages showed what the
  quotas had done. [STYLE](../STYLE.md) writes the new rules once (sections 3, 4, 6, 7 and
  8), and the table of defaults in [AGENTS.md](../../AGENTS.md) follows it. The one
  protected file changed is [`scripts/check_style.py`](../../scripts/check_style.py), and
  this, exactly, is loosened:
  - the reports D1 (a mishnah outside 250–450 words), D2 (fewer than three or more than
    five paragraphs, or one over 120 words) and D3 (a paragraph without a bold lead, or a
    last paragraph not "The modern way") are removed: a mishnah has no count, its leads are
    optional, and so is "the modern way";
  - the report D13 (a reading line not beginning "For ") is removed: a line gives the same
    facts in its own words and order. S17, which fails a reading file's shape and links,
    is unchanged;
  - S10 lets TeX stand within `$…$` in a paragraph that opens `**The modern way.**`, and
    nowhere else: TeX outside those spans, in that paragraph or in any other, fails as
    before. The paragraph ends where Markdown ends it: at a blank line, or at a line that
    opens a heading, a list item (a numbered list only from 1), a quotation, a code fence,
    an HTML block, a rule or a table; a line that only looks like one, such as `|z| is one`,
    goes on with it. Within it, S10 refuses the shapes of span known to break on GitHub. Its
    renderer, tried with sample spans on 18 October, needs the dollars paired within the
    paragraph, never `$$`; one line, no white space just inside a dollar; the opening
    dollar at a line's start or after white space or "(", the closing one before white
    space, a line's end or a punctuation mark; balanced braces; no backslash before an
    ASCII punctuation mark, which GitHub's Markdown removes; and no `<`, `>` or `&`, which
    it escapes twice. Those lost backslashes show that GitHub's Markdown reads inside a
    span, and by CommonMark's rules for emphasis, checked with a CommonMark parser and not
    tried on GitHub, a `*`, or a `_` after anything but a letter or a digit, pairs with
    another across two spans: so a span holds no `*`, `~` or backtick, and a `_` only
    straight after a letter or a digit. A shape not yet found may still break, and the
    reviewer's checklist (STYLE, section 8, item 5), which sees each span rendered on
    GitHub, stays the guard. Before anything else, the script's self-check reads 44 sample
    mishnahs, twelve on the allowed side and thirty-two refused, among them TeX outside
    the dollars in the modern way, `$…$` in another paragraph or in a list item, heading,
    quotation or table just under the modern way, `$…$` on a wrapped line that only looks
    like one, and each malformed span;
  - S20, which held the letters of a figure at a glance italic, now holds them upright, and
    S15 holds Euclid's figures to the same (it read no style before); the owner's "one
    style" is read as upright, the style the text already has (S9) and the only one the
    Lean can show, since Heath's sentences stand on every page as `--` lines in a code
    block. While the figures are set upright, in a change of their own, the new switch
    `UPRIGHT_LETTERS_REQUIRED` is `False`: a figure's letters may all be italic, as every
    figure's are now, or all upright, never mixed, and a new report, D15, lists the
    figures still italic. The switch is turned on once every figure is upright, and never
    turned back to quiet a figure.

  Nothing else is loosened: every other rule reads what it read. Radians, and upright
  letters within a formula (`$\mathrm{A}$`), are rules of STYLE, section 4, for a reader
  to judge; no check reads them. GitHub renders `$…$`: III.20's modern way, rewritten with
  `$e^{i\beta}$` and `$\frac{\mathrm{C} - \mathrm{A}}{\mathrm{B} - \mathrm{A}}$` (a trial,
  not committed), passed S10, went onto `book/III/20.md` through `scripts/render.py`
  byte for byte, and GitHub's Markdown API set each of its spans as mathematics with the
  TeX intact. This supersedes the line "usually 250–450 words, with reasons for
  exceptions" in stage 1b of [brief 0005](0005-astra-review.md). The pages are rewritten
  under the new rules by #46 and #48.
- **Stage 2 in the edition: brief 0006's words in the foundations, the axiom lock's
  vocabulary grown.** Every statement of stage 2 of [brief 0006](0006-statements.md) is
  proved, and moves from `Staging/` to its home in that brief's table, in a move the
  coordinator delegated to the stage's integrator. The definitions they use are approved for
  the foundations as a class: the owner's call, as the tracking issue
  ([#50](https://github.com/jackChallis/stoicheia/issues/50)) records it, is that "the
  definitions the frozen briefs name are approved for the foundations, each recorded in its
  pull request" (decision 4 of brief 0006). This entry records the ones this pull request
  moves, each as the brief froze it: `Magnitude.sum`, into
  `Elements/Foundations/Magnitudes.lean`; and `InOrder`, `segments`, `endOf`,
  `OnFiniteLine`, `OnOrInsideTriangle`, `Corners`, `triples`, `Fitted` with its two
  constructors, `Rectilineal`, `Rectilineal.area`, `Apart` and `Apart.area`, into
  `Elements/Foundations/Phrases.lean`. None is an assumption. Their facts go to Book Zero,
  in two new files that `Basics.lean` gathers, `Elements/Figure/Sums.lean` and
  `Elements/Figure/Rectilineal.lean`; the bridge `Fitted.fan`, whose proof cites I.13, goes to
  `Elements/BookI/Prop45.lean`, before `Prop45.fan`, as the brief provides. The sixteen
  companions of I.40, I.45, II.1 and II.14 move beside their propositions and join
  `Elements/Companions.lean`; the statements of I.40, I.45, II.1 and II.14 themselves do not
  change. `Staging/Stage2/` is gone, and `Staging.lean` says so. The routes as proved are
  those the brief declares, save one detail of a plan: `InOrder.between_end` uses Between 5
  (`between_of_between_right`), where the brief names Between 6 and Diagram-segment 1. The
  protected files this changes are three. [`Certificate/axioms.lock`](../../Certificate/axioms.lock)
  is rewritten by `python3 scripts/check_fidelity.py --write-lock`: its `[axioms]` table is the
  same 87, byte for byte, and its `[vocabulary]` grows from 61 words to 91, by the words above
  and what Lean declares for them, each structure's constructor and the projection the
  companions use (`Apart.mk`, `Apart.pieces`, `Rectilineal.mk`, `Rectilineal.pieces`), and
  the auxiliary declarations of the five definitions by recursion (`._f`, `.match_1` and
  `segments._sparseCasesOn_1`). [`tests/model/lock.sha256`](../../tests/model/lock.sha256) is
  renewed, and [MODEL.md](../../tests/model/MODEL.md) read again: no axiom, and no word an
  axiom reaches, has changed, so its account stands, and `tests/model/run.py --fast` passes.
  [`review/terms.toml`](../../review/terms.toml) gains the tag `figure-with-dissection`, of
  kind `representation`, word for word as brief 0006 gives it, before the records of I.45 and
  II.14 use it. Those records, with I.40's and II.1's, become `full` by their companions,
  and wait for their reviewer's reading and stamp; the tags `adjacent-bases`, `two-triangles`
  and `three-pieces` stay in the file, though no record carries them now.
- **The certificate keeps a proof's own axioms apart from those it inherits.** Argon's
  second review of the book-III release found that `direct_axioms` lists, as a
  proposition's own, every axiom its proof term names together with those of the Book
  Zero lemmas and shared steps it calls, so that a reader asking which rules a proof calls
  got a longer list than the proof's own; we thank Argon for it
  ([#65](https://github.com/jackChallis/stoicheia/issues/65)).
  [`Certificate/Facts.lean`](../../Certificate/Facts.lean) now writes two more fields for
  every entry: `own_axioms`, the axioms named in the proof's own declarations (the
  declaration, the helpers in its proposition's namespace, and Lean's auxiliary
  declarations), and `inherited`, each other axiom it uses itself with every lemma, of
  Book Zero or shared, that brings it in. A second self-check joins the first: the run
  fails unless an entry's `direct_axioms`, Lean's foundations aside, are exactly its
  `own_axioms` and its inherited axioms, so that its `axioms` are still exactly its own,
  those it inherits, its Common Notions' and those of what it cites. Every field that was
  there before is byte for byte as it was, `direct_axioms` among them, and the policy on
  superposition still reads it, so no proof may reach that rule through a lemma either.
  [`Certificate/FIELDS.md`](../../Certificate/FIELDS.md) documents both fields.
  [`scripts/render.py`](../../scripts/render.py) shows them: each page's table gains the
  rows "Its own Lean calls" and "Through lemmas", and its list of tacit rules marks a
  rule "(used here)" only when the proof's own Lean calls it, and otherwise names the
  lemmas it comes in through; CERTIFICATE.md gains the columns "Own rules (all kinds)"
  and "Through lemmas (all kinds)". That is a change to what it writes, which the
  regenerated pages show, and not to what it accepts.
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py) reads a field of
  `tests/certificate_expectations.json` that is an object, as `inherited` is, by its
  keys, and fails an expectation whose entry lacks its field, which it read as empty
  before, so that an `excludes` could pass on a field that had gone. Both are stricter,
  and nothing is loosened.
  [`tests/certificate_expectations.json`](../../tests/certificate_expectations.json) keeps
  its four expectations and gains five: III.2 rests on Circle 2 (`inside_of_between`),
  which neither its own Lean nor any lemma it calls brings in, so it comes only through
  III.1; and I.5's own Lean never calls Postulate 3, which it inherits through Book Zero's
  `exists_between_nearer`. The protected files this changes are `Certificate/Facts.lean`,
  `Certificate/FIELDS.md`, `scripts/render.py`, `scripts/check_fidelity.py` and
  `tests/certificate_expectations.json`. The overlap catalogue's "First enters" moves to
  the new fields in a text pull request of its own, after this one.
- **The style check's cases, in `tests/`.** The cases with which
  [`scripts/check_style.py`](../../scripts/check_style.py) checked its own reading, on
  every run and before anything else, move to a test file of their own,
  [`tests/test_check_style.py`](../../tests/test_check_style.py) (new). This settles
  [issue #44](https://github.com/jackChallis/stoicheia/issues/44), the question that
  [#3](https://github.com/jackChallis/stoicheia/pull/3) left open. They are the 44 phrase
  cases, each wording rule's phrases wrapped and unwrapped, and S20's 11 ink cases, each
  read with three spellings of an angle's wedge, 33 in all. Every case moves as it was,
  its rule, its search, its text and its expected finding the same and in the same order,
  and none is added or dropped: compared with origin/main's copy, they are identical one
  for one, and the file fails when D7's pattern stops wrapping, when S3 passes over an "I"
  after "Book" across a tab or a line break, or when S20 stops reading paths. The home is
  the one [WORKFLOW](../WORKFLOW.md), section 8, gives a guard's regression, and that
  section now names the file: a defect fixed in the style check's reading of a phrase or
  of a letter's ink comes with a case there. WORKFLOW asks for no start-up self-check, so
  the script's is removed. In CI and in the pre-flight nothing runs less often: the file
  needs no Lean and runs in well under a second, so it stands where the cases ran before,
  just before `check_style.py`, in CI's `check` job
  ([`.github/workflows/ci.yml`](../../.github/workflows/ci.yml), a step of its own), in
  the `CHECKS` list of [`scripts/safe_push.py`](../../scripts/safe_push.py), and in the
  sequence of WORKFLOW, section 8, and a case read wrongly stops the checks before the
  style check's findings are read, as the self-check did. A contributor who runs
  `check_style.py` alone no longer runs the cases, so WORKFLOW asks whoever changes the
  script to run the file too. The check is moved, never weakened. The script's docstring
  and [STYLE](../STYLE.md), section 8, say where the cases are.
- **The formal model, begun in `model/`.** The owner decided on 18 October, after Astra's
  third answer on [issue #73](https://github.com/jackChallis/stoicheia/issues/73), for
  which we thank Astra warmly
  ([the decision](https://github.com/jackChallis/stoicheia/issues/73#issuecomment-6253675685)):

  > **The owner's decision (18 October): start now, in `model/`, as Astra recommends.** A
  > Lake package of its own inside this repository, with a pinned Mathlib and a required CI
  > job once it builds; the main library stays plain Lean. A separate parameterized
  > signature and laws generated from the elaborated declarations, with translation checks;
  > the hardest laws prototyped first (circle intersections, angle transfer, Postulate 5,
  > superposition, areas, finite avoidance); the hyperbolic model afterwards. MODEL.md's
  > conclusions are softened now, to say what the evidence is until the proof is complete.

  The package adds, all under `model/`: its Lake files (`lakefile.toml`, with Mathlib
  pinned to `v4.35.0`, `lake-manifest.json`, `lean-toolchain` and `.gitignore`); the
  library `Model` (`Model.lean`, and under `Model/` the files `Signature.lean`,
  `Hand.lean`, `Euclidean.lean`, `Euclidean/Circles.lean`, `Euclidean/CircleSides.lean`,
  `Euclidean/Magnitudes.lean`, `Euclidean/Centre.lean` and `Audit.lean`); the library
  `Check` (`Check.lean` and `Check/Hand.lean`); `lock.sha256`, the hash of
  `Certificate/axioms.lock` the model was last checked against; and
  [`model/README.md`](../../model/README.md), which says what each file holds and where
  the work stands: 12 of the 87 laws proved in the plane so far, and the proposed
  `exists_centre`. Its proofs stand on Mathlib, and the README thanks those whose work
  the plane's readings use. Outside `model/`, only CI and this page change: the main
  package depends on nothing in `model/`, and its `lakefile.toml` and `lake-manifest.json`
  are unchanged, so `lake build` at the root never sees Mathlib. Softening MODEL.md's
  conclusions, as the decision asks, is a change of its own:
  [`tests/model/MODEL.md`](../../tests/model/MODEL.md) is unchanged here. The CI job is a
  new job, `formal-model`, in
  [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml); its id is not `model`,
  which is the numerical harness's. After installing elan, it checks `model/lock.sha256`
  against the lock, restores `model/.lake/packages` and `~/.cache/mathlib` from a cache
  keyed on `model/lake-manifest.json`, and runs `lake exe cache get` and `lake build` in
  `model/`, stopping after 30 minutes. It is not yet a required check: `REQUIRED_CHECKS`
  in [`scripts/safe_push.py`](../../scripts/safe_push.py) and the ruleset on main still
  name `check`, `model` and `negative`, and making `formal-model` required, as the
  decision foresees once it builds, is the owner's call. Even so, `git safe-push --merge`
  refuses a pull request while any of its checks fails or is still running, so a red or
  running `formal-model` already holds a merge there.
- **Pages name what follows a theorem truly.** [`scripts/render.py`](../../scripts/render.py)
  called every declaration after a theorem that is neither its porism nor a companion one
  of the "theorems later propositions use". With stage 2's companions in the edition, that
  would have covered `Fitted.fan`'s fourteen helpers on I.45's page and
  `Prop14.area_pos` on II.14's, which no later proposition uses. The listing now names
  three kinds: a declaration that another Lean file of the edition uses is one of the
  "theorems later propositions use"; one that only other declarations of its own file use
  is a "lemma for its own proofs"; and one that nothing uses, as III.17's `Prop17.inside`
  will be (brief 0007), is "a lemma beside the proposition". A use is read from the Lean
  with its comments taken out, so a name in a comment or a docstring is no use. Clauses
  that hold lists are parted by semicolons. The Proof row names first the porism and the
  companions that share the proposition's status, the companions together in the order
  the review record lists them, and then each whose status differs. The page generator
  checks its reading of uses against cases of its own before it renders anything; no page
  on main changes, since every such label there is true (#94, found in the review of
  brief 0007 and of stage 2's move).
- **Trains: reviewed branches land together.** Landing one pull request at a time cost
  about ten minutes each, since the ruleset and safe_push require every pull request to be
  up to date with main, and almost every one touches the decisions page and the generated
  pages; twenty reviewed branches waited. On the owner's word ("It feels like we are
  solving problems serially ... Map out a PR strategy. And for those that can run in
  parallel run them that way"), and his approval of the plan that proposed them, branches
  now land in trains: one branch merging several reviewed branches, each a merge commit of
  its own, with one pre-flight, one CI run and one merge ([WORKFLOW](../WORKFLOW.md),
  section 10, "Trains"). Nothing in the checks changes: a train is an ordinary branch to
  safe_push, keep_apart still holds within it, and strict status checks stay on.
- **A representation tag for a figure given with its triangles.**
  [`review/terms.toml`](../../review/terms.toml) gains `figure-with-dissection`, which brief
  0006 froze, so that the records of I.45 and II.14 can name how their figure is given
  (any division into triangles that lie apart; a figure with one boundary, its triangles
  glued edge to edge; or Euclid's and Byrne's triangles from one corner), and that every
  figure can be so divided and another division gives the same sum are not proved here.
  It lands on its own, before the records that use it, since safe_push keeps a check's
  data apart from the content it judges (#19).
- **The restricted superposition prototype, in Staging.** The coordinator approves that
  the prototype of #75 (brief [0009](0009-superposition.md), round 2: a finite symbolic
  context with a valuation, the restricted rule carried as a hypothesis, I.4's and I.8's
  conclusions proved from it) keeps its proofs in `Staging/Superposition/`, as WORKFLOW
  section 2 allows an approved prototype, under the names `Elements.Superposition.Prop4`
  and `Prop8`, which say plainly that these are not the edition's I.4 and I.8. No axiom is
  added; the edition's superposition rule is unchanged, and it lands only when the
  evidence brief 0009 asks for is complete (the owner's decision on #75).
- **The formal model's lock hash renewed with stage 2's words.** Stage 2's move adds
  words that only the statements of companions use, so `model/lock.sha256` is renewed
  with `tests/model/lock.sha256`, as its own comment says; no law of the model changes.
- **The style rules' new cases live with the others.** When the owner's style decision
  (#70) met the move of check_style's cases into a test (#44), its new cases for S10's
  boundary (`$…$` allowed in "the modern way", TeX refused elsewhere, delimiters balanced)
  joined the phrase and ink cases in
  [`tests/test_check_style.py`](../../tests/test_check_style.py); every case of both is
  kept (44 phrase, 44 S10 and 33 ink cases), none weakened.
- **An overlap is worded by its kind, as the catalogue gives it.** A record's
  `[overlap]` may now name the kind of its row in the
  [overlap catalogue](../reports/overlaps.md), `kind = "states"`, `"gives"` or `"step"`,
  as [`review/SCHEMA.md`](../../review/SCHEMA.md) defines.
  [`scripts/heath.py`](../../scripts/heath.py) accepts only those three, and asks of a
  step a `note` saying which step, in which proof (brief 0008, question 3); its self-test
  puts both rules to records of its own. [`scripts/render.py`](../../scripts/render.py)
  words by the kind the line under the enunciation and the book's summary, which also
  heads the book's index, its section of CERTIFICATE.md and its row of README.md: a rule
  that states the proposition or gives it at once "contains" it, as before, and a rule
  that supplies a step "supplies a step of a proof of it", with whether our proof rests
  on the rule. The pages said that superposition and Circle 4 contain I.2, I.3, I.7 and
  I.23, where the catalogue says only that each supplies a step, in an audit lemma that
  takes seven axioms or more; so the words are "a proof of it", not "its proof", since our
  own proofs of I.2, I.3 and I.7 never use the rule, and I.23's never calls it, resting on
  it only through I.8 and I.20, which it cites (#93, found in the review of the Circle 2
  branch, #87). Astra's probe in the
  challenge of brief 0008 showed that both displays had to read the key, and we are
  grateful. The key is optional so that this check lands first, on its own: a record
  that names no kind is worded as before, so no page changes here, and the records name
  their kinds after it, in a pull request of their own.

- **A table of names, so the library is easy to use.**
  [`scripts/render.py`](../../scripts/render.py) changes what it writes and nothing it
  accepts or checks: it now writes `book/names.md`, every proposition, porism and companion
  of every book with its Lean name, the module that declares it, its page and its
  certificate, read from `facts.json` and the proposition files, so that a Lean user who
  knows Euclid's number finds the name, and a reader of the Lean finds the page
  ([issue #76](https://github.com/jackChallis/stoicheia/issues/76), the owner's: "easy for
  others to use as it stands"). It is not a check change (WORKFLOW, section 10): the
  regenerated page shows it, and it stands under `book/`, which the check that the pages
  are current already reads. The README usage guide, naming and deprecation policy,
  and links to the table follow separately (keep_apart). Generated API documentation
  (doc-gen4, in CI) comes in a change of its own, and nothing of it is published without
  the owner's OK.
- **Using the library and keeping its names.** The table of names lands first;
  its guide and links follow separately (keep_apart). The README gains "Use it": the `require` for a
  `lakefile.toml`, pinned to the release tag `book-III`, its one-line form for a
  `lakefile.lean`, and a short example, each built in a fresh project against the tag on
  18 October; and, for a project that already has a `lake-manifest.json`,
  `lake update stoicheia` first, since Lake 4.35's `lake build` does not add a new
  dependency to a manifest that exists. FORMALIZATION, section 2, gains "Names, and how they change": how names are
  made; a released name never renamed or removed without a deprecated alias for one
  release; a changed statement keeping its proposition's name, with the old one kept as a
  companion where citers need it; and the release notes listing every name deprecated and
  every statement changed.
- **The Jev audit's client.** Brief 0005's stage 6 asks for an
  independent audit by Jev, TypeSafe's decision model, through a fresh client
  ([#36](https://github.com/jackChallis/stoicheia/issues/36)).
  [`scripts/audit/jev.py`](../../scripts/audit/jev.py) (new) is that client, written for
  Stoicheia from TypeSafe's public documentation; we thank TypeSafe warmly for Jev, and for
  documentation clear enough to build from. It uses the standard library alone. It runs
  the model preflight, then one decision request for each row of a JSON Lines file, with
  retries off, a timeout, no redirect followed and HTTPS only, and writes one line for each
  row: the choice, every option's probability, Jev's confidence, the model that answered,
  the latency, the tokens used and the SHA-256 of the body sent. Each run pins a versioned
  model id (`jev-1.13.0` by default) and refuses an alias unless told otherwise. Each choice
  is asked a second time in the same request with its options reversed, since TypeSafe's
  notes on Jev 1.13 say it can lean toward the option that comes first. The key is read
  only from the file that `STOICHEIA_JEV_KEY_FILE` names, outside the repository; it is
  never printed, logged or written, and it is redacted from anything the service echoes.
  Only a row's state, question and images are sent, never its expected answer. A dry run
  prints every request and reads no key; `--resume` takes up a stopped run, sending only
  the rows not yet answered; `score` lists what goes to the adjudicator (a disagreement, a
  confidence under 0.5 or none given, an answer that moves when its options are reversed
  or comes from another model than the one pinned); and `self-test` runs every command
  against a stand-in for the service on the same machine, with no network and no key. The
  calibration set follows in a separate change, keeping the client apart from the
  content it judges (keep_apart). The client's self-test needs that set. The protected file it adds is `scripts/audit/jev.py`. No
  request has been sent yet; the accuracy bar Jev must meet on the set is the
  coordinator's to state before the first run, and `score --bar` counts it met only when
  every row of the set is answered and no request failed.
- **The acceptance checker ([#35](https://github.com/jackChallis/stoicheia/issues/35)).**
  [`scripts/check_acceptance.py`](../../scripts/check_acceptance.py) (new) checks every
  [machine] item of the acceptance checklist across the 99 propositions, each book and the
  edition, reads every [review] item from the review records, and writes a report with
  every failure listed; it changes no other file and reuses the checks already in place.
  It is not yet a step of CI or of safe_push: it reports, and the consolidation release
  waits for it to report no failure. The checklist itself, `docs/ACCEPTANCE.md`, and the
  first report follow in a content pull request, since safe_push keeps a check apart from
  the content it judges.
- **The Jev calibration set.** The calibration set the brief describes is
  [`docs/reports/acceptance/jev/calibration.jsonl`](../reports/acceptance/jev/calibration.jsonl)
  (new), quoted from the files at `4d02d50`: fourteen rows, five seeded and nine controls.
  Item 9's question, framed as the brief frames it, is asked of the I.40, II.1, III.14 and
  III.24 statements as they stand before stages 2 to 4 move their new statements in, each
  once labelled "full" (seeded) and once with its own record (a control), and of four full
  statements with their records, each beside a seeded statement of its kind: I.39, I.6,
  II.4 and III.3. Item 10's question is asked of I.41, once with a planted dummy citation
  (I.37's result bound to `_` and never used, the step done by I.38: it compiles without a
  warning, and its proof term still names I.37, so the certificate would list it) and once
  as proved. It follows the client in a separate change (keep_apart). The examples in
  `scripts/audit/jev.py` now name the calibration file; only that documentation changes,
  with every check preserved. No request has been sent.
- **One certificate pin dropped, for one merge, on the owner's word.** Taking Circle 2 out of
  every proof (#60) makes the pin "III.2 rests on Circle 2, through III.1" false, and the
  harness does not let a pin flip in the same pull request as the content that flips it.
  The owner approved the two steps (18 October): this pull request drops that one pin from
  [`tests/certificate_expectations.json`](../../tests/certificate_expectations.json) and
  removes "only through III.1" from the reason of the pin on what III.2 inherits; the pull
  request that takes Circle 2 out adds the stronger opposite pins, that III.1, III.2 and
  II.14 rest on neither Circle 2 nor Circle 3. Nothing else is loosened.
- **The opposite pins: III.1, III.2 and II.14 rest on neither Circle 2 nor Circle 3.** The
  second of the owner-approved two steps: with Circle 2 taken out of every proof (#60),
  [`tests/certificate_expectations.json`](../../tests/certificate_expectations.json) gains
  three pins that their certificates exclude `Tacit.inside_of_between` and
  `Tacit.outside_of_between`, stronger than the one dropped in #107.
- **The formal model, complete.** All 87 locked laws are proved in the ordinary Euclidean
  plane in [`model/`](../../model/README.md), and `model_exists : ∃ S : Signature, Laws S`
  is proved with no hypothesis left
  ([#73](https://github.com/jackChallis/stoicheia/issues/73);
  [the owner's note](https://github.com/jackChallis/stoicheia/issues/73#issuecomment-6258608865)).
  The owner had made it a gate for the consolidation release
  ([his words](https://github.com/jackChallis/stoicheia/issues/73#issuecomment-6256202836):
  "the formal model is a gate for the consolidation release, not a target: every locked
  law proved in the model before #38"). What it establishes is what Astra wrote for this
  case, with our thanks: "Lean checks that the ordinary Euclidean plane satisfies every
  law in this revision's foundation. This establishes a model relative to Lean's logical
  foundations and Mathlib's construction of the real numbers. It does not establish that
  every formal statement captures Euclid's intended meaning." So the consistency of the
  axioms is a theorem, relative to Lean's logic and Mathlib's real numbers. The
  independence of Postulate 5 is not: that the other laws cannot give it, or that a
  statement failing in the hyperbolic plane cannot be proved without it, still rests on
  the numerical hyperbolic check until a hyperbolic model is built. The pages that said
  the model was in progress now say this, adapted to each:
  [`tests/model/MODEL.md`](../../tests/model/MODEL.md), a protected file, whose opening
  points to the model, whose section "A formal model: in progress" is now "The formal
  model" (what is proved, where, how the lock ties it and what it does not show; the
  links to its anchor move with it), and whose "What this shows, and what it does not"
  keeps the consistency, now proved, apart from non-derivability, still numerical; the
  formal model's row of the README's table of checks;
  [FORMALIZATION](../FORMALIZATION.md), sections 3 and 9; the milestone in
  [PROGRAM.md](../PROGRAM.md), section 4, marked done; the module docstring of
  [`Elements/Foundations/Words.lean`](../../Elements/Foundations/Words.lean), which keeps
  its length, so that no line a page links to moves, with no statement and nothing in the
  lock changed; and the dated correction at the head of
  [read-through 01](../reports/read-through-01.md). The numerical harness, its results
  and its hash are unchanged. The `formal-model` CI job is not yet a required check: the
  ruleset on main, and `REQUIRED_CHECKS` in
  [`scripts/safe_push.py`](../../scripts/safe_push.py), still name `check`, `model` and
  `negative`, and making `formal-model` required, as the decision of 18 October foresees
  once the package builds, is the owner's call.

- **A representation tag for the mixed angles.**
  [`review/terms.toml`](../../review/terms.toml) gains `mixed-angles-local`, the tag that
  brief 0011, which lands with them, gives the records of III.16 and III.31 once their
  companions state the angle clauses, in the move of the mixed angles into the edition
  ([#57](https://github.com/jackChallis/stoicheia/issues/57)): an angle contained by a
  straight line and a circumference is read as the region it opens near its vertex, and
  compared with a rectilineal angle placed at that vertex, along its straight arm and on its
  side, by containment near the vertex. Its last clause carries Astra's wording, as the
  prototype's report gives it (its condition 4): the comparisons use local containment of
  curved angular regions, and no general arithmetic or ratio theory of mixed angles is
  claimed. The tag adds that no motion of a mixed angle is claimed either, as the
  coordinator's approval of the prototype, above, says. It is a tag of kind
  `representation`, with no badge, since the certificate's sentence on badges speaks of a
  measure with no radius in it. It lands on its own, before the records that use it, since
  safe_push keeps a check's data apart from the content it judges, as
  `figure-with-dissection` did; `mixed-angles-omitted` stays while a record uses it. The
  protected file this changes is `review/terms.toml`.

- **The negative test of an undeclared run reads the passage of any kind.**
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py)'s fifth test drops the
  passages that declare III.16's runs of `--` lines with no Lean beneath them, and expects
  `check_fidelity.py` to catch the run of the angle clauses. It required that run's passage
  to be `unformalized`; once the companions of III.16 state those clauses (brief 0011, in
  the move of the mixed angles,
  [#57](https://github.com/jackChallis/stoicheia/issues/57)), the record declares the run
  as argued another way, and the test would fail on a precondition while the check it
  tests still works. It now requires only that a dropped passage begins that run, of
  whatever kind, and expects the same failure, so it plants the same break and catches it
  on today's record and on the record to come; nothing is loosened. It lands on its own,
  before the records it reads, since safe_push keeps a check apart from the content it
  judges. The protected file this changes is `scripts/negative_tests.py`.

- **Placement: only III.24 and `Arcs.lean` may cite it.** [Brief 0006](0006-statements.md)
  ("Placement", the policy) asks for a check, with a negative test, that outside
  `Elements/BookIII/Placement.lean` and `Elements/BookIII/Placement/` only III.24 and
  `Elements/BookIII/Arcs.lean` cite `placement` or any declaration of the `Placement`
  namespace: the lemmas of the namespace carry the same distance-keeping content as the
  whole, so a check of `placement` alone could be got round through them.
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py) gains it in two parts. Read
  from the source as its scan of forbidden commands reads it (`read_lean`), comments and
  literals taken out, no Lean file under `Elements/` but those four names `placement` or
  `Placement`, each finding naming its file and line; `Staging/` and `Audit/`, which that
  scan reads too, are outside the policy, which is the edition's, and `Staging/` holds
  placement's staged statements until they move. And, from facts.json, no entry but III.24
  has placement, a lemma of the `Placement` namespace or anything declared in placement's
  files among its shared steps, so that a proof that reaches it without naming it is caught
  too. [`scripts/negative_tests.py`](../../scripts/negative_tests.py) gains two tests: a
  lemma of the namespace named in `Elements/BookIII/Squares.lean` is caught on its line,
  and the word in a comment there is not (test 9, the build test becoming 10); placement
  among III.26's shared steps, on a copy of facts.json, is caught, and III.24, given it
  too, is not blamed (in test 3). The superposition check that the brief rewords needs no
  new code: the policy that only I.4 and I.8 use superposition directly reads III.24's
  `direct_axioms`, whose walk passes through placement and its lemmas and stops at I.4, I.7
  and I.8 as entries, and the lock check covers every axiom III.24 rests on. The check is
  added, and nothing is loosened; with nothing under `Elements/` naming placement yet, it
  passes on main. It is a check change, and lands in a pull request of its own, before the
  stage 3 statements it checks (WORKFLOW, section 10). FORMALIZATION, section 7, lists the
  policy and the two tests.

- **`Audit/` and the formal model's build files are protected paths.** `Audit/` holds the
  audit lemmas whose pinned axiom lists (`#guard_msgs`) back the overlap catalogue's
  claims, so a change there could weaken what the catalogue asserts without a security
  review or a decisions entry. The work on brief 0008 raised it, and the coordinator
  decided it as a check strengthened, never weakened (#96).
  [`scripts/safe_push.py`](../../scripts/safe_push.py)'s protected list now holds `Audit/`;
  `Audit.lean`, the root that decides which audit lemmas `lake build Audit` checks; and
  the model's build files, `model/lakefile.toml`, `model/lakefile.lean` (which Lake would
  read in preference to the toml, as at the root), `model/lean-toolchain`,
  `model/lake-manifest.json` and `model/lock.sha256`. [WORKFLOW](../WORKFLOW.md), section
  10, "Protected paths", names each. A change to any of them needs a new line here naming
  it, the label `security-review` and a `/security-review`. They are content the checks
  judge, not checks, so they stay judged: a check change is still kept apart from them, as
  it was before they were protected. A protected path is now named only whole, from the
  root (with or without a leading slash) or by a relative link, so a line naming
  `tests/model/lock.sha256` no longer counts for `model/lock.sha256`, nor one naming
  `model/lakefile.toml` for the root's `lakefile.toml`. Nor is a path named by a longer
  one at its other end, so a line naming `Audit.lean.orig` does not count for
  `Audit.lean`; and a line edited in place so that it names a different file now counts
  for the file it newly names (from `model/lakefile.toml` to `lakefile.toml`, say), which
  the old pattern refused, because it read the root's `lakefile.toml` in the removed line
  too. [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) gains the cases:
  each new path refused without its line, a longer path's mention refused, a relative
  link accepted, and the new paths still judged. None of the cases it held before is

- **The tests of an interruption after the push depend on nothing but the run.** Two tests
  of `InterruptedAfterThePush` had failed once beside a Lean build (#95, found during the
  work on #40). Under load alone they never failed here: eleven runs of the class, eight
  of them at load averages of 23 to 32 with four from-scratch builds of the library
  running alongside, and three more with git's background gc forced. They did fail,
  exactly the two that follow CI while the third passed, when the checkout's
  `scripts/safe_push.py` changed after the suite had committed it as origin/main's, as an
  edit in a shared checkout would change it while the suite runs: the copy run then
  differs from origin/main's and hands over to it, the hand-over leaves behind the
  stand-ins the tests put in place of following CI, and the run follows the stand-in CI to
  success, exit 0. So [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) now
  runs every driven test from a copy of the harness as the suite committed it, and the
  three tests of the class run on a clock of their own, which never reads the wall clock
  and never waits, twice: with time standing still, and with each reading an hour after
  the last, past every deadline `safe_push.py` keeps. Each run must still end in "pushed;
  CI not followed", exit 3, and must now show origin/main's harness, never handed over,
  and a total that is the clock's. `scripts/safe_push.py` is unchanged, and no test is
  loosened.

## 19 October 2026

- **The edition does not name its owner.** The owner asked that Stoicheia not be presented
  as anyone's personal project, and that the name come out of its prose. Where a passage
  needs the role, it now says "the owner", the repository's owner, as
  [WORKFLOW](../WORKFLOW.md), section 1, defines the role, with exactly the same force: no
  approval or decision moves. AGENTS.md says "the repository owner", since there "owner"
  also means a file's owner. Changed: [AGENTS.md](../../AGENTS.md),
  [FORMALIZATION](../FORMALIZATION.md), WORKFLOW, [PROGRAM](../PROGRAM.md), the README's
  "How it was made", briefs 0001 and 0005 to 0009, and two reports:
  [outside review 01](../reports/outside-review-01.md), whose quoted prompts are now
  labelled "We asked" and keep their words, and
  [read-through 01](../reports/read-through-01.md). Brief 0001, kept as history, records
  the change in its own note. No statement, check or earlier decision changes, and no
  protected path. Three things are the owner's to decide: the copyright line in
  `NOTICE`, the authors in `CITATION.cff` and the repository's address on GitHub. A sample
  identity in `scripts/test_safe_push.py`, a protected file, now uses
  `Stoicheia Team <team@example.org>` instead of a person's name. This tooling-only change
  leaves the test's meaning unchanged: an ordinary identity is not flagged.

  name in a test in `scripts/test_safe_push.py`, a protected file, waits for a tooling pull
  request of its own.

- **The style check reads every text a reader meets: the check change
  ([#66](https://github.com/jackChallis/stoicheia/issues/66)).** Argon's second review of
  the Book III release (18 October) found that S7 and S12 skipped the notes of the review
  records, the front pages, the reports and the docstrings the pages show, so that
  "Definition 8" and `hnearer` reached the pages unseen; our warm thanks to Argon.
  [`scripts/check_style.py`](../../scripts/check_style.py) now reads each of them, as
  [STYLE](../STYLE.md), section 8, lists:
  - the Review notes: the texts of a record that its page shows (the statement's `note`,
    `short` and `hypotheses`; the `note` of the route, the representation and the overlap;
    the figure's `case` and `note`; the clause map's claims; each passage's `note`), and
    each tag's `meaning` and `badge` in `review/terms.toml`, under the prose rules S1 to
    S9, with D7 to D9;
  - the overlap catalogue, beside the gap catalogues, and S7 in both, where it was D10;
  - the Other reports, every other report of `docs/reports/` save the outside reviews,
    which keep their reviewers' words as written, under S1, S7 and S8;
  - the Rendered docstrings, the tacit rules' that `render.py` copies onto the pages,
    which now fail S6 and S7 as well;
  - the front pages and the table of names, beside the generated files, and S7 in all of
    them;
  - S12 beyond the mishnah, in the prose, the Review notes, the catalogues, the Rendered
    docstrings and the front pages, each text with its book's namespace (every book's for
    a text with none, and the foundations' for the Rendered docstrings), and the name
    before the colon of a backticked `name : type`, which B2 and E2 of
    `scripts/check_acceptance.py` now read in the gap catalogues and the
    overlap catalogue too, as S12 does, since they take their names from
    `check_style.lean_names`. `NOT_DECLARED` lists the two tactics and the three fields
    of facts.json it cannot `#check`, each with its reason, and fails an entry that no
    text uses any more. The overlap catalogue's audit lemmas are put to Lean once
    `lake build Audit` has run, as CI runs it. The mishnah is asked as it always was,
    every name with `import Elements` alone, and neither excuse holds there;
  - S22, new: a code span of letters alone (`P`, `PQ`, `ABCD`), in all of these and the
    Lean notes. The owner's second comment on #66 asked that Book Zero's backticked pairs
    of letters be swept, or excepted in STYLE: they are swept, with the lone letters
    beside them, so that a sentence does not set P one way and PQ another, in the text
    change that follows this one; and STYLE, section 1, says that a step written over any
    letters writes them plain too, the Lean's variables among them.

  The hypotheses rule has one home, STYLE, section 1, "Hypotheses in words", as the
  owner's first comment on #66 asked, since the form in review/SCHEMA.md named a
  hypothesis by its local name where STYLE said words: the row for `hypotheses` and the
  worked example of [`review/SCHEMA.md`](../../review/SCHEMA.md), and the
  [proposition template](../templates/proposition.md), point to it, and S12 holds it.
  The new reach is held file by file. On main at `89c5da4` it finds 1,173 things, 1,137 of
  them S22's, nearly all in the notes of Book Zero and the foundations, 25 of S7 and 11 of
  S12, in 37 files; `REACH_PENDING` lists those files, each with the rules it had findings
  of and whoever mends it (the text change after this one; stages 3 and 4; the records of
  Books I and II; the next change to III.10 and III.19, with their records; the
  coordinator, for the foundations), and reports their findings of those rules as D16
  meanwhile. Every other finding of the reach fails at once, in a listed file as in any
  other, and every file is held to all it was held to before: nothing is loosened, and
  cases of `tests/test_check_style.py` show an em dash still failing in a listed file, and
  a listed file held at once to the rules it is not listed for. A rule of an entry whose
  file has nothing of it left is reported as done, rule by rule as the excuse is (S12
  aside when Lean is not asked, under `--no-lean` or for want of `lake`), and comes out
  of its entry in a change to the check, and the entry with its last rule; the list goes
  once it is empty.
  `scripts/check_acceptance.py` also sends every style finding in a proposition's review
  record to P9 before it classifies findings by rule.
  The protected files changed are [`scripts/check_style.py`](../../scripts/check_style.py),
  [`scripts/check_acceptance.py`](../../scripts/check_acceptance.py),
  [`tests/test_check_style.py`](../../tests/test_check_style.py) (54 scope cases and 14
  reach cases), [`review/SCHEMA.md`](../../review/SCHEMA.md) and
  [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml), whose comment on S12 now
  says what it reads. Astra read the first draft cold, through the Codex CLI, and found
  nine faults, five more in a second reading of the mends and one in a third, each now
  mended with a case of its own: among them, a phrase that runs from one Lean note into a
  rendered docstring, a docstring read with other white space than its page shows, a
  mishnah name excused that used to fail, a TOML comment taken for a note, and a D10
  report lost. Our warm thanks to Astra.

- **S12's reports distinguish names from other code spans.** The check change for #66
  keeps the Other reports in S12, as `d017113` added them. Their file names and numeric
  file locations are recognized against the repository; Lean supplies its keywords,
  tactics, attributes and namespace-only names. A report may explicitly identify an
  external tactic, a namespace, a scan identifier or a revision identifier. Certificate
  fields and review schema fields and values are recognized from their definitions where
  the prose discusses them. A trailing dot names a family, not a declaration. None is an
  exception made from a list of failed names, and a typed hypothesis is still checked.
  These classifications apply to the new report reach alone: the mishnah keeps every
  check it already had.

  The remaining findings on main's content at `bd3b72a` are the initial inventory of
  this reach, deferred by file and rule in `REACH_PENDING`, as the other new reach is:

  | File | Rule | Findings |
  |---|---|---|
  | `docs/reports/mixed-angles-prototype.md` | S12 | 147 |
  | `docs/reports/read-through-01.md` | S12 | 2 |

  The 149 findings include incomplete or ambiguous references, local names and names
  from a staged or earlier version, among them `Exceeds.nearVertexOpen`. The content
  change after #66 corrects or qualifies each reference; the S12 entry then comes out
  in a check change. The read-through's existing S7 entry stays. Every report still
  reaches S12, and an unknown declaration in an unlisted report fails.

  Reading `d017113` and `8c235bb` in full also exposed the Lean probe's existing
  100-error cutoff: the new reports reached it, and later names were not checked.
  The probe now passes `-DmaxErrors=0` to Lean, so every name is read, even after a
  pending report's hundredth finding. A source-level option does not change that
  command-line reporting limit. The Markdown changes in those commits align code spans,
  tables and container boundaries with the documented scope; the changed D10 expectation
  concerns a multiline code span, which the rule excludes. No other main-content failure
  or relaxation of a documented rule was found in those commits.

  The protected files changed are [`scripts/check_style.py`](../../scripts/check_style.py)
  and [`tests/test_check_style.py`](../../tests/test_check_style.py). The regressions cover
  the token categories, retained mishnah enforcement, unknown report names with and
  without an S12 pending entry, and a failure after more than 100 deferred errors.
  [STYLE](../STYLE.md), section 8, describes the report classification. No judged content,
  Lean source, review record or generated page changes.

- **A new tag, `touching-whole-circles`.** [`review/terms.toml`](../../review/terms.toml)
  gains the tag, of kind `representation`, with the meaning [brief 0008](0008-centre.md)
  gives it, word for word (section 4, "Records, Lean files and pages", and question 9):
  "Circles touching one another are read of the whole circles: touching within, no point
  of the inner is outside the outer; touching without, no point is within both; so touching
  circles cross nowhere, the reading Heath reports as Todhunter's (III.6, III.11–III.13)."
  It is a representation, not a centre: when `centre-given` leaves the records, those of
  III.11, III.12 and III.13 keep their `[representation]` with this tag, and III.6 takes it
  too. It lands here, in a pull request of its own, before any record uses it, as
  [FORMALIZATION](../FORMALIZATION.md), section 3, asks and as step 1 of the brief's
  section 6 orders; no record carries it yet, so no page changes. When the definition of
  contact within changes, in the brief's step 6, the meaning gains that the inner circle has
  passed within the outer (question 16). Protected file changed: `review/terms.toml`.
- **An overlap always names its kind.** The last part of
  [#93](https://github.com/jackChallis/stoicheia/issues/93), as its comments list it. The
  decision of 18 October, "An overlap is worded by its kind, as the catalogue gives it",
  made `kind` optional so that the check could land before the records named their kinds,
  and worded a record with no kind as one whose rule contains the proposition. Every
  record on main now names its kind (I.2, I.3, I.7 and I.23 `step`, III.2 `states`, III.5
  and III.6 `gives`), so the key is required, and a new `[overlap]` without it, as III.1's
  might be under brief 0008, can no longer render "contains" by default, the defect #93
  fixes. [`review/SCHEMA.md`](../../review/SCHEMA.md) marks `kind` required, and its list
  of what the machine checks says so. [`scripts/heath.py`](../../scripts/heath.py) rejects
  an `[overlap]` with no `kind` ("`kind` is missing"), and its self-test case
  `{rule: Tacit.circle_eq}`, which it accepted, is now a rejection; the other five cases
  stand. [`scripts/render.py`](../../scripts/render.py) drops its fallback to "contains":
  `overlap_steps` reads the record's `kind`, which every record it is given now carries.
  The proposition template's `[overlap]` lines say the key is always named. Nothing a
  reader sees changes: the pages render the same at the branch's base. This is a check
  change on its own; it changes no record.
- **The negative tests read the count of assumptions from the lock.** The planted-assumption
  test of [`scripts/negative_tests.py`](../../scripts/negative_tests.py) expected
  `check_fidelity.py` to say "declares 88 axioms, not 87", a count fixed in the script. It
  now reads the number of axioms in
  [`Certificate/axioms.lock`](../../Certificate/axioms.lock) before it plants anything, and
  expects one more than that, so the test keeps its meaning when an approved rule joins the
  lock. This is step 1's third item in [brief 0008](0008-centre.md), section 6: without it,
  the pull request that adds the rule that every circle has a centre could not pass. Today
  the lock holds 87, so the test expects what it expected before; nothing else in the
  script, and no check, changes. The one protected file it changes is
  `scripts/negative_tests.py`.
- **The model's audit and its root are protected too (#96).** `model/Model/Audit.lean`
  pins the model's proofs to `propext`, `Classical.choice` and `Quot.sound` alone and
  checks that `Elements` is absent; `model/Model.lean` imports that audit, so the build
  checks it. They join `Audit/` and `Audit.lean` in the protected paths of
  [`scripts/safe_push.py`](../../scripts/safe_push.py), and remain content the checks
  judge, so a check change is still kept apart from them. A change to either needs its
  own whole path named here, the label `security-review` and a `/security-review`.
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) gains cases for each:
  refused without that line, a longer path's mention refused, a relative link accepted,
  and still judged. The cases also keep similarly named paths, `model/Model/Hand.lean`
  and `model/Check/Hand.lean` unprotected. [WORKFLOW](../WORKFLOW.md), section 10, names
  the two files and their reason. Nothing is loosened; no model proof or audit changes.
  In `scripts/safe_push.py`, with regression cases in `scripts/test_safe_push.py`, a
  relative link must resolve from the decisions page's folder to the protected file,
  so routine edits to `model/Model.lean` (a new import) and `model/Model/Audit.lean`
  (a new pinned law) now need such a line too.
- **The overlap wording and the table of stages are brought up to date.** The two text
  follow-ups to #93 update the [README](../../README.md)'s row for `Audit/` and the
  [Book I brief](book-I.md)'s account of its four overlaps: a rule supplies a step of
  I.2, I.3, I.7 and I.23, and I.23 rests on superposition through I.20 as well as I.8.
  Brief 0005's table of stages in [PROGRAM](../PROGRAM.md) marks stage 2 done and names
  #90 in stage 4's row as the pull request that proved its propositions in Staging.
  The next steps in [`docs/program.toml`](../program.toml), which supply PROGRAM's
  status table, keep their words for now. A protected test in
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) quotes Book I's stage
  words. The next steps are reworded after the test's own change on
  `tooling/safe-push-stage-line` lands separately, as [WORKFLOW](../WORKFLOW.md),
  section 10, requires.
- **Stoicheia Team is the edition's copyright holder and cited author.** On 19 October 2026
  the owner decided that [NOTICE](../../NOTICE) reads "Copyright 2026 Stoicheia Team and
  contributors" and [CITATION.cff](../../CITATION.cff) names one author, the entity
  "Stoicheia Team". The credit that [LICENSE-PROSE.md](../../LICENSE-PROSE.md) asks for now
  names that author beside the title. [README.md](../../README.md) has no citation block or
  text asking readers to cite the project; [references.bib](../references.bib) has no entry
  for Stoicheia itself, so neither changes. [LICENSE](../../LICENSE) keeps the Apache
  template's copyright line. A repository-wide search for the surname and copyright lines
  found no other project attribution to change; third-party credits and notices stay as they
  are. The sample name in `scripts/test_safe_push.py` still waits for its own tooling pull
  request. This settles two of the three things "The edition does not name its owner" left
  to the owner. The repository's address on GitHub remains the owner's to decide, and its
  links stay unchanged. No statement, check or protected path changes.
- **The screen's new near misses are pinned in the audit.** The overlap screen, as #78 widened
  it, finds that III.30 can be proved from its angle measure alone, without III.28. The
  catalogue lists it among the near misses of representation, and
  [`Audit/Overlaps.lean`](../../Audit/Overlaps.lean) gains the proof that shows it,
  `Audit.III_30_measure`, beside the other audit lemmas. `Audit/` became a protected path
  with #96 (train H6, #113), so this entry names the file: `Audit/Overlaps.lean` gains one
  lemma and its docstring, and no pin, statement or check changes. No proposition rests on
  the new lemma; it records what a rule already gives.
- **The review schema points to the acceptance checklist that now exists.**
  [`review/SCHEMA.md`](../../review/SCHEMA.md) said that `docs/ACCEPTANCE.md` "will fix the item
  keys" and that `items` stays empty until it exists. The checklist landed with #111 and fixes
  the keys and when an item counts, so the schema's `items` row and the sentence after the
  table now say so and link it. Wording only: no field, rule or check of the schema changes.
  This entry names the protected file `review/SCHEMA.md`.

- **No certificate entry may rest on Circle 2 or Circle 3.** The check keeps
  [brief 0008](0008-centre.md)'s III.1 construction from reaching Circle 2, which states
  III.2, or Circle 3, which gives it at once.
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py) now refuses either rule
  in any entry's axioms, propositions, porisms and companions of every book included,
  and names the entry and the rule. It also fails if `Certificate/axioms.lock` no longer
  holds either rule's name, so a renamed axiom cannot leave the check refusing nothing.
  Main at `39ae65c` passes, and its `facts.json` is the one delivered here: none of its
  121 entries rests on either rule.
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) plants Circle 2 in a
  proposition and Circle 3 in a porism and a companion, on separate copies of
  `facts.json`, without a build, and expects each refusal by name. It then renames Circle 3
  in the lock, restored after, and in a copy of `facts.json`, and expects the missing
  name to be caught. These are the two protected files changed. FORMALIZATION states what
  the check covers: an entry, whether through its own proof or through a lemma it uses.
  Book Zero lemmas are not entries, so they are covered only through entries that use
  them. The overlap catalogue's account of the rule, and the README's row, are held for
  the pull request that follows. Nothing is loosened.

- **Planted faults for the remaining checks.** `scripts/negative_tests.py` now plants an
  em dash in I.1's mishnah, caught by S1 with the file named; a relative link to a
  missing page, caught with the source and target named; a generated I.1 page stale
  beside a changed mishnah, caught by the page's Git status line after rendering; and
  an axiom omitted from an audit lemma's expected list, caught by `#guard_msgs` in
  `lake build Audit`. The freshness test changes the source as well: editing only the
  page would let the renderer restore the committed text and leave Git status clean.
  A corrupt header in I.1's compiled file makes leanchecker itself name the file and
  report its invalid header, using the invocation in `scripts/check_kernel.py`.
  This tests the loading of compiled files; no invalid proof term is planted for the
  kernel replay. Each new plant restores its inputs in `finally`, and the freshness
  test saves every renderer output. Before each plant that builds, every file under
  `.lake/build` is saved, including companion outputs, dependent modules, hashes and
  traces. A restoration build is attempted; if it fails or is interrupted, the saved
  files return with their original bytes and newly created files are removed. After
  I.1's successful rebuild, leanchecker replays the restored environment. The
  assumptions test restores or removes its temporary module's outputs in a nested
  `finally`, even when the restoration build is interrupted. Each new plant reports
  its time, restoration included. An outer `finally` compares the final Git status
  with the entry status, even on interruption, preserving an exception already in
  flight if that comparison also fails. Restoration needs writable files and time
  for `finally` to finish; a forced process kill cannot provide it.
  `tests/test_negative_tests.py` tests failed and interrupted builds, saved and absent
  outputs, temporary-module cleanup, replay after a successful rebuild and the final
  status comparison in temporary directories, without Lean or Git. The script runs
  these regressions before planting. Its docstring states the coverage and its limits;
  the README table update is deferred to a later pull request after this check change.
  The protected files changed are `scripts/negative_tests.py` and
  `tests/test_negative_tests.py`. No check is loosened.
- **The merge commit names the owner GitHub names
  ([#41](https://github.com/jackChallis/stoicheia/issues/41)).** `git safe-push --merge`
  gives the merge commit GitHub's own subject, "Merge pull request #N from owner/branch",
  and took the owner from origin's URL, which after a transfer or a rename, both of which
  GitHub redirects, would name the old one. It now takes the owner GitHub reports for the
  pull request's head (`headRepositoryOwner`), read by the gates with the branch name and
  the title, and a new gate, "subject", shows the subject before the merge and refuses the
  merge when GitHub names no owner, or none an account could have (a login of letters,
  digits and hyphens), before gh is asked. Nothing the merge checked before is loosened.
  The files changed are [`scripts/safe_push.py`](../../scripts/safe_push.py)
  (`merge_subject`, beside `gates` and `merge`, and its docstring) and
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) (a test, with the
  stand-in for gh naming no owner, five owners no account could have, then a new one,
  which fails before the change), with
  [WORKFLOW](../WORKFLOW.md), section 10, "Landing work: pull requests", step 4.
- **A merge is GitHub's word, never gh's exit alone
  ([#42](https://github.com/jackChallis/stoicheia/issues/42)).** With a merge queue or
  auto-merge on, `gh pr merge` exits 0 having only queued the pull request; `--merge` took
  that for a merge, judged origin/main's last commit as the merge commit, and would then
  have advised reverting the wrong commit. Neither is on today. Whatever gh's exit, GitHub
  is now asked, and success is reported only when GitHub says the pull request is merged
  and origin/main holds the merge commit GitHub names (a full object name). gh exiting 0
  with the pull request not merged, GitHub naming no merge commit or one origin/main does
  not hold, GitHub not to be asked, or giving no state, is "merge state unknown", exit 3,
  with no revert advised, since nothing on main is known to be the merge. Nothing is
  loosened: a merge that happened, or may have, is still never exit 1, and three cases are
  now more cautious than before: GitHub giving no state after gh failed, once "nothing was
  merged", exit 1; GitHub not to be asked after gh exited 0, once a merge; and an
  interruption while GitHub is asked after gh exited 0, once "merged", exit 3. One test's
  expectation moves with the last, the more cautious way:
  `test_interrupted_after_gh_merged_is_merged` is now
  `test_interrupted_after_gh_exits_0_is_unknown`, still exit 3, and expects "merge state
  unknown" where it expected "merged". The change's independent review found four answers
  GitHub could give that the merge misread or crashed on, and we thank it: an owner that
  is no account's name (above), a state that is none of OPEN, CLOSED and MERGED (once
  "nothing was merged", exit 1, though gh had merged), and a merge commit named by
  something other than its full object name, or by nothing, which was fetched and judged
  before the merge state was settled. Each is now refused by the gate, or "merge state
  unknown" before anything is fetched, with tests. The files changed are
  [`scripts/safe_push.py`](../../scripts/safe_push.py) (`merge_outcome`, `verify_merge`,
  `merge_main`, a new refusal `MergeUnknown`, and its docstring) and
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) (three ways for the
  stand-in for gh to exit 0 with no merge on main that GitHub vouches for, a way for
  GitHub to give any answer a test needs, and six new tests, each failing before the
  change), with
  [WORKFLOW](../WORKFLOW.md), section 10, "Landing work: pull requests", step 4.
- **III.37 leaves the grouped-case example.** The example in the `uncarried_runs` docstring
  of [scripts/check_fidelity.py](../../scripts/check_fidelity.py) drops III.37, whose case
  with the centre on AC gets a proof of its own, `Prop37.centre_on_secant`, on ship R1's
  train. The docstring holds before and after that train lands. I.14 remains as the example
  of a "similarly" that one argument already covers. The docstring is the only change to
  the script; the check is unchanged.
- **I.39 and I.40 now follow Euclid's reductio to its end.** I.40's companion
  `Prop40.general` does so too, so their records' route is `euclid`. Under "The follow-ups
  to the precision pass", the entry "Two more kinds of passage, and what 'argued another
  way' means" called them "one step changed". It is superseded on this point and stays as
  history. [review/SCHEMA.md](../../review/SCHEMA.md) now uses III.8 as its example of a
  `modified` route: its last step compares the angles at the centre by I.24.
- **The overlap screen unfolds every defined word, tries each statement bare, and has its
  cases.** Argon's second review of the Book III release (section 1.3) found that
  [`Audit/screen.py`](../../Audit/screen.py), the mechanical screen behind the
  [overlap catalogue](../reports/overlaps.md), unfolded only the phrases `SameSideOf` to
  `LinesMeet`, so that a statement written with `Triangle`, `Collinear`, `circumference` or
  `standing` was searched only in part
  ([#78](https://github.com/jackChallis/stoicheia/issues/78)); we thank Argon for reading
  the screen so closely. The screen now begins with a pass that lists every definition of
  the edition that a statement or a rule reaches, through the bodies of other definitions,
  and stops if one is not provided for. It unfolds 35 words: the phrases, `Triangle` and
  `Collinear` among them, and the words for "any number" that stage 2 brought in
  (`InOrder`, `segments`, `endOf`, `triples`, `Magnitude.sum`, and the areas of a figure
  given with its triangles), those defined by cases or by recursion through the equations
  Lean proves for them. It gives the magnitudes Lean chooses (`circumference`, `standing`,
  `rect`) and the order "not greater" to `grind` by what their definitions say and nothing
  more, a lemma each, proved from Lean's choice alone, and leaves the kinds of magnitude,
  with their sum, order and zero, as the axioms state them. Every file of tries first proves
  thirteen goals that `grind` closes only with the definitions unfolded, each checked to
  fail without them, so a screen that has stopped unfolding stops. Its docstring says what
  stays unsearched: that two descriptions choose the same magnitude when they hold of the
  same things; that every point of a circle measures a circumference alike, which is III.21;
  and what a figure fitted from triangles (`Fitted`) or given with them (`Rectilineal`,
  `Apart`) holds by its formation, since `grind` does not reason by induction or open a
  structure's fields of itself. Each attempt with rules is now two tries, `grind` as it
  chooses and `grind` forward, each with the budget the two used to share; a try that runs
  out of time is tried again with four times as much, and one that runs out again, or that
  stops on any other error, is listed as not searched to the end. A try leaves out the rules
  `grind` refuses, finding nothing in them to match: the twelve that only say that a point,
  a straight line or a circle exists, and, forward, fourteen more with no hypothesis it can
  start from. Given one, `grind` refused the whole list, so that until now more than a
  quarter of the attempts, the families Postulates and Constructions and every pair with
  either among them, were made with no search at all. A bare try, with no rule, comes first
  for each statement, so that a statement that holds by its definitions alone is listed
  apart and not counted as a rule's. Each job runs on one thread. The screen names the
  statements it closes; fails if III.2, III.5 or III.6, the rows it has always found, stops
  closing by a rule; and stops if a Lean process ends before its file does, or an error
  falls in a file's preamble. It reads a try's messages from its `set_option` line, so that
  one reported there is not counted against the try before it, and it reads an error
  whether or not Lean names its kind after the word, as Lean 4.35 does for some
  (`error(lean.unknownIdentifier): …`), so that such an error in the pass over the rules
  stops the screen, and a try that stops on one is listed.
  [`tests/test_screen.py`](../../tests/test_screen.py) (new) puts the screen's own functions
  to small cases with no Lean: the attempts and tries it makes, its reading of Lean's logs,
  of the rules refused and of the definitions reached, and the known rows. The protected
  file it adds is `tests/test_screen.py`. `Audit/screen.py` is not a protected path today;
  it is named here too, as [#96](https://github.com/jackChallis/stoicheia/issues/96) may
  make `Audit/` one. CI runs neither the screen, which takes about an hour and a half of
  processor time, nor its cases yet: whoever changes the screen runs both. Run on the
  statements of `89c5da4`, the 99 propositions, the three porisms and the 19 companions, its
  48,400 attempts made 90,629 tries and closed III.2, III.5 and III.6, each by a rule, and
  nothing else; no statement closed bare. Seven tries ran out of time even with four times
  the budget, all of them III.34 from Postulate 4, alone or with Postulate 5 and at most one
  more family. III.34 asks for three points on its circle, and the rules among those that
  put a point on a circle that has none need a straight line, which III.34 does not give
  and none of those rules draws. The catalogue's account of the screen, and III.30 among
  its near misses, follow on a text branch of their own, after this one.
- **What the checks of train H8b judge lands in train H9b.** As the entry for H8b says, the
  content its branches held back lands here, after the checks: `docs/ACCEPTANCE.md`'s lines
  for style everywhere (`tooling/style-everywhere`), the README's table and the overlap
  catalogue's lines on the Circle rule (`tooling/no-circle-2`), the README's row for the
  negative tests (`tooling/planted-faults`), PROGRAM.md's open work
  (`tooling/safe-push-followups`) and the overlap screen itself
  (`tooling/overlap-screen-unfold`, #78), whose tests landed with H8b. Acceptance in CI and
  its page wait for a fix (#35). The protected file this train changes is `Audit/screen.py`:
  the screen unfolds every defined word, tries each statement bare, and has its cases, as the
  entry for #78 describes; it declares nothing Lean checks, and no audit lemma, pin or
  statement changes.
- **The checks, made ready for retiring axioms.** The owner asked, "Fewer axioms is better.
  Any more that can go?", and on 19 October 2026 approved both retirements: "Please do both.
  79 is rather large with so many books in front of us." On 20 October the owner approved
  landing each as three pull requests; this is the first of the first. A search found eight that can go with no choice of basis (the retirement's own entry
  names them). Since a check never changes in the pull request of the content it judges,
  this change prepares the checks first, with all 87 axioms in place and the pin change
  recorded below. Main already reads the expected axiom count from
  the lock in its negative tests, and that count stays as main has it; the further
  changes to the negative tests are recorded below.
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) moves its mutation, count
  and membership fixtures to laws and pins that survive (I.5's inherited Postulate 3);
  [`scripts/safe_push.py`](../../scripts/safe_push.py) drops the generators `gs_adj` and
  `gs_lmc_opp` from its allow-list, because
  [`tests/model/hyperbolic.py`](../../tests/model/hyperbolic.py) now samples those two laws
  with generators the other laws use, with byte-identical output;
  `tests/model/derived.py` (new) keeps the eight laws'
  configurations as derived properties, which
  [`tests/model/exhaustive.py`](../../tests/model/exhaustive.py),
  [`tests/model/structured.py`](../../tests/model/structured.py) and
  [`tests/model/run.py`](../../tests/model/run.py) run, count and enforce as strongly as the
  laws, [`tests/model/MODEL.md`](../../tests/model/MODEL.md) records that independent
  contract, and [`tests/model/mutations.py`](../../tests/model/mutations.py) changes only
  a description. The formal model's comparison of the eight hand translations directly
  with the library's declarations goes with the retirement, since the model is content
  the checks judge.
- **One certificate pin dropped, with the owner's approval.** The retirement makes
  `Tacit.centre_unique` a theorem, so no certificate can list it, and the first expectation
  in [`tests/certificate_expectations.json`](../../tests/certificate_expectations.json),
  that III.1 Por.'s assumptions include it, had to go first, as the pin dropped for #60 did.
  On 19 October 2026 the owner approved this first step of a two-step pin flip: commit
  `5d200cf` removes the `includes: ["Tacit.centre_unique"]` pin while retaining its count.
  Deleting that dependency still fails, but a substitution that keeps the count would no
  longer be caught. C6's full `equals` pin remains pending; the retirement then adds stronger
  pins that III.1, III.1 Por., III.2 and II.14 rest on none of the eight. This approval is for
  the first pin change alone; the retirement itself is approved as the entry above says.
  The stronger pins cannot fail once the eight are theorems, as the next paragraph explains;
  pins that can fail are #168, which holds every release until it closes.
  As built, those pins put the eight names in `excludes` on each entry's `axioms`. Once
  the eight are theorems no axiom list can hold their names, so those pins cannot fail;
  an entry's use of a proved rule shows only in the axioms beneath it, which `proved_rules`
  (the entry below) lists for each rule. A pin on the proved rules an entry uses would
  need a field of its own, which this change does not add.

- **Restricted superposition prepared for the owner's final word, not landed.** On
  19 October 2026, [brief 0009, round 3](0009-superposition.md) records the replacement
  prepared on `lean/superposition-restricted`, at `aa96ab8`, from `origin/main` at
  `39ae65c`. The owner's decision of 18 October authorised the prototype and preparation;
  the finished branch awaits the owner's final word. `Tacit.superposition` now has type
  `Superposition.Rule primitives`: a represented derivation may export one equality of
  lengths, angles or triangles about the given figure, and may neither introduce objects
  inside the placement nor export its hypothetical corners or side. I.4 and I.8 alone use
  it directly. Their statements and Heath lines are unchanged, their coincidence
  arguments are retained, and every dependent proof has rebuilt. The same 115 of 121
  certificate entries rest on the rule. I.23 keeps its construction through I.22 and
  inherits the rule through I.8 and I.20.

  The four new pure modules under `Elements/Foundations/Superposition/` are `Syntax.lean`,
  `Semantics.lean`, `Soundness.lean` and `Restriction.lean`. They use Lean's `module` format
  with public imports and sections so that the model's modules can import them. Their
  words include `Atom`, `Lit`, `Metric`, `Letter`, `LineLetter`, `Law`, `Cited`, `Derives`,
  `Name`, `LineName`, `Interpretation`, `Val`, `Collinear`, `Triangle`, `Rule`, `guards`,
  `kept`, `branch` and `rayOfAnglePremises`, with the reached constructors, fields,
  recursors, matchers, renamings, law data and interpretations. The library's `primitives`
  reads them in its own geometric words. `Elements/Figure/Superposition.lean` proves the
  geometric cited laws; I.8 supplies I.7's adapter. The deleted directory
  `Staging/Superposition/` held the six prototype files; its proofs and restriction evidence
  now have these production homes. The old-axiom compatibility example is removed.

  `Certificate/axioms.lock` restates one axiom, keeps all 87, and adds 115 vocabulary
  entries, from 91 to 206, with no former word removed or otherwise changed.
  `Certificate/Facts.lean` recognises actual uses of the calculus's three congruence
  constructors as C.N. 4; all 121 common-notion lists match the baseline.
  `tests/certificate_expectations.json` keeps its eleven existing expectations unchanged
  and adds thirteen for the restricted rule, its citations and C.N. 4.
  `Audit.lean` imports the new superposition audit.
  `Audit/Superposition.lean` pins 27 dependency closures, including both propositions,
  soundness, restriction evidence and the cited-law proofs.
  `Audit/Overlaps.lean` retires `I_2`, `I_3` and `I_23`, preserving the thirteen surviving
  overlap proofs and their pins.
  `Audit/screen.py` describes those construction shortcuts as retired.
  `review/SCHEMA.md` replaces the obsolete overlap example with I.7, without changing a
  field or validation rule.
  `scripts/heath.py` uses I.7's surviving overlap in two self-test cases, preserving their
  accepted and rejected outcomes.

  The model generator gives declarations from the four pure modules a checked identity
  translation, retaining universe arguments, lock coverage, syntactic correspondence and
  all previous rejection tests. It translates `primitives` over the model signature. The
  plane's proved isometry and reflection supply placement, its proved Postulate 1 supplies
  the kept side, and `Rule.of_placement` proves the restricted law. `model_exists` remains
  unconditional, resting only on `propext`, `Classical.choice` and `Quot.sound`.
  `model/Model/Audit.lean` retains the existing closure pins and the unknown-`Elements.Point`
  sentinel, and checks that Model may import from Elements exactly these four modules:
  `Elements.Foundations.Superposition.Syntax`, `Elements.Foundations.Superposition.Semantics`,
  `Elements.Foundations.Superposition.Soundness` and
  `Elements.Foundations.Superposition.Restriction`, including transitive imports. Their
  declarations are checked to use only the pure modules and `Init`, with no geometric
  words, project axioms or `sorryAx`.
  `model/lakefile.toml` documents that precise import boundary; Mathlib stays in `model/`.
  `model/lock.sha256` is renewed against the regenerated lock.
  `tests/model/lock.sha256` is renewed against the same lock.
  `tests/model/laws.toml` describes placement with its kept side as the sampled sufficient
  condition for the restricted law.
  `tests/model/MODEL.md` explains the reduction, the proved model and the import boundary.
  `tests/model/search.py` retains its placement checks and checks the kept side too.
  `tests/model/hyperbolic.py` retains its placement checks and checks the kept side too.

  The I.4, I.8 and I.23 pages and the overlap catalogue now describe an inference in
  System E's style. An independent reader has read and stamped the six records for I.2,
  I.3, I.4, I.8, I.23 and I.44, retaining full coverage and Euclid's route. No equivalence
  with System E's two rules or whole-theory non-derivability is claimed. Questions 2, 4
  and 5 of the brief remain the owner's: accept the five-part restriction or require
  another formal statement; permit I.7 inside the placement despite constructions in its
  proof or require construction-free cited proofs; retain the laid-down side or revise
  the calculus and argument. The branch follows the first reading in each case. After
  `lean/retire-axioms-2`, the proofs of `triple_incidence2` from Postulate 2 and
  `eq_of_len_eq_zero` from Postulate 3 bring I.4's cited laws within question 4 too;
  `drawsNothing` and the audit pins must be reviewed again.

  Before landing, the check changes in `Certificate/Facts.lean` and `scripts/heath.py`
  must be split into a tooling pull request that lands first, as WORKFLOW, section 10,
  requires. The retirement branches must be reconciled, generated outputs regenerated,
  and the finished revision validated and independently reviewed, including the model
  and the protected paths named above. This entry records preparation, not landing
  approval; no check, expectation, lock or schema is loosened.

## 20 October 2026

- **The Jev scorer checks confidence in both askings
  ([#36](https://github.com/jackChallis/stoicheia/issues/36)).** Each Jev choice is asked
  twice, the second time with its options reversed, unless the run is made with
  `--no-order-check`; a noul is asked once. `score` in
  [`scripts/audit/jev.py`](../../scripts/audit/jev.py) sent an answer to adjudication when
  its first asking had a confidence under the threshold or none, and read the reversed
  asking only for a changed choice; it now applies the same confidence rule to the reversed
  asking too, and says which asking fell short. A line whose reversed asking is not an answer
  at all stops `score` with a failure, as it stopped it with an error before. The
  threshold stays 0.5 and exclusive. The self-test gains cases for a low, a missing and a
  null confidence in the reversed asking, a refused reversed asking that is not an answer
  (with and without a bar), a single asking, and the boundary. More answers go to adjudication, none fewer. The audit of Books
  I and II found this while scoring, and its report, on `text/jev-audit-I-II`, follows this
  change, as a check lands before the content it judges. The protected file this changes is
  `scripts/audit/jev.py`. Neither CI nor `safe_push` runs its self-test: whoever changes the
  client runs `python3 -I scripts/audit/jev.py self-test`.

- **The source scan reads the formal model too (#121).** On 19 October 2026 the scan in
  `scripts/check_fidelity.py` is extended to every `.lean` file under `model/`, without
  entering the package's own `model/.lake`, where Mathlib and the build live; a `.lake`
  folder deeper in the model is read like any other, since git tracks it and Lean can
  build it. Symbolic links to files or directories in every scanned tree and its root
  file are refused by their own paths and never followed, a link at `model/.lake` among
  them: the scan skips only what lies inside a real `model/.lake` directory, links there
  included, and never the link that stands in its place. Mathlib imports are allowed
  there, but the forbidden commands and attributes stay the same, and
  an `axiom` is refused anywhere in the model. Only `model/Check.lean` and `model/Check/`
  may use `run_cmd` first on its line followed by `Check.Generator.<ident>` or
  `(Check.Generator.<ident>`: running the generator is those files' job. The named
  allowance exempts that command alone, so its arguments and any further command are
  still scanned. The one string in the model the scan could not read for certain, the
  implicit binder's in `model/Check/Generator.lean`, line 600, became an interpolated
  string with an escaped opening brace and exactly the same output in a pull request of
  its own (`tooling/model-generator-brace`), landed before this one, since a check is
  never changed in the same pull request as the code it checks.
  `scripts/negative_tests.py` plants axioms, forbidden commands and attributes in the model's Model and Check files, tests
  the allowance's boundary and the `.lake` boundary both ways, refuses a link named
  `.lake` to a directory, a file or nothing in `model/`, `model/Model/` and
  `model/Check/`, and checks that the unplanted tree passes; it copies only `facts.json`,
  never `model/.lake`. These are the two protected files changed:
  `scripts/check_fidelity.py` and `scripts/negative_tests.py`.
  [FORMALIZATION](../FORMALIZATION.md), section 7, records the scope and the tests.
  Nothing is loosened in `Elements/`, `Staging/` or `Audit/`; Book Zero's import rule
  and the placement policy still apply only in `Elements/`. The model's independent
  kernel replay, the other half of #121, is still open.
- **The acceptance checklist in CI, held to what main passes
  ([#35](https://github.com/jackChallis/stoicheia/issues/35)).** A new job, `acceptance`, in
  [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml), runs
  [`scripts/check_acceptance.py`](../../scripts/check_acceptance.py) on every pull request,
  with the whole history for the records' commits, and keeps its reports as an artifact of
  the run. Until the consolidation release it fails only for an item that already passes on
  main and does not pass on the pull request: a pass may not turn into a fail, while the
  failures main still has (742 at #111) are reported and hold nothing back. Main is checked
  beside the pull request, in a worktree of the merge commit's first parent, with the pull
  request's own checks copied in (`scripts/`, `tests/`, `Certificate/`, `review/SCHEMA.md`
  and `review/terms.toml`), keeping main's own values pinned to its content. The new
  `scripts/copy_acceptance_checks.sh` is the helper that CI and the behavioural tests share
  to copy the pull request's checker code while preserving those pinned values, so that one
  copy of the checks judges both, and a check made stricter, which lands on its own before
  the content it judges, holds nothing back. Main's
  run leaves out the kernel replay and the model tests (E1 and E4), which the `check` and
  `model` jobs hold on every pull request. The script gains two options: `--json`, which
  writes every item's verdict beside the report, and `--compare MAIN PR`, which runs no
  check and exits 1 for each item that passes in MAIN and does not pass in PR (a fail, a
  check not run, or an item missing), and 2 for a file `--json` did not write, or for two
  files written by different copies of the script. A staging item, P10 or E6, that turns
  into a fail is listed and not held: both read `Staging/` alone, and a statement that a
  stage adds or changes is staged before its proof ([WORKFLOW](../WORKFLOW.md), section 2),
  so they turn into a fail exactly when a pull request stages one, as I.20's degenerate
  case was staged after I.20 was proved; only the full gate holds them. The lane's
  independent review found that the ratchet would have held such a pull request back, and
  that a misspelt gate turned the job off; we thank it for both.
  [`tests/test_check_acceptance.py`](../../tests/test_check_acceptance.py) (new) puts the
  comparison to small files of verdicts, and the job runs it before the checker. The full
  gate is one line of the workflow, `ACCEPTANCE_GATE: ratchet`, which the consolidation
  release's pull request sets to `full`: from then on the job skips main, and any failure
  fails it, as step 9 of [WORKFLOW](../WORKFLOW.md), section 10, asks; any other value
  fails the job at once. Nothing is loosened:
  no other job, check, test or expectation changes, and without the new options the
  script's verdicts, report and exit status are as before. The job is not a required check:
  the ruleset on main and `REQUIRED_CHECKS` in
  [`scripts/safe_push.py`](../../scripts/safe_push.py), unchanged, still name `check`,
  `model` and `negative`, and making `acceptance` one is the owner's call; even so,
  `git safe-push --merge` refuses a pull request while any of its checks fails, is cancelled
  or is still running, but a skipped or missing `acceptance` does not hold it when the
  three required jobs pass and no other check fails, is cancelled or is still running.
  The pre-flight's `CHECKS` are unchanged too, since the job builds main beside the
  pull request: like `formal-model`, it is CI's alone. The follow-up pull request
  `docs/acceptance-ci-page` will add the new section "In CI" to
  [ACCEPTANCE](../ACCEPTANCE.md) and update [WORKFLOW](../WORKFLOW.md), sections 8 and 10;
  those reader-facing documentation changes are deliberately deferred from this one.
  The review's correction changes `.github/workflows/ci.yml`,
  `scripts/copy_acceptance_checks.sh` and `tests/test_check_acceptance.py`: main keeps its
  axiom lock, certificate expectations, model hash, law names and account of the laws
  (WORKFLOW, section 10, step 4), and a regression runs the shared helper and the certificate
  checks to show that an updated definition or expected count cannot hide a pull request's
  E2 failure.

- **I.45 and II.14 are allowed as restricted while the outline proof is to come (#116).**
  On 20 October 2026 the owner approved ship G's decisions for #116, including:
  "**Interim disclosure.** Approve the restricted-scope entries in section 7 and keep
  `figure-with-dissection` until all bridges are proved and reviewed."
  This supersedes the 18 October decision to call both full under the convention of a
  figure supplied with a checked finite division. The figure is given with its checked
  division into triangles, and its area is relative to that division; existence of a
  division from the outline and independence of area from the division chosen remain to
  be proved under #116.
  `scripts/check_acceptance.py` adds I.45 and II.14 to `ALLOWED_LIMITS`, each as
  `("restricted", "figure-with-dissection")`, and [ACCEPTANCE's table](../ACCEPTANCE.md#the-limitations-allowed)
  gains the same two rows. They go when the outline proof is proved and reviewed.
  The record change follows on a text branch of its own, stacked on this tooling change.
  The protected files changed are `scripts/check_acceptance.py`, whose only change is
  those entries and their comment, and `tests/test_acceptance_limits.py` (new), which checks
  the list against the table and exercises P3 with and without the required tag. CI does
  not run it yet; whoever changes the limitations runs it.

- **Exact counts in prose are rendered and checked.** The stale-content audit found the
  vocabulary still given as 61 where the lock held 91, and companions as nineteen across
  seven propositions where the list held twenty across eight. The owner asked for a rule
  that catches such drift. Inline HTML comments, `count:name` and `/count`, delimit just
  the number; `:word` spells it out and `:Word` capitalises its first letter. The syntax,
  shown with its opening brackets escaped in [STYLE](../STYLE.md), section 4, is distinct
  from the existing scope and status regions and leaves no visible delimiters in Markdown.
  Only counts computed exactly from files are generated: the lock's axioms, tacit rules
  and postulates, using the renderer's existing classification, the axioms other than
  Postulate 5, and its vocabulary; the
  listed companions and the propositions they widen; each book's records and those at
  stage `full`; and the acceptance report's failing items and propositions passing every
  own item, read from its generated summary at that report's revision. Surrounding prose
  stays human. No Lean run is needed to compute or check a count.
  `render.py` fills markers in tracked Markdown before copying introductions and other
  prose into book pages, where it removes the count comments. Whole renderer outputs are
  excluded. Markers that overlap README.md's generated scope regions or PROGRAM.md's
  generated status region, including their delimiters, are refused before rendering,
  since those regions are replaced. Markers are refused in this decisions log and throughout `docs/reports/`,
  except the living `gaps-book-*.md` and `overlaps.md` catalogues, so dated evidence stays
  at its revision. Unknown, malformed, nested and unclosed markers fail with file and
  line. `check_fidelity.py`, already run before rendering, also refuses a stale value,
  giving the name, stated and computed values, and the command to regenerate.
  Small fixtures test each count and the marker boundaries; negative tests plant wrong,
  unknown and correct counts in a source copy under `/tmp`, without a build. Their
  `--counts-only` option runs those plants and the file-only regressions; the default
  suite still runs every plant. This is the tooling branch only. A later content branch
  adds markers to the prose. The protected files changed are
  `scripts/generated_counts.py`, `scripts/render.py`, `scripts/check_fidelity.py`,
  `scripts/negative_tests.py` and `tests/test_generated_counts.py`.
- **Count discovery and rendering refuse unsafe inputs.** Following the code and
  security reviews, Git's resolved work tree must match the supplied root, including
  copies using `GIT_DIR` and `GIT_WORK_TREE`. Missing or mismatched metadata fails with
  a diagnostic. Symlinks in every component below the repository root, and paths resolving
  outside the root, are refused before an optional input is tested for presence, or a path
  is read or written; a symlink supplied as the root itself remains a supported alias.
  Whole renderer outputs are now scanned and any count marker there is refused; this
  supersedes their exclusion in the entry above.
  Review counts use tracked records alone and check proposition numbers. Regressions
  cover these boundaries and run rendering from a stale marked introduction through
  to its updated source and copied page without count comments. The protected paths
  changed by this branch are `scripts/generated_counts.py`, `scripts/render.py`,
  `scripts/check_fidelity.py`, `scripts/negative_tests.py` and
  `tests/test_generated_counts.py`.

- **A check for merge-conflict markers.** Pull request #138 left a diff3 base marker and a
  duplicated, outdated fragment on this page, and nothing caught it; the owner asked for a
  rule to catch such residue. S23 of `scripts/check_style.py` ([STYLE](../STYLE.md),
  section 8) reads every tracked text file, fenced code and comments included, and refuses
  an opening, base or closing marker (exactly seven characters, then a space or the line's
  end), and a seven-equals middle between markers or where it cannot underline a Markdown
  paragraph, since a resolver can delete the outer markers and leave a middle, as #138
  left a base. Setext headings stay allowed, including paragraphs of several lines.
  The check tracks comments, fences, HTML blocks, GFM tables, completed headings,
  indented code and link reference definitions; a fence inside a comment or HTML block
  opens no block. It skips symlinks,
  and traversal errors name their path and stop the check. The walk without Git serves
  S23 alone; S12 loads its strictly Git-backed index only when needed. The updated S23
  finds no marker in origin/main's 1,100 text files at `d95125f0`.
  The style check is its home because it
  already holds the repository's file-and-line rules and runs in CI and the pre-flight
  with its cases; `check_fidelity.py` judges the Lean, Heath's text and the certificate,
  and the Jev audit is an independent model's reading, not a mechanical check. Planted
  markers in `scripts/negative_tests.py` (item 16) and cases in `tests/test_check_style.py`
  show each kind refused, the block boundaries held, traversal errors raised, symlinks
  skipped and valid setext headings allowed. By keep_apart (WORKFLOW, section 10),
  the rule lands apart from the content fix, `text/decisions-marker` (#140), which removed
  the marker first; on main since #140 it finds none. The protected files changed are `scripts/check_style.py`,
  `scripts/negative_tests.py` and `tests/test_check_style.py`.
- **S23 errs toward refusal for possible reference definitions.** A lone Markdown middle
  is allowed only when every line of the preceding block is ordinary paragraph text;
  any line beginning with up to three spaces, a bracketed label (escaped brackets
  included) and a colon disqualifies the block until its next boundary, as does a block
  quote or list item, since an underline is never a lazy continuation. Within a
  paragraph, as in GFM, only a list item that can interrupt it counts: a bullet, or an
  ordered item numbered 1, with some text. `2. item`, `1.` or a bare `*` goes on with
  the paragraph, which a seven-equals line may underline; at a block's start any list
  item disqualifies the block.
  S23 examines only middles of exactly seven equals and errs toward refusal in doubtful
  contexts, so an author whose heading is refused can use eight, since other lengths are
  never examined as middles.
  This deliberately refuses `[label]: destination extra words` with seven equals even
  though it is paragraph text. `scripts/check_style.py` retains the possible definition
  across destination and title continuations. `tests/test_check_style.py` covers the
  three reported escapes, the conservative refusal, the eight-equals alternative,
  list markers that cannot interrupt a paragraph and ordinary headings across block
  boundaries; `scripts/negative_tests.py` adds a two-line
  definition to item 16. These are the three protected paths changed; [STYLE](../STYLE.md)
  states the rule. No mathematical statement or review record changes.

- **The circle ban survives a rule being proved.** The check change precedes the
  retirement, with all 87 axioms still in place. No certificate entry may rest on
  Circle 2 (`Tacit.inside_of_between`) or Circle 3 (`Tacit.outside_of_between`).
  [`Certificate/Facts.lean`](../../Certificate/Facts.lean) now finds every theorem
  this project declares in `Elements.Tacit` and records Lean's `collectAxioms` for it
  in `facts.json` as `proved_rules`, documented in
  [`Certificate/FIELDS.md`](../../Certificate/FIELDS.md).
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py) requires each
  forbidden name either to remain an axiom in the lock or to name a proved rule
  resting on another forbidden circle rule that remains an axiom there. The
  per-entry refusal is unchanged: in the planned retirement, Circle 2 is proved
  from Circle 3, so every use still brings in a forbidden axiom. A renamed rule or
  a proof without a forbidden axiom beneath it is refused.
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) plants both cases
  of proved Circle 2, restores the lock, and drops one project axiom from
  `Audit.III_2`'s pin whether its list occupies one line or several.
  [`tests/test_negative_tests.py`](../../tests/test_negative_tests.py) checks the
  guard, both pin forms and restoration on failure or interruption.
  [FORMALIZATION](../FORMALIZATION.md), section 7, records how the ban continues
  to hold. This prepares the checks for the retirement; it retires no axiom.
- **Eight axioms retired, 87 to 79.** The owner asked,
  "Fewer axioms is better. Any more that can go?", and on 19 October 2026 approved both
  retirements: "Please do both. 79 is rather large with so many books in front of us." On
  20 October the owner approved landing each as three pull requests; this is the second of
  the first. Pins that III.1, III.1 Por., III.2 and II.14 rest on none of the eight, able
  to fail now that the eight are theorems, are #168, which holds every release until it
  closes. Each of the eight keeps its name and exact type and becomes a theorem at the
  earliest place it can be proved: `Tacit.centre_unique`, `Tacit.inside_of_between`
  (Circle 2, from Circle 3, which stays), `Tacit.exists_point_outside_circle`,
  `Tacit.line_meets_circle_of_opposite_sides` and `Tacit.triple_incidence3` in
  [`Elements/Figure/Circles.lean`](../../Elements/Figure/Circles.lean);
  `Tacit.not_same_side_of_circles_meet` (Circle 4) after I.7; and
  `Tacit.adjacent_eq_of_right` and `Tacit.inside_of_angle_add` after I.13. No proof rests on
  the axiom it replaces or on a later proposition, and I.7 and I.13 do not rest on their
  corollaries. The first four came from a probe; the other four are the derivable rules
  that lie on no cycle of the derivation graph, so no later choice of basis can disturb
  them. The rest of the search, what else could go and what each choice costs, is evidence
  for the owner, not part of this change. I.7's audited shortcut through Circle 4 is
  circular now, and the audit says so. I.12, which cited the intersection rule now proved
  from Circle 3, cuts its circle instead through a point inside it, the crossing of CD with
  AB (Intersection 3), so that no certificate entry rests on Circle 2 or Circle 3; the pins
  of #60 for II.14, III.1 and III.2 still say so, through their exclusion of Circle 3. The
  axioms leave
  `Elements/Foundations/Tacit/Constructions.lean`, `Diagram.lean` and `Transfer.lean`.
  Protected files changed with them, as values pinned to the axioms:
  [`Certificate/axioms.lock`](../../Certificate/axioms.lock), written by `--write-lock`;
  [`tests/model/lock.sha256`](../../tests/model/lock.sha256) and `model/lock.sha256`;
  [`tests/model/laws.toml`](../../tests/model/laws.toml), and the eight laws' code in
  [`tests/model/search.py`](../../tests/model/search.py) and
  [`tests/model/hyperbolic.py`](../../tests/model/hyperbolic.py), the other laws in their
  order. [`tests/model/MODEL.md`](../../tests/model/MODEL.md) follows the smaller lock.
  The results of `run.py --full --write` are recorded in
  [`tests/model/results/angle_check.txt`](../../tests/model/results/angle_check.txt),
  [`tests/model/results/exhaustive.txt`](../../tests/model/results/exhaustive.txt),
  [`tests/model/results/grid_check.txt`](../../tests/model/results/grid_check.txt),
  [`tests/model/results/hyperbolic.txt`](../../tests/model/results/hyperbolic.txt),
  [`tests/model/results/mutations.txt`](../../tests/model/results/mutations.txt),
  [`tests/model/results/search-seed1.txt`](../../tests/model/results/search-seed1.txt),
  [`tests/model/results/search-seed2.txt`](../../tests/model/results/search-seed2.txt),
  [`tests/model/results/search-seed3.txt`](../../tests/model/results/search-seed3.txt),
  [`tests/model/results/structured.txt`](../../tests/model/results/structured.txt) and
  [`tests/model/results/summary.txt`](../../tests/model/results/summary.txt).
  The examples of the certificate's fields and of the review schema, which are check
  inputs, follow in a change of their own, landed after this one.
  [`Audit/Overlaps.lean`](../../Audit/Overlaps.lean) imports the proved rules, updates its
  exact axiom pins to follow the retired rules' proofs and labels the circular derivations;
  [`Audit/screen.py`](../../Audit/screen.py) removes the five retired rules from its list
  of circle axioms and explains why I.7 is no longer an independent overlap.
  [`model/Model/Audit.lean`](../../model/Model/Audit.lean) changes only comments to explain
  the 79-law assembly and retention of the eight individual audits, with every guard and
  axiom pin unchanged.
  [`tests/certificate_expectations.json`](../../tests/certificate_expectations.json) keeps
  the measured counts of III.1 and its porism (55 tacit rules each) and gains pins that
  keep the eight names out of the axiom lists of III.1, III.1 Por., III.2 and II.14. With
  the eight now theorems those pins cannot fail; the pins that hold are the counts and the
  exclusion of Circle 3, which keeps Circle 2 out too, since Circle 2 rests on it (III.1
  Por. does use the proved `Tacit.centre_unique`). The formal model's generated
  laws, checks and assembly follow from its generator; its proofs in the plane stay, as
  derived facts. The five files `model/Check/Angles.lean`, `model/Check/Circles.lean`,
  `model/Check/Incidence.lean`, `model/Check/Intersections.lean` and `model/Check/Sides.lean`
  compare the eleven hand translations of the eight rules directly with the library's
  declarations, binder kinds included, so the comparisons stand now that the eight are
  theorems; [`model/README.md`](../../model/README.md) and the hand-translated law files
  say so. Proposition and porism statements, definitions and `--` lines are
  unchanged; the records whose Lean changed were read again and stamped by readers who
  wrote none of them.
  On integration with main at `209d71fd`, `Audit/Overlaps.lean` also updates the exact
  pin for `Audit.III_30_measure`: Lean no longer prints `Tacit.adjacent_eq_of_right`,
  now a theorem, and prints every other entry unchanged. The guard remains exact.
- **The certificate's and the schema's examples follow the eight retired axioms.** A
  check-input change of its own, landed after the retirement of the eight (87 to 79), which
  leaves the check inputs not pinned to the axioms alone.
  [`Certificate/FIELDS.md`](../../Certificate/FIELDS.md) updates its axiom examples and
  the counts for III.1 and its porism because `centre_unique` and Circle 2 are now theorems.
  [`review/SCHEMA.md`](../../review/SCHEMA.md) updates its overlap examples to distinguish
  current axioms from proved rules; its fields, requirements and worked TOML examples stay
  unchanged.
  [`Certificate/FIELDS.md`](../../Certificate/FIELDS.md) also marks I.5's inherited
  Postulate 3 example as an excerpt.
  [`scripts/heath.py`](../../scripts/heath.py) uses the retained Circle 3 axiom in its
  overlap error message's example.
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) explains that its
  Circle 2 plant deliberately puts a theorem's name in an axiom list, and that the Circle 3
  rename also invalidates III.2's `[overlap]`, although the plant does not rely on that
  failure; the plants stay unchanged.
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) repairs its
  expectation-drop test, which the retirement broke: it injected the retired name
  `Tacit.centre_unique` into III.1's axiom list, and the commit's own pass refuses a name
  that is no axiom. It now injects `Tacit.circle_eq`, a locked tacit rule III.1 does not
  use, caught by III.1's count of tacit rules, and still drops III.1's axioms expectations
  in the same commit to verify that the check change stays separate from content changes;
  its corrected introduction describes that fixture without saying III.1's current
  certificate contains `centre_unique`. The test now first asserts that III.1 does not
  already use the rule, and looks in origin/main's failure for the count instead of the
  excluded name; its other assertions stay.
  [`tests/certificate_expectations.json`](../../tests/certificate_expectations.json)
  changes only its reasons: exclusions of retired names do not detect uses of the
  theorems, while the existing Circle 3 exclusions still constrain dependencies.
  Every expectation value stays unchanged. No check, field or requirement changes.

- **Review schema wording.** [review/SCHEMA.md](../../review/SCHEMA.md) now describes the
  style check's reading of review notes, distinguishes items the schema permits from
  verdicts that count for acceptance, and records I.40's completed stage-2 change, to match
  the checks and records on main. The TOML fixtures read by `scripts/heath.py` and the
  checks' requirements are unchanged.

- **The stage test reads the program's words.**
  `test_renderer_validation_loosened_with_content_is_kept_apart` in
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py), a protected file,
  quoted Book I's stage words from [`docs/program.toml`](../program.toml) to plant a
  stage [`render.py`](../../scripts/render.py) does not know. It now reads the first
  stage line from the file, so that the program's words can change without changing
  this test. It plants the same fault and expects the same refusal; nothing it checks
  is loosened. This test change lands on its own, in train H10, before the stage words
  change in train D4 ([WORKFLOW](../WORKFLOW.md), section 10: a check lands first). The
  protected file changed is `scripts/test_safe_push.py`.

- **S12 reads "Revision" as "revision".** The acceptance report's "Revision" header
  sent the commit identifier `d95125f0` to Lean as a name.
  [scripts/check_style.py](../../scripts/check_style.py) now reads "Revision" as
  "revision"; all other context words keep their case-sensitive matching. The
  commit-shape test is unchanged and nothing else is excused.
  [tests/test_check_style.py](../../tests/test_check_style.py) covers that
  header, the same hex word without revision context and a non-commit word beside
  "Revision", and keeps the unknown Lean name in sentences beginning "Read", "Reviewed"
  and "Verification" subject to Lean checking. These are the two protected files changed.

- **The modern figure's checks precede its place on the page.** The owner asked for
  figures for the modern mathematics, drawn to match Euclid's figure and carrying the
  same letters (#49). S24 checks `figures/<book>/NN-modern.svg`: Euclid's figure's canvas
  width, palette and strokes; the title "I.N: the modern way", with no caption; a Euclid's
  figure beside it; and a paragraph opening "**The modern way.**" in its mishnah.
  S25 checks its text at size 17: Euclid's figure's letters upright, and the paragraph's
  own lower-case names italic, with numbers and the signs of an expression. It reads names
  in TeX and plain words, including Book II's "AC = a", but excludes English letters
  after apostrophes, those of e.g. and i.e., and the article "a" unless a sign, digit or
  bracket stands beside it. Comments, code and link targets supply no names.
  The shared `check_style.modern_span` selects the paragraph from the original Markdown
  blocks and retains its source offsets before comments and code are masked: indented
  code supplies no paragraph, multiline inline comments preserve its boundaries, and
  code spans across lines supply no names. Its regression cases stay with these checks.
  The rules are S24 and S25, formerly S23 and S24 on this branch; S22 remains letters in
  backticks, S23 checks merge-conflict markers (`tooling/no-conflict-markers`), and S26
  checks one letter, one point (`tooling/letter-check`, #68). The hard rules now run from
  S1 to S26.
  Acceptance assigns both modern rules to P8 and each modern figure's findings
  to its proposition; S22 remains a text rule.
  These checks read the source paragraph and SVGs, not the generated page, and apply to
  the thirty modern figures already on main. Train H10 carries the checks; the page
  insertion, its two renderer tests, the regenerated pages and the checklist's P8 sentence
  follow in train F1. `scripts/render.py` and `docs/ACCEPTANCE.md` keep main's copies.
  The protected files changed are
  [scripts/check_style.py](../../scripts/check_style.py),
  [scripts/check_acceptance.py](../../scripts/check_acceptance.py) and
  [tests/test_check_style.py](../../tests/test_check_style.py).
  [STYLE](../STYLE.md), sections 2, 7 and 8, describes the figure and its rules.
  The reviews' fixes close S24 and S25's input: the modern figure may use only the elements,
  attributes and spellings the modern figures on main use, so no CSS is read; a malformed
  figure is reported on its file and checking goes on; and a modern paragraph with inline
  HTML or reference-link syntax is refused, its indentation counted in columns.
  After merges `ce98e710` and `57a5a94f`, `scripts/check_style.py` restores `93d61b6c`'s
  table reading as `modern_table_columns` and `modern_table_cell_ranges`, and its
  companion lookup as `modern_drawn_letters`, with `modern_text_of` preserving internal
  newlines, keeping S23, S26 and the idea-figure checks' helpers unchanged, with the S24
  and S25 refusals covered in `tests/test_check_style.py`.
  The fixes through `12667af1` retain these separate readers while tightening modern
  SVG input and modern-paragraph markup checks; S23, S26 and the idea-figure checks
  keep their existing readings.

- **One letter, one point: S26.** Argon's second review of the book-III release found seven
  letters of Euclid's figures crossed or all but touched by strokes: III.17's D, III.16's G,
  III.8's K and L, III.33's F in two of its three figures, and I.2's E. We thank Argon
  warmly for so careful an audit
  ([#68](https://github.com/jackChallis/stoicheia/issues/68)). The issue read the seven as
  letters naming two points; what Argon measured was strokes through letters, and the rule
  holds a figure to both. [`scripts/check_style.py`](../../scripts/check_style.py) gains a
  rule, S26, which fails a figure, Euclid's or at a glance, that draws a letter twice (save
  once in each of Heath's figures side by side, in III.25, III.33, III.35 and III.36, split
  at straight cuts the script gives), or that lets a stroke, a dot or the canvas's edge come
  within 2 of a letter. A letter is measured as Georgia draws its capital, upright or italic
  as the figure sets it, by the convex hull of its outline's points, which the script
  carries as numbers (`GLYPHS_UPRIGHT`, `GLYPHS_ITALIC`), read once from the fonts, so that
  it still needs only Python's standard library; `path_rings` now also says which subpaths a
  Z closes. S20 now reads only figures the gate admits, flattens curves adaptively to within
  0.001, and retains significant Unicode spaces in text rather than stripping them.
  [`tests/test_check_style.py`](../../tests/test_check_style.py) gains cases of S26,
  among them one or more for each of seven faults that two reviews of the rule found: a
  stroke's width taken at a transform's mean stretch, a rect's rounded corners read as
  square, a circle of no radius read as drawn, an anchored label with a prime placed by its
  capital alone, a letter drawn twice in one of the figures side by side counted as once in
  each, a corner's radius spelled 5e1 read as none, and a line of no length with butt caps
  read as drawn; and, from the independent review, cases for what none of them had pinned:
  an ellipse, a polyline, a dot or a stroke wholly within a letter, the canvas's right, top
  and foot, a letter's size and transform, and a prime; and, from a later review, three on
  what a line through a letter is called: two dashed by itself or by its group, called a
  dashed line, and one whose dasharray is none, called a line. A corner's radius is now
  read in one pass, so reading a malformed radius takes time linear in its length.
  The CSS width, scale transforms and exponent radius began as geometry cases; once the
  gate closed the input language, their cases instead require their exact refusal, while
  every admitted clearance case remains a test of the geometry.
  Later reviews found, one after another, SVG spellings that a renderer reads one way and
  S26 another; S26 now reads only the elements, attributes and spellings that the figures
  on main use and refuses any other, so no CSS is read, and it measures circles, ellipses,
  arcs, rounded corners and curves with a conservative allowance for their chords. The
  final review's fixes in `scripts/check_style.py`, with regressions in
  `tests/test_check_style.py`, refuse effective strokes and bold weights on point labels
  (main's bold numbers remain allowed), retain significant Unicode spaces for refusal, and
  require both ellipse radii and an effective `font-family` on point labels of `Georgia`,
  `Georgia, serif` or `Georgia, 'Times New Roman', serif`, inherited or explicit.
  Numeric inputs are limited to magnitude 10,000, against
  main's largest input of 440 at `209d71fd`; cubic subdivision has a depth limit, and
  non-finite intermediate results fail the figure; an iterative gate limits nesting to
  16 levels below the root before recursive helpers run. Decoder errors are caught at the
  parser call. Both entry points have regressions requiring the next figure's finding after an
  arithmetic or encoding failure. Subdivision is bounded for each cubic; these limits do
  not bound the input's length or its number of elements or path commands.
  The protected files changed by the DTD correction are `scripts/check_style.py` and
  `tests/test_check_style.py`. Every figure reader now scans the bytes for `<!DOCTYPE`
  and `<!ENTITY` before constructing a parser, then parses those same bytes. The scan
  removes NULs so UTF-16 and UTF-32 spellings are caught too, and deliberately refuses
  declaration markers inside comments. ElementTree's pure-Python fallback omits the
  doctype callback for bare declarations and internal subsets alone; the byte guard
  makes refusal independent of that callback, which remains a second guard. The
  tests pin the single S26 diagnostic and continuation for SYSTEM and PUBLIC
  declarations with internal subsets, entities referenced in attributes and text,
  a referenced parameter entity, undeclared references and markers throughout the
  document. An isolated subprocess disables the C accelerator before import and
  checks temporary copies of I.1's figures and the declaration cases with the real
  fallback. Ordinary XML declarations, comments and character references remain
  admitted; an undeclared reference without a DTD retains its malformed-SVG finding.
  The combined parser guards supplied source bytes too, and S25's companion reader
  shares that refusal, returning `None` while retaining `modern_text_of`'s exact
  reading of the text; its regression also runs with the pure-Python parser.
  Mitre joins now use original segments' endpoint tangents, with no joins between a
  curve's flattened chords. The closed text language admits only Heath's letters and
  ASCII integer annotations, so Greek, full-width and other unmeasured text cannot pass
  unseen. Zero fill and stroke opacity are refused on shapes and ancestor groups, while
  main's positive opacity spellings remain admitted. Each path subpath now keeps its own
  conservative chord allowance, so a remote arc cannot widen an unrelated straight
  subpath's clearance measure. The gate also requires the SVG namespace and the figures'
  container-and-leaf structure before measuring anything. A point label with effective
  fill none is refused, while a visible explicit fill still overrides an ancestor's none.
  Both figure entry points have cases requiring an S26 finding. And
  [`scripts/check_acceptance.py`](../../scripts/check_acceptance.py)
  files its findings under P8, the figures. The matching words in
  [ACCEPTANCE](../ACCEPTANCE.md) follow in the content train; this branch keeps that
  page exactly as it is on origin/main.
  [STYLE](../STYLE.md), sections 7 and 8, gives the rule, and the reviewer's checklist, item
  16, asks that a letter naming one of Heath's points name no straight line or circle in the
  Lean. A rule is added and nothing is weakened. The earlier figure work for #68 corrects
  fifteen labels, III.16's G among them, through `text/letter-collisions`. G's correction
  is in `a4cb748c`, brought into train D3 by `c2424533`.

  This check change lands in train H10 before the content it judges, with the checklist's
  words following in the content train, as H9b followed H8b for style everywhere. Its number
  is S26: S22 is "letters in backticks, where they are plain"; S23 checks merge-conflict
  markers, and S24 and S25 check the modern figure. All four rules are included in train
  H10. Main's checks, cases, REACH_PENDING and
  reports, including D15 for italic figures and D16 for the pending reach, stay whole.
  The follow-up through `daf4bec7` brings S26's processing-instruction refusal and quiet
  companion lookup on parse failure into H10, while the modern rules keep their byte
  parser and readers and S23 keeps main's helpers.

- **The modern figure is shown beneath its paragraph (#49).**
  [scripts/render.py](../../scripts/render.py) places each existing modern figure
  immediately after its whole modern way paragraph, with a blank line on each side;
  [STYLE](../STYLE.md), sections 2 and 7, now describes that placement as present.
  It uses `check_style.modern_span`, preserving source indentation, comments and code,
  and checks placement and refusal against ten cases before writing pages. An existing
  modern figure with no valid paragraph stops the render with a diagnostic naming the
  proposition, the figure and the missing paragraph, including when the mishnah file
  is absent. With no modern figure, rendering is unchanged.
  [tests/test_check_style.py](../../tests/test_check_style.py) gains the two renderer
  regression tests for an absent mishnah and an absent modern figure; its placement and
  page caller tests now require refusal when the paragraph is missing or invalid, while
  keeping the positive cases. The original placement change was content:
  [WORKFLOW](../WORKFLOW.md), section 10, says, "A change to what `render.py` writes is
  not a check change in this sense, since the pages it regenerates show it".
  These orders keep the output regression tests with that content; they add checks of
  the output, while the source figure rules S24 and S25 precede it in train H10.
  The refusal changes what the renderer accepts: `scripts/render.py` and
  `tests/test_check_style.py` are the guard changes for `security-review`.
  Train F1 carries the renderer and its regenerated pages. Because origin/main's
  renderer would write those pages without the figures, `scripts/safe_push.py` counts
  the change as a check change, which lands apart from content the checks judge; so
  [ACCEPTANCE](../ACCEPTANCE.md)'s P8 words for S24 and S25 and for the letter rule S26
  follow in train F2, with the eight further figures of the modern way.

- **A standing read for stale content.** The A0 read of 20 October found claims false on
  main and others that queued work would make false, beyond what mechanical checks can
  judge. Before every release and at the end of each programme stage, the coordinator
  assigns an independent reviewer the read set out in
  [docs/WORKFLOW.md](../WORKFLOW.md#10-how-a-book-is-made-and-released), section 10,
  step 8; [docs/PROGRAM.md](../PROGRAM.md#5-lessons), section 5, records its first
  instance and the conflict marker and stale counts that prompted separate checks.
  Findings go in dated reports under `docs/reports/`, and fixes in the trains or pull
  requests that make them true. The existing step numbers stay, preserving ACCEPTANCE's
  citation of step 9. No check changes.
- **Content kept fresh in four tiers, and the release gate (#164).** On 20 October 2026
  the owner approved a process for keeping hand-written content true: defects (a conflict
  marker, a broken link, the owner's name, a claim the Lean contradicts, a failing check)
  are never on main; facts (counts, status tables, the acceptance report, the certificate)
  are generated, never written by hand; reader prose is true at release, fixed in the train
  that changes the fact or at the latest in the release's pull request; working records
  (briefs, reports, issues, the tracker) are dated, with status notes when overtaken, and
  the issues and tracker kept current. A release waits for its gate: a read for stale
  content on the candidate, its Tier 0 to 2 findings fixed and its Tier 3 records noted;
  the wiki refreshed, reasonably correct as of its date and not expected to be more
  current; the notes approved before the tag. The same day the owner ruled that
  unfinished or prototype work may be on main only as an open issue labelled
  `blocks-release`, and that no release goes out while one is open; the check that holds
  a release on that label comes in its own pull request. WORKFLOW, section 10 (steps 8
  and 10, and the landing section's list of required checks, which the owner extended on
  20 October to `formal-model` and `acceptance`), and PROGRAM, section 2, now say so.
  GitHub's ruleset requires all five checks. `scripts/safe_push.py` still tests for the
  presence of a passing run only for `check`, `model` and `negative`, while refusing any
  reported failure or pending check; aligning that local test is a separate follow-up
  requiring its own protected-check change. No check changes here.
- **Current lock totals carry inline count markers.** The owner asked for the current
  totals in handwritten prose to follow the lock. The markers surround the number alone:
  `README.md` has the total in the formal-model row; `Certificate/FIELDS.md` has the
  current vocabulary total; `docs/FORMALIZATION.md` has the tacit-rule and axiom totals
  in the foundations policy and the axiom total in the model row; `docs/PROGRAM.md` has
  the model's axiom total and the vocabulary total; `docs/briefs/book-I.md` has the
  tacit-rule total; `model/README.md` has the lock totals in its introduction,
  translation and dependency accounts, the total apart from Postulate 5, and only the
  denominator of the assembly's coverage; `tests/model/MODEL.md` has the axiom and
  tacit-rule totals in its introduction and model account, and the totals apart from
  Postulate 5 in its hyperbolic and formal-model accounts. There are 29 markers.
  The two current vocabulary totals change from 61 to 91. PROGRAM's statement-only
  subset changes by hand from 24 to 54: the generated vocabulary table in
  `model/Model/Laws.lean` has 37 distinct names, all in the lock's 91-entry vocabulary,
  and its recorded SHA-256 matches the current lock. Subtracting those names leaves
  54. The 37 stays, and neither subset gets a marker, since the tooling computes
  neither subset.
  Euclid's five postulates, historical counts, primitive-word and proof-coverage counts
  stay human. In particular, the assembly's first 87 stays human, as does "all 87" in
  `model/Model/Audit.lean`: the tooling reads tracked Markdown only, so that Lean comment
  remains an open manual count. A grep of `mishnah/intro/` found no eligible lock total.
  The existing block between `counts:begin` and `counts:end` in `tests/model/MODEL.md`
  is written by `tests/model/run.py --full --write`: its dated numerical results and
  axiom-by-axiom table stay untouched. README's scope rows and PROGRAM's status table
  stay untouched too.
  The tooling that reads the markers landed first, in #166: `scripts/render.py` fills
  them, and `scripts/check_fidelity.py` checks them against the lock. The protected files changed here are `Certificate/FIELDS.md` and
  `tests/model/MODEL.md`; no check, declaration, lock or review record changes.

- **The Jev audit's question generator.** On 19 October 2026 the owner approved running Jev,
  TypeSafe's decision model, as the independent audit of brief 0005's stage 6
  ([#36](https://github.com/jackChallis/stoicheia/issues/36)) on Books I and II, whose 62
  records are at the stage `full`.
  [`scripts/audit/jev_questions.py`](../../scripts/audit/jev_questions.py) (new) writes that
  audit's questions, in the rows that [`scripts/audit/jev.py`](../../scripts/audit/jev.py)
  sends, for review items P11 to P15 of [ACCEPTANCE](../ACCEPTANCE.md): the statement's
  scope, with its companions and porism; whether each proposition a proof unit calls does
  work, and whether any hypothesis is used only for show; whether each record's
  representation claim is right, including `n/a` as the claim that no bridge is required,
  and, for a supplied bridge, whether it is stated. Every one of the 62 propositions gets
  this question. Dependency placement is supplied as context but not itself adjudicated,
  and a bridge-stated answer is not all of P13. The questions also ask whether the
  commentary's account of the scope, the route and the Lean it names agrees with them; and
  whether the Heath figure, sent as an image, agrees with the proof and its caption.
  Production states quote their files exactly, checked byte for byte against `git show`
  of a named commit, and the expected answers, taken from the records, stay on this machine.
  Ten seeded controls, each a planted defect in a generated row only, measure whether the
  questions can find a fault. It
  refuses absolute evidence paths, parent traversal or evidence resolving outside the
  repository, symlinks in evidence or either output path, and output collisions with
  evidence, tracked files other than the two default outputs, case-only aliases of tracked
  files even when the tracked path is missing, or each other.
  `scripts/audit/jev_questions.py` also refuses Git metadata and protected paths from
  AGENTS.md and the lists in `scripts/safe_push.py`, independently of the index, including
  their aliases, and guards every input before a Heath helper opens it.
  An output outside the repository is allowed, and replacement never follows a final
  symlink; the checks cover existing links and aliases, excluding a concurrent writer
  racing them in the same tree.
  It uses the standard library alone, reads no key and sends nothing;
  `--commit REV --check` regenerates the rows twice and compares them with both files.
  [`tests/test_jev_questions.py`](../../tests/test_jev_questions.py) (new) tests the file
  containment and all ten controls, including the two commentary mutations, with no Lean,
  network or key; CI does not run it yet. The added cases in `tests/test_jev_questions.py`
  verify protection without index entries and refusal before an outside target is opened.
  The generator lands on its own, before the rows,
  results and report it produces (`text/jev-audit-I-II`), as keep_apart asks. No existing
  check is weakened, and no schema or record expectation changes.

- **The restricted-superposition certificate tooling lands before the Lean replacement.**
  For issue #75 and [brief 0009](0009-superposition.md), the coordinator approves this
  strengthening before the content branch lands. `Certificate/Facts.lean` counts C.N. 4
  when a walked local declaration's value names `Elements.Superposition.Coincidence.step`.
  The later calculus declares `Coincidence : Prop` with that one constructor; each of
  `Derives.len_congr`, `Derives.angle_congr` and `Derives.area_congr` takes a first explicit
  argument `(cn4 : Coincidence)`. Derivations taking the step supply `.step` or `⟨⟩`.
  Transformers such as `Derives.map` pass the marker they receive as a bound variable.
  Counting the three congruence constructors instead gave false C.N. 4 reports whenever
  a proof reached a transformer that rebuilds all three, even on a derivation with no
  congruence step. There is no list of eliminators to skip: that could hide a real use.

  `Certificate/FIELDS.md` and the emitter's docstrings state the exact semantics. Like
  `#print axioms`, the report follows what proof terms name, through the local declarations
  they name, without evaluating them. Passing a bound marker adds no step; a helper that
  names the constant counts even when evaluation would take another branch. Merely
  reaching an inductive type's constructor list does not count. The marker changes no
  axiom walk; the module boundary is strengthened below. A single backtick names the
  marker without requiring it to exist, so the tooling runs on main before the calculus
  exists and leaves main's facts unchanged.

  `tests/fixtures/CertificateCN4.lean` declares exact-name stand-ins for the marker and
  the three congruence constructors, a `Derives.map` that rebuilds every constructor and
  passes its marker along, and a soundness-style eliminator. `tests/test_certificate.py`
  runs an unmodified copy of the emitter against this fixture as a temporary package's
  `Elements` module, with the built foundations available and all output kept temporary.
  Each congruence constructor counts directly, through a helper, and through both
  transformers. Given derivations through either transformer or both do not count; the
  type-only and other-constructor controls remain. Bound markers do not count; a helper
  that names a step does. All sixteen entries retain the same non-empty axiom fields.
  The positive direct and helper cases fail against origin/main's old emitter, which has
  no calculus detection; constructor counting passes those positives but fails the
  transformer and bound-marker controls. These are separate regression baselines.

  With the coordinator's approval, `.github/workflows/ci.yml` and `scripts/safe_push.py`
  run `python3 -I tests/test_certificate.py` immediately after
  `lake env lean Certificate/Facts.lean`, as does [WORKFLOW](../WORKFLOW.md), section 8's
  command block. `scripts/test_safe_push.py` parses the workflow with PyYAML 6.0.3, pinned
  in `scripts/requirements-test_safe_push.txt`, and compares all three command sequences
  through a normalized `jobs.check` model. It pins that position and rejects job or step
  conditions, job dependencies, shell overrides, continuation settings other than
  `continue-on-error: false`, and extra commands in a required check's run body. The one
  multi-command body runs the renderer, prints generated-file freshness and asserts that
  the output is empty. [WORKFLOW](../WORKFLOW.md), section 10 gives the pinned install
  immediately before the guard suite. `scripts/negative_tests.py` plants constructor
  counting, requires the focused test to reject its false report, restores the source in
  `finally`, and requires the restored regression to pass. This fits the harness's existing
  pattern of a source fault caught by a separate check; it runs only in a disposable tree.
  `tests/test_negative_tests.py` checks restoration on interruption.

  `scripts/heath.py` uses `Tacit.angle_le_two_right`, which supplies I.13's upper bound
  on an angle in `Prop47.within`, for its overlap self-test, with the same acceptance of
  a complete `step` record and rejection when its note is missing. No check is weakened.
  For the same reason `review/SCHEMA.md` gives the same overlap as its example of the kind
  `step`, in place of I.2, I.3, I.7 and I.23: the restricted rule retires the shortcuts for
  I.2, I.3 and I.23, and the axiom retirements make I.7's audit circular, while I.13's in I.47
  survives both. Wording only: no field, kind or rule of the schema changes.
  Protected files changed, each named here on a line added relative to origin/main:
  `Certificate/Facts.lean`, `Certificate/FIELDS.md`,
  `scripts/heath.py`, `scripts/safe_push.py`, `scripts/test_safe_push.py`,
  `scripts/requirements-test_safe_push.txt`, `review/SCHEMA.md`,
  `scripts/negative_tests.py`, `tests/test_negative_tests.py`,
  `tests/test_certificate.py`, `tests/fixtures/CertificateCN4.lean`,
  `.github/workflows/ci.yml`.
  The later content branch must supply the marker interface and pin I.4's and I.8's
  `common_notions` in `tests/certificate_expectations.json` when its proofs land.

  The security review's fix round closes the inherited module boundary gap. Listing
  `env.header.moduleNames` by root in the environment loaded by Facts.lean gives
  `Init`, `Lean`, `Std` and `Elements`. The walks may stop at modules under Lean's three
  module roots that the running toolchain supplies, as the next fix round below
  verifies. They walk local declarations in
  `Elements` and the emitter itself, and refuse any reached declaration from another
  imported module, naming both declaration and module before writing any certificate.
  All five walks apply this check before their stopping rules, including the vocabulary
  walk. The module is read from the environment, not inferred from the declaration's
  namespace.

  The regression compiles `Staging.Hidden` separately from its temporary `Elements`
  entry module. Its helpers supply `Coincidence.step`, Common Notion 1 and the existing
  `Tacit.add_comm` axiom, with another case naming the helper only in the entry's type.
  The axiom case also covers an entry that already uses the same axiom directly, which
  the old axiom comparison could not distinguish. Reached helpers fail with the module
  diagnostic; unused imported helpers remain allowed. The old emitter accepts the
  hidden step, notion and type-only cases, and gives only the axiom mismatch for the
  helper supplying an otherwise absent axiom. These regressions require the new
  diagnostic and no certificate output.

  The constructor-counting plant now saves the source bytes before entering `try`,
  mutates inside it and restores those bytes in `finally`. Its restoration regression
  covers interruption during the check, interruption during mutation and a partial
  write error; the mutation cases also preserve CRLF bytes exactly. The other plants
  retain their target checks: the compiled assumption plant is an `Elements` module,
  and the `Staging`, `Audit` and model command plants are checked by the source scan.
  Protected files changed in this fix round: `Certificate/Facts.lean`,
  `Certificate/FIELDS.md`, `tests/test_certificate.py`, `scripts/negative_tests.py`
  and `tests/test_negative_tests.py`. No foundation or expected value changes.

  A further review round found that a module's root is not evidence of its origin: a
  separately compiled `Lean.Hidden`, found first on the search path, could supply a
  helper using Common Notion 1 that every walk stopped at, silently omitting the
  notion. Facts.lean now lists, once per run, the imported modules under `Init`, `Std`
  and `Lean` whose `.olean`, as `findOLean` finds it for the import, lies in the library
  directory of the running `lean` (`getLibDir`), both paths resolved; `isLocal`, the
  boundary every walk shares, lets only those end a walk and refuses any other module
  with the module diagnostic. The regression gives its temporary package a `Lean` root
  whose entries link to the toolchain's own files beside a compiled `Lean.Hidden`. A
  reached `Lean.Hidden.notion` fails, naming declaration and module, with no
  `facts.json`; a reached `Lean.Position` of the toolchain's `Lean.Data.Position`, found
  through those links, still ends the walk, and the existing cases pass unchanged.
  `scripts/test_safe_push.py`'s model of `jobs.check` also records `working-directory`
  at the workflow's and the check job's run defaults and on each required step, and
  rejects any of them, since the recorded command could then run a substitute script;
  mutations at all three scopes are refused, and the `formal-model` job keeps its
  directories. Protected files changed in this round: `Certificate/Facts.lean`,
  `Certificate/FIELDS.md`, `tests/test_certificate.py`, `scripts/test_safe_push.py` and
  `.github/workflows/ci.yml` (the step's name only). No check is weakened, and main's
  facts and pages are unchanged.

  The next review round found that the model still skipped every step without a
  required command, so an earlier step could write a shell startup file defining
  `python3() { return 0; }` and export it through `$GITHUB_ENV` as `BASH_ENV`, leaving
  the certificate command in place but running nothing. The model now reads every step
  of `jobs.check`: each is either a required check or the modeled setup, which is
  `actions/checkout@v5` with no inputs, `actions/setup-python@v5` with only
  `python-version`, and the elan install's exact body; any other step or action is
  refused. Conditions, continuation, shell, working directory and `env` are refused on
  every step, `env` also at the workflow and the check job, and a check-job setting the
  model does not read, such as `container`, is refused. Mutations for the `BASH_ENV`
  step, an unlisted action, a checkout of another ref, `env` at each scope and a
  container are refused, and the actual workflow, whose other jobs keep their `env`, still
  passes. Protected file changed in this round: `scripts/test_safe_push.py`. No check is
  weakened, and main's facts and pages are unchanged.

  A further review found that another checkout before rendering could restore the
  committed `facts.json`, discarding the freshly computed certificate before the
  freshness assertion. `scripts/test_safe_push.py` now requires the setup to form one
  initial prefix: checkout, Python setup, then the elan install, each exactly once in
  that order, before the first check. Mutations insert a checkout before rendering,
  insert Python setup after checks begin, repeat either action, reverse the actions or
  omit setup; each is refused. Protected file changed in this round:
  `scripts/test_safe_push.py`. No check is weakened.

- **The model's shared-module checks land before the restricted rule (brief 0009, #75).**
  The branch `tooling/superposition-model-check` carries the generic checks from
  `lean/superposition-restricted` in `model/Check/Generator.lean`: declarations from exactly
  the four pure superposition modules are shared by identity, with their universe
  arguments preserved. Admission is by declaring module. Before translation, a transitive
  audit reads every declaration in those modules and permits dependencies only on those
  modules and `Init`, with only Lean's three logical axioms and no `sorryAx`. The checks
  land separately from the content they serve, as WORKFLOW requires. The four modules do
  not exist on main yet, so the audit has no roots, no declaration is shared, and all three
  generated files remain byte for byte unchanged. An empty shared-import list adds no
  blank line to the generated laws header.
  `model/Check/RoundTrip.lean` adds cases using Init declarations and isolated lookup
  copies, so the audit is exercised before the calculus arrives: it accepts an Init-only
  closure and refuses a transitive geometric dependency in a type or value, a dependency
  found only in an opaque value or a recursor rule, `sorryAx`, and an unapproved axiom.
  All helpers called by `run_cmd` live in
  `model/Check/Generator.lean`, as the model scan's allowance intends; the guarded cases
  stay in `model/Check/RoundTrip.lean`. `plantPureDependency` takes a definition and a
  dependency, plants it in a copy of the definition's type or value, and audits from that
  definition with an isolated lookup. The content branch can use it on
  `Elements.Superposition.guards`. `checkSharedIdentity` checks the production translation
  plan in both directions, preserving zero, symbolic and compound universe arguments;
  here `Nat.rec` pins the refusal of a constant that is not shared. Parameterised fixtures
  extend `pureModules` with stand-in modules for the same plan construction and purity
  audit, so the real calculus stays shared after it arrives. The import-header fixtures
  use explicit stand-in reached words without constructing a plan. The cases for
  `List.filterMap` and `Model.Kind.rec` exercise successful identity entries before the
  calculus arrives, including two universe arguments and a shared name in the Model namespace.
  Reverse translation exempts
  identity entries from its residual model-name check. Further cases check a non-empty
  shared-import header and module-root collection: a dependency planted in an otherwise
  unused declaration is found without that declaration being supplied as an audit root.
  Both module-root fixtures also extend the production boundary. `comparePlantedWord`
  runs on a matching copy of translated `Elements.Collinear`, with no message, and on a
  copy with two points exchanged, with its exact diagnostic pinned by `#guard_msgs`.
  Production continues to use exactly the four pure modules.
  `checkModelImports`, called from RoundTrip, reads `Model.lean`, every Lean file under
  `Model/`, and each pure module's source if present. Model imports are restricted to Model
  modules, the four pure modules and the external package roots recorded once in
  `modelImportPackages`, from Lean and the pinned Mathlib dependency configurations in
  `model/lake-manifest.json`. Other roots, including `Check`, `Staging`, `Audit`,
  `Certificate` and unknown names, are refused. Pure files admit only the four pure
  modules and `Init`. Every import name must first have canonical path components, as
  specified in the fifth-round correction below. Auditing these local sources bounds their
  closure under the configured package roots and unmodified external dependencies and
  toolchain, without search-path or symlink substitution. External sources and file
  provenance are not audited here. Lake 4.35 defaults
  the Model library to root `Model` and glob `Glob.one Model`, building `Model.lean` and
  following its imports. Auditing that root outside `Model/` and the whole directory
  covers its local sources, including unimported ones. Lean's header parser handles legacy
  headers without `module`, comments, blank lines, `module` and import modifiers, and
  stops at the first body command. Malformed headers are refused.
  `checkModelImportsWith` makes the decision from a list of files and imports; planted
  headers exercise the same parser and decision. They accept permitted imports and
  refuse plain and public geometric imports, a module below an approved module, and
  Mathlib in a pure file, as well as `Check.Original` in a legacy `Model.lean` header,
  `Staging`, `Audit`, `Certificate` and an unknown root. The real tree is checked too.
  **The protected path `model/lakefile.toml` changes** to register all files the import
  audit reads as text inputs in the Check library's `needs`: `Model.lean` and the `.lean`
  files under `Model/` and `../Elements/Foundations/`. The plane-proof input also selects
  only `.lean` files. An experiment with a missing `input_dir` fails with "no such file or
  directory", so the existing foundations parent is registered instead of its absent
  `Superposition/` child; it selects other foundation
  Lean files as well as the four pure sources. Reading Lake 4.35's installed
  `Lake/Config/InputFileConfig.lean`, `Lake/Load/Toml.lean`,
  `Lake/Build/Common.lean` and `Lake/Build/Trace.lean` confirms that `filter` is supported,
  `inputDir` filters and sorts before collecting file traces, and `BuildTrace.mix`
  combines hashes without hashing their path captions. The filter
  `filter = { extension = ["lean"] }` makes a `.txt` to `.lean` rename add a hashed input,
  including when it introduces the first pure source. A selected file's addition or
  removal changes the hashed list. A rename within that list can still replay a result
  if its ordered contents stay the same; filenames are not themselves hashed. Text hashes
  normalise line endings, and timestamp-only changes can also replay results. Other
  changes to selected contents rebuild the checks. CI's fresh build runs every check,
  including the whole import audit, regardless of these local cache traces. This
  strengthens the check without changing its expectations or the generated files. The
  protected build-file change needs the security review required by WORKFLOW before landing.
  RoundTrip also tests `modelDir` with relative and absolute filenames.
  The path fix in `model/Check/Generator.lean` replaces the early `return` with `pure`,
  so resolving a relative filename continues to its parent directories and the package
  check. `model/README.md` explains the boundary and the regressions. The complete change
  is `model/Check/Generator.lean`, `model/Check/RoundTrip.lean`, `model/README.md`,
  `model/lakefile.toml` and `docs/briefs/0002-decisions.md`; `model/lakefile.toml` is the
  only protected path among them under `PROTECTED` or `PROTECTED_JUDGED` in
  `scripts/safe_push.py`.

- **Fourth-round rename experiments for `model/lakefile.toml`.** Run on `68e4ea30` with
  the fourth-round working changes, on 20 October 2026. From `model/`, with
  `export PATH=$HOME/.elan/bin:$PATH` before each Lake invocation, the unmodified baseline's
  `lake build` passed (2625 jobs). A file `Model/Unused.txt` containing
  `import Check.Original` followed by a newline was added, and `lake build` passed.
  After `mv Model/Unused.txt Model/Unused.lean`, with identical bytes, `lake build`
  incorrectly passed from cache. Removing the fixture and rebuilding restored a passing
  tree before editing the inputs.
  With the extension filters in place, the same build, rename and build sequence rebuilt
  `Check.RoundTrip` and exited 1 with:
  ```text
  error: Check/RoundTrip.lean:239:0: model/Model/Unused.lean: Model imports `Check.Original`, outside the approved import roots
  ```
  The second case created `../Elements/Foundations/Superposition/Syntax.txt`, containing
  `import Elements.Foundations.Words` followed by a newline. `lake build` passed;
  `mv ../Elements/Foundations/Superposition/Syntax.txt ../Elements/Foundations/Superposition/Syntax.lean`
  preserved its bytes, and the next `lake build` exited 1, rebuilding `Check.RoundTrip`:
  ```text
  error: Check/RoundTrip.lean:239:0: Elements/Foundations/Superposition/Syntax.lean: pure module imports `Elements.Foundations.Words`, outside the four pure modules and `Init`
  ```
  `Check.Generated` also refused the newly present, unimported foundation module in that
  case. Each fixture was removed afterwards, the newly created `Superposition/` directory
  was removed, and `lake build` passed again (2625 jobs). No generated source was written.

- **Fifth-round module-name correction for brief 0009, #75.** The import audit previously
  accepted `Model.«..».Check.Original`; an absolute-path component under `Init` could also
  label the geometric words as Lean's own. `isCanonicalModuleName` now requires non-empty
  string components, with no slash, backslash, NUL or colon, neither `.` nor `..`, and no
  trailing dot or space. Anonymous names and numeric components are refused. The import audit
  applies this predicate before root permissions; core, shared and project membership,
  foundation collection and shared headers use it too. A non-canonical sharing boundary
  is an error. Harmless escaped names such as `areas-p5` remain accepted.
  Reading the installed Lean 4.35 `Lean/Util/Path.lean` and `Init/System/FilePath.lean`
  confirms that `modToFilePath` joins each component with `FilePath.join`: `..` permits
  traversal and an absolute component discards the preceding path. Windows drive prefixes,
  streams and trailing-dot or trailing-space aliases are refused on every platform.
  `Lean/Compiler/ModPkgExt.lean` exposes an imported module's optional package identifier
  through `Environment.getModulePackageByIdx?`. Inspection found no identifier on any of
  the installed toolchain's 653 `Init` modules, and `some "stoicheia"` on the geometric
  words. `isLeanCore` now requires a canonical `Init` name and an absent package identifier,
  refusing every named package. `Lean/Environment.lean` retains no resolved file path; its
  importer can use either `findOLean` or explicit import artefacts, so looking up a name
  again would not authenticate the already loaded file. An unlabelled replacement remains
  outside what these checks distinguish. The build assumptions above still apply.
  Planted headers reproduce both escapes, and planted declaring-module lookups for
  `Elements.Point` and `Elements.Collinear` exercise the core and sharing decisions without
  installing a new module. These cases failed before the canonical guard was added.
  A matrix exercises the predicate, header parser and import decisions, including Windows
  spellings, empty components, NUL and invalid numeric names; positive cases keep harmless
  escaped identifiers and canonical modules admitted. Further core cases refuse named
  packages even with canonical names, and accept actual Init declarations. All run before
  the calculus arrives.
  This round changes only `model/Check/Generator.lean`, `model/Check/RoundTrip.lean`,
  `model/README.md` and this decisions file. The three generated sources stay unchanged.

- **Sixth-round source spelling and compiled imports for brief 0009, #75.** At
  `356b62ab`, the source audit selected only an exactly lower-case `.lean` extension.
  On this case-insensitive filesystem, Lake built `Model/Uppercase.LEAN` when asked for
  `Model.Uppercase`, and the source audit passed it. The requested fixture, containing
  `import Check.Original`, did not make the whole baseline build pass: Lean refused its
  non-`module` header when `Model.lean` imported it. Both observations matter.
  `model/Check/Generator.lean` now validates directory listings before selecting sources:
  every extension equal to `lean` ignoring case must be exactly `lean`, and distinct paths
  equal after lowercasing are refused, including directory components. It checks the
  actual Model root filename and the listings under Model and the existing foundations
  parent. A case variant of a pure module's prescribed path is also refused on its own,
  so selecting by listing cannot lose the old audit's case-insensitive path lookup.
  `model/Check/RoundTrip.lean` supplies planted listings as data, exercising
  upper-case and mixed-case extensions and collisions on any filesystem. The extension
  and collision cases failed before the new decision was implemented.

  The same generator now traverses the compiled import graph from `Model`, using
  `findOLean` and `readModuleData` from the installed Lean 4.35 toolchain. Its
  `Lean/Environment.lean` shows that `mkModuleData` copies the whole import header into
  the first `.olean` part, including non-public imports. Every name is checked before
  lookup, against the canonical-name predicate and the source audit's Model whitelist.
  A visited set handles repeated imports and cycles; refusals give the import path.
  The source audit's complete Model list must appear in the closure. Model's default
  root and glob build only `Model` and its imports, so an unimported source is refused;
  new globs would require new graph roots and a revised coverage check. Source headers
  are still audited, including files nothing imports and the four pure sources.
  Planted closure data refuses `Check.Original`, `Elements.Foundations.Words`, where
  `Elements.Point` is declared, a non-canonical name, and an uncovered source module.
  This checks the graph of compiled imports. It does not authenticate files on the search
  path, establish correspondence with sources, or recover earlier import artefacts.

  **The protected path `model/lakefile.toml` changes in this round.** Check keeps its
  existing restriction against importing Mathlib. Instead its `needs` includes
  `Model:leanArts`, building the whole Model library before any Check module runs, also
  for a direct Check-module build. The graph reader imports no declarations and runs no
  module initialisers. Both source-directory filters now enumerate all sixteen ASCII
  case variants of `lean`; adding a `.LEAN` source invalidates the checks. The existing
  limits of content-only traces still apply to renames within the selected set.
  With the fixture unimported, `lake build` now fails with:
  ```text
  model/Model/Uppercase.LEAN: non-canonical source extension (expected `.lean`)
  ```
  With its import added to `Model.lean`, Lake instead reports `build cycle detected`
  through Model, Check's new build prerequisite and `Check.Original`. Both temporary
  source changes were removed. `model/Model.lean` is byte for byte unchanged.

  The real compiled graph reaches `Lake.Util.Version`, through `Mathlib.Init`,
  `ImportGraph.Tools` and `ImportGraph.Util.Modules`. `Lake` ships with Lean's toolchain,
  like `Init`, `Std` and `Lean`, so the captain added it to the permitted roots of the
  import checks this branch introduces; no existing check is loosened, and `isLeanCore`,
  which decides what is trusted as Lean's own in translation, still admits only `Init`.
  `model/README.md` documents the graph check, build ordering and provenance limits.
  The files changed are `model/Check/Generator.lean`, `model/Check/RoundTrip.lean`,
  `model/README.md`, `model/lakefile.toml` and `docs/briefs/0002-decisions.md`.
  `model/lakefile.toml` is the only protected path changed in this model-check round and
  still needs the independent security review before landing. All three generated sources remain
  byte for byte unchanged. No proposition review record is made stale.
  On `356b62ab` with these uncommitted changes, `python3 scripts/check_fidelity.py`,
  `python3 -I tests/model/run.py --fast`, `python3 -I tests/test_negative_tests.py` (eight
  tests), and the generated-file `git diff --exit-code` pass. With `Lake` permitted,
  `cd model && lake build` passes (2625 jobs).
  The optional style check initially found eight unknown Audit names with stale build
  artefacts; `lake build Audit` passed (139 jobs), then `python3 scripts/check_style.py`
  passed. Every Lake invocation exported the elan path first. No full repository CI or
  independent security review was run, and no commit, push or GitHub action was made.

- **Seventh-round verification of the model import boundary (brief 0009, #75).** The
  supplied worktree was clean at `8e7d22f1`, with the previous model-check changes and
  the certificate-tooling branch already committed. The captain's permission for `Lake`
  was already recorded in `modelImportPackages`, the single list used by the new source
  and compiled-import checks. `Lake` is shipped with Lean, alongside `Init`, `Std` and
  `Lean`; its admission here does not loosen an existing check. No further root is added.
  `isLeanCore` still requires a canonical `Init` name and no package identifier, and the
  shared-definition boundary remains exactly the four pure modules.

  `model/Check/Generator.lean` clarifies that distinction and extends the core-decision
  regression to `Std`, `Lean` and `Lake.Util.Version`. `model/Check/RoundTrip.lean` now
  explicitly accepts `Lake.Util.Version` in Model source headers and compiled closures,
  and pins its refusal in a pure source. The existing planted closures still refuse
  `Check.Original`, `Elements.Foundations.Words` and `Model.«..».Check.Original` with
  their exact diagnostics. The real compiled closure and source-module coverage pass.
  Reading the compiled graph finds 4,224 Model-closure modules, all within the approved
  roots. A separate temporary graph probe finds 2,416 modules in Check's closure, with
  roots `Check`, `Elements`, `Init`, `Lean`, `Model` and `Std`: no Mathlib, dependency
  package, Model root or Euclidean proof module enters Check through the prerequisite.

  **The protected path `model/lakefile.toml` changes again**, to explain that
  `Model:leanArts` is a build prerequisite and adds no Lean import. The normal build has
  no cycle because Model imports no Check module. `model/README.md` records the same
  boundary, the regressions and the distinction between the two fixture refusals.
  On this case-insensitive filesystem, `Model/Uppercase.LEAN` containing exactly
  `import Check.Original` and a newline, unimported, makes `cd model && lake build`
  exit 1 with:
  ```text
  model/Model/Uppercase.LEAN: non-canonical source extension (expected `.lean`)
  ```
  Adding `public import Model.Uppercase` to `Model.lean` makes the same command exit 1
  with Lake's refusal, before either audit runs:
  ```text
  error: build cycle detected:
    model/+Model.Uppercase:leanArts
    [anonymous]/Model:leanArts
    model/Check:extraDep
    model/+Check.Original:presetup
    model/+Check.Original:leanArts
    model/+Check.Original:exportInfo
    model/+Model.Uppercase:importInfo
    model/+Model.Uppercase:presetup
    model/Model:leanArts
    model/Model:default
    model/+Model.Uppercase:leanArts
  ```
  The fixture was removed and `model/Model.lean` restored byte for byte. Lake had produced
  no `Uppercase.*` build outputs; the cleanup checked that none remained. The restored
  `cd model && lake build` passes (2625 jobs). No generated source was written.

  The complete protected-file list for the branch against origin/main now includes the
  merged certificate tooling. Each full path is named here on an added line:
  `.github/workflows/ci.yml`, `Certificate/FIELDS.md`, `Certificate/Facts.lean`,
  `model/lakefile.toml`, `review/SCHEMA.md`, `scripts/heath.py`,
  `scripts/negative_tests.py`, `scripts/safe_push.py`, `scripts/test_safe_push.py`,
  `tests/fixtures/CertificateCN4.lean`, `tests/test_certificate.py`,
  `tests/test_negative_tests.py`.
  Only `model/Check/Generator.lean`, `model/Check/RoundTrip.lean`, `model/README.md`,
  `model/lakefile.toml` and `docs/briefs/0002-decisions.md` change in this round.
  No proposition, foundation, lock, expected value or review record changes.

  Validation on `8e7d22f1` plus this round's uncommitted changes: `cd model && lake build`
  passes (2625 jobs), as does the direct `cd model && lake build Check.RoundTrip`
  (2610 jobs). `python3 scripts/check_fidelity.py`, `python3 -I tests/model/run.py --fast`,
  `python3 -I tests/test_negative_tests.py` (ten tests), `python3 scripts/check_style.py`
  and `git diff --check` pass. The generated-file command
  `git diff --exit-code -- model/Model/Laws.lean model/Check/Laws.lean model/Model/Assembly.lean`
  passes; comparison with saved bytes and HEAD confirms all three are unchanged.
  A local check of the protected-path definitions confirms all twelve changed protected
  files appear on added decisions lines. Every Lean and Lake invocation exported
  `PATH=$HOME/.elan/bin:$PATH` first. No full repository CI, independent kernel replay
  or independent security review was run. The changes remain uncommitted; no push or
  GitHub action was taken. Security review before landing remains open.

- **Eighth-round Unicode source aliases for brief 0009, #75.** At `2a481ee5`, ASCII
  lowercasing did not identify `ſyntax.lean` as an alias of `Syntax.lean`. The listing
  check accepted the former, and exact selection from the listing omitted it from the
  stricter pure-source import audit. A canonical path on this machine opens that alias.
  `model/Check/Generator.lean` now probes each of the four pure modules by its canonical
  source path, independently of the directory listing, and audits the file that path opens.
  The separate listing check permits only ASCII letters, digits, `_`, `-` and `.` in
  each component, with empty, `.` and `..` components refused. It checks directory entries
  and non-source filenames too, before ASCII case comparisons. The existing exact `.lean`
  extension, case-collision and prescribed pure-path checks remain. Model sources are read
  from the validated ASCII listing, with the root required as `model/Model.lean`.
  The import decision validates supplied source paths before deciding whether the pure or
  Model import boundary applies, so an alias cannot receive the Model permissions.

  `model/Check/RoundTrip.lean` adds listings and headers supplied as data. They refuse
  the long-s aliases of a pure source and a Model source, a Kelvin-sign alias, and other
  non-ASCII names. A directory component and a non-source filename are checked as well;
  canonical ASCII paths, including all four pure sources, pass. These cases need no pure
  source files or folding filesystem. With the old generator, the ten refusal cases failed
  because no diagnostic was emitted; with the correction, `lake build Check.RoundTrip`
  passes (2610 jobs). `model/README.md` explains the canonical probes, ASCII filenames
  and the regression evidence. Lake's inputs are unchanged: the existing extension filters
  already include these `.lean` aliases. Non-source entries are checked when the audit
  runs, but changing those entries alone need not invalidate a cached check; the existing
  content-only trace limits on renames also remain.

  Real experiments on this machine created
  `Elements/Foundations/Superposition/ſyntax.lean` containing exactly
  `import Lake.Util.Version` and a newline, then separately
  `model/Model/ſcratch.lean` containing exactly `import Check.Original` and a newline.
  Reading the canonical paths `Elements/Foundations/Superposition/Syntax.lean` and
  `model/Model/Scratch.lean` returned those bytes. Each `cd model && lake build` exited 1,
  with the respective source-audit diagnostic:
  ```text
  Elements/Foundations/Superposition/ſyntax.lean: non-canonical source path (expected ASCII letters, digits, `_`, `-`, `.` in each component)
  model/Model/ſcratch.lean: non-canonical source path (expected ASCII letters, digits, `_`, `-`, `.` in each component)
  ```
  Both temporary files and the newly created `Superposition/` source directory were removed.
  The restored `cd model && lake build` passes (2625 jobs). On `2a481ee5` plus this
  round's uncommitted code, `python3 scripts/check_fidelity.py`,
  `python3 -I tests/model/run.py --fast` and `python3 -I tests/test_negative_tests.py`
  (ten tests) pass. The three generated sources, `model/Model/Laws.lean`,
  `model/Check/Laws.lean` and `model/Model/Assembly.lean`, match both HEAD and origin/main
  byte for byte. Every Lean and Lake invocation exported `PATH=$HOME/.elan/bin:$PATH` first.

  This round changes only `model/Check/Generator.lean`, `model/Check/RoundTrip.lean`,
  `model/README.md` and `docs/briefs/0002-decisions.md`. No proposition statement, Heath
  comment, foundation, lock, expected value or review record changes; no record is made
  stale. The complete protected-file list for the branch against origin/main, including
  the earlier certificate tooling, is named again by whole path on added lines:
  `.github/workflows/ci.yml`, `Certificate/FIELDS.md`, `Certificate/Facts.lean`,
  `model/lakefile.toml`, `review/SCHEMA.md`, `scripts/heath.py`,
  `scripts/negative_tests.py`, `scripts/safe_push.py`, `scripts/test_safe_push.py`,
  `tests/fixtures/CertificateCN4.lean`, `tests/test_certificate.py`,
  `tests/test_negative_tests.py`.
  The changes remain uncommitted. No push or GitHub action was taken. Full repository CI,
  independent kernel replay and independent security review were not run in this round;
  security review before landing remains open.

- **The owner approves the restricted superposition replacement.** The owner's exact
  approval is: "replace the superposition rule as ship S built it, with brief 0009 questions 2, 4 and 5 as prototyped, the model's import of the four pure modules, the page claim 'a restricted inference in System E's style', tooling PR first. Lands after /no-mistakes and an independent Codex read of the model lane."

  [Brief 0009](0009-superposition.md) and the code agree on those answers. Question 2
  accepts the five-part restriction: parts 1, 2, 3 and 5 are theorems; part 4 is a reading
  of `Rule.infer`, with the limited theorem `Metric.holds_const`. Question 4 permits a
  proved law whose statement asserts no existence inside the placement, even when its
  proof uses constructions; I.8 therefore cites I.7 on its hypothetical corner.
  Question 5 keeps the side AC as a straight line through D and C′. The approved model
  imports are exactly the four pure modules `Elements.Foundations.Superposition.Syntax`,
  `Elements.Foundations.Superposition.Semantics`, `Elements.Foundations.Superposition.Soundness`
  and `Elements.Foundations.Superposition.Restriction`; the approved page claim is
  "a restricted inference in System E's style". Neither equivalence with System E's
  two printed rules nor whole-theory non-derivability is claimed.

  The approval covers restating `Tacit.superposition`, the pure calculus and its use in
  I.4 and I.8, the corresponding update of `Certificate/axioms.lock`, and the model's
  translation and proof. The tooling pull requests must land first. Landing the
  replacement also requires /no-mistakes and an independent Codex read of the model lane.
  The read at `cdcf3b9e`
  found no weakening and one older relative-path defect in `model/Check/Generator.lean`;
  the read at `0085b443` found that an escaped module name passed the Model import audit.
  Both are fixed on `tooling/superposition-model-check`. That evidence is tied to the
  revisions read; the revision that lands still needs its own read and validation.

  Common Notion 4 is marked at its actual steps by the pure proposition
  `Elements.Superposition.Coincidence`, with its sole constructor
  `Elements.Superposition.Coincidence.step`. The three congruence constructors of
  `Derives` take the marker as their first explicit argument. Renaming passes the
  received marker along and soundness binds it; neither creates one. I.4 and I.8 supply
  it at their congruence steps. The tooling certificate counts this constructor instead
  of the congruence constructors, so merely reaching `Derives.map` no longer reports
  C.N. 4. This adds no axiom and changes no derivable conclusion, proposition statement,
  Heath line or route. Integration with `tooling/superposition-certificate` regenerates
  `Certificate/axioms.lock`, both model hashes, the model outputs, certificate and pages.
  The 87 axiom statements stay unchanged; the vocabulary grows from 206 to 208, adding
  `Superposition.Coincidence` and `Superposition.Coincidence.step` and changing only
  `Superposition.Derives.len_congr`, `Superposition.Derives.angle_congr` and
  `Superposition.Derives.area_congr` to take the marker. `Derives` still has seventeen
  constructors. The certificate has 122 entries: 99 propositions, 3 porisms and 20
  companions. Of these, 116 reach the calculus and its marker; none reaches the calculus
  without taking or inheriting a congruence step, so all Common Notion lists stay
  unchanged. I.4 has C.N. 4 and C.N. 5; I.8 has C.N. 1, C.N. 3, C.N. 4 and C.N. 5.
  `tests/certificate_expectations.json` keeps all 24 existing expectations and adds
  I.8's inclusion of C.N. 4 beside I.4's existing expectation. The fixture tests cover
  derivations that reach transformers without a step. I.4's and I.8's review records
  were read again by an independent reader after the marker change and stamped at
  `0085b443`.

  Once the two tooling branches have landed, the protected files this branch changes are
  `Audit.lean`, `Audit/Overlaps.lean`, `Audit/Superposition.lean`, `Audit/screen.py`,
  `Certificate/axioms.lock`, `model/Model/Audit.lean`, `model/lakefile.toml`,
  `model/lock.sha256`, `tests/certificate_expectations.json`, `tests/model/MODEL.md`,
  `tests/model/hyperbolic.py`, `tests/model/laws.toml`, `tests/model/lock.sha256` and
  `tests/model/search.py`. `Certificate/Facts.lean`, `scripts/heath.py` and the example in
  `review/SCHEMA.md` now arrive with `tooling/superposition-certificate`, which lands
  first, so this branch changes no check input other than values pinned to it and the
  superposition law's code in the two numerical harnesses. The content change in `Audit/screen.py` unfolds
  `primitives`, the edition's interpretation of the restricted calculus, without
  changing its coverage check or returning placement witnesses. No check, expected
  value, lock or schema is weakened; the check changes land in tooling first.

  Integration with the model tooling moves the import-boundary check out of
  `model/Model/Audit.lean`: `Check.Generator.checkModelImports`, called from
  `model/Check/RoundTrip.lean`, checks every Model source and the four pure modules on
  each build. The unknown-`Elements.Point` sentinel and every axiom pin remain in
  `model/Model/Audit.lean`. The real-calculus regressions use the tooling's generator
  helpers, retaining every case and expected rejection; `model/lakefile.toml` keeps
  all tooling inputs and `needs` unchanged and describes the boundary now in use.
  The two identity fixtures for `List.filterMap` and `Model.Kind.rec` add their stand-in
  module to the production boundary, since the laws now reach the real calculus.
  Their success expectations and the production boundary itself are unchanged.

- **Finishing the prototyped answers to brief 0009's questions 2, 4 and 5 is tracked in
  [#150](https://github.com/jackChallis/stoicheia/issues/150).** The owner approved those
  answers "as prototyped" (the entry above) and, as #150 records, said: "prototyped work
  needs to be finalized - that opens an issue". #150 carries the label `blocks-release`, so
  no release is made until it closes. The replacement lands on the prototyped answers. Until
  #150 finishes them, part 4 of the restriction is an inspection of `Rule.infer` as locked
  in `Certificate/axioms.lock`, not a theorem; `Cited.drawsNothing` is a classification set
  by hand, whose meaning is judged by eye from the audit's pinned axiom closures; and the cost of the kept side is
  checked by reading the model's proof. Non-derivability stays unclaimed. The landing order
  with the retirement waves (#119) is the first wave, `lean/retire-axioms`, then the
  replacement, then the second wave, `lean/retire-axioms-2`, whose landing carries the
  review of `drawsNothing` and of the audit pins. [Brief 0009](0009-superposition.md)
  records this in its round 4. The docstrings that cite question 4 in
  `Elements/Foundations/Superposition/Syntax.lean` and
  `Elements/Foundations/Superposition/Restriction.lean`, and the comment beside I.8's route
  note in `review/I/08.toml`, now say "as prototyped" and cite #150; these are comments
  only, and change no statement, declaration, stamp or check. The 19 October superposition
  entry is restored verbatim from `bccc3f52`, as #150 requires. The approval and the
  correction to Common Notion 4 counting belong to the 20 October entry above; they do
  not revise that earlier record of preparation.

- **The model-check branch's reviews closed, and Model/Audit.lean's heading corrected.**
  Six independent Codex code and security reviews of `tooling/superposition-model-check`
  ended with both verdicts passing at `bc4e6574`; the round entries above that say a
  security review is still open record their own rounds, and this entry closes them. A
  /no-mistakes round then corrected the wording of the protected `model/Model/Audit.lean`,
  a comment and a heading only: the library's geometric vocabulary is not imported, and
  the import checks permit only the four pure superposition modules. No guard, pin or
  declaration of that file changes. The other files the branch changes on its own are
  `model/Check/Generator.lean`, `model/Check/RoundTrip.lean`, `model/README.md` and the
  protected `model/lakefile.toml`, named above.

- **Unfinished work may land with its issue, and holds the release until it is finished.**
  The owner set the rule: "I don't mind incomplete work, prototypes, whatever so long as
  those are flagged issues and releases are held up until those are finalized."
  Each prototype, provisional answer, restricted or partial scope awaiting a proof,
  deferred page, test not yet in CI, or thing a disclosure calls "to come" has an open
  issue labelled `blocks-release`, named in the pull request's new "Unfinished work"
  section, whose Required box confirms that every piece is listed; a pull request with
  none says "None". The merge gates require that section once the template in force has
  it, read each named issue from GitHub, and refuse another repository's reference, a
  pull request number, a closed or unlabelled issue, a list item with no issue, or a read
  that cannot be trusted. A pull request labelled `release` is refused while any issue
  or pull request labelled `blocks-release` is open; ordinary pull requests make no
  read of that list.
  Three rounds of independent review found ways for a renderer to show what a parser of
  the section did not read, so the section is read as raw text: the one line
  `## Unfinished work`, which GitHub must show as a heading, no other line whose letters
  begin "unfinished work", and, apart
  from the template's own comment, plain ASCII with no markup, "None" or a list naming each
  issue as `#N` (WORKFLOW, section 10, step 4). Malformed pull request labels refuse;
  label comparisons ignore case; each named issue is bound to this repository by its
  canonical address, so a rename is allowed and a transfer is not; the merge gate and
  the pre-flight's CI watcher leave out a `release-gate` run left from an earlier
  `release` label on an ordinary pull request. The gate checks what the section says;
  it cannot know what was left out of it, so a "None" that should have named an issue
  remains for the reviews to find.
  The merge command never writes the pull request body. If the pre-flight summary or
  another part safe_push owns is stale, it refuses before writing; the coordinator runs
  the pre-flight to refresh those parts, then starts a fresh merge attempt. Thus a
  concurrent edit to "Unfinished work" cannot be overwritten by the merge that checked
  the earlier text.
  `scripts/check_release_gate.py` makes the same release check, with an offline JSON
  mode for its tests, and the separate `release-gate` CI job shows the hold on a release
  pull request. That job is skipped on ordinary pull requests and runs main's copy of
  the script, though GitHub reads the workflow file itself from the pull request; the
  merge gate reads the issues again and is the authority, and the owner runs the script
  once more just before a tag.
  Both readers follow every page and fail closed on unreadable data. The offline tests
  in `tests/test_release_gate.py` run in CI's `check` job and safe_push's check sequence,
  immediately after `tests/test_check_style.py`, with no Lean or network; the full
  `scripts/test_safe_push.py` harness tests the merges and refusals locally through its gh
  stand-in; its source clone copies Git's objects without hard links, so a sandbox that
  may read the repository can run it. No planted fault
  is added to `negative_tests.py`: these gates judge pull request text and issue state,
  which the offline fixtures and gh stand-in supply, rather than a break in the
  edition's files. WORKFLOW's step 9 also gains a sentence the release needs beside the
  hold: the release pull request moves the `acceptance` job's `ACCEPTANCE_GATE` from
  `ratchet` to `full`, as that job's entry above says. The protected files changed are:
  `.github/pull_request_template.md`,
  `.github/workflows/ci.yml`,
  `.github/workflows/release-gate.yml`,
  `scripts/safe_push.py`,
  `scripts/check_release_gate.py`,
  `scripts/test_safe_push.py`,
  `tests/test_release_gate.py`.
  [WORKFLOW](../WORKFLOW.md), sections 8 and 10, records the checks and the release
  hold. `git safe-push --label release` creates the `release` label, with its
  description, the first time it is given; the consolidation release (#38) lands through
  a pull request carrying it. Tags and releases stay manual, by the owner.
- **The joins by Postulate 1 stay wherever Euclid writes them (part of
  [#32](https://github.com/jackChallis/stoicheia/issues/32)).** Train Tw2 first removed the
  joins by Postulate 1 from I.5, I.11, I.16, I.20 and I.26, since the later steps of those
  proofs do not use the segment the join names. The coordinator ruled that a join stays
  wherever a sentence of Euclid's stands over it, and goes only where none does: he writes
  "let ... be joined" over each of these steps (`heath/I/05.md`, line 16; `heath/I/11.md`,
  line 16; `heath/I/16.md`, line 12; `heath/I/20.md`, line 18; `heath/I/26.md`, lines 12
  and 54). So all five joins stay, the five Lean files are as they were, and the records of
  I.5 and I.11 now declare their joins as passages carried from the text. This is not a
  dummy citation in the sense of [FORMALIZATION](../FORMALIZATION.md), section 5: the step
  is Euclid's own, written where he writes it. A later sweep for unused steps keeps a join
  that a sentence of Euclid's stands over, on this ground.

- **The checks read a tree without the files a commit adds to them (#178).** The
  pre-flight's pass with origin/main's checks (`scripts/safe_push.py`, steps 3 and 4)
  takes the files a commit adds under the check inputs out of the work tree, while Git's
  index still lists them. `scripts/negative_tests.py`, which runs in that pass in step 4,
  copied every tracked path for its count plants, so on such a commit it stopped with
  `FileNotFoundError` in `tests/test_generated_counts.py`, which uses the same copy,
  before any count plant ran; the count plants, run alone, stopped the same way. A
  tracked Markdown file taken out stopped the freshness plant's list of generated outputs
  too, and the merge-marker copy passed such files over without a word.
  `check_fidelity.py` and `render.py` read every tracked Markdown file for count markers
  (`generated_counts.updates`), and both run in that pass in step 3 and again in step 4,
  so a Markdown file the commit adds there, as `tests/notes.md`, failed both in that pass
  with `No such file or directory`. A failure in that pass is only a note, but
  `keep_apart` counts it, so a content pull request with a new test beside it was refused
  as a check changed together with what it checks: the second item of #178.

  One rule, `generated_counts.absent_tracked`, now holds wherever these checks list
  tracked files: a tracked file absent from the work tree under the check inputs is named
  on stdout as a note, and the check goes on with what is present; one absent anywhere
  else, where the pre-flight takes nothing out, is a failure that names it.
  `generated_counts.updates`, which `check_fidelity.py` and `render.py` share, follows
  it, and so do the negative suite's two copies and its list of generated outputs; no
  plant is skipped. A file is absent only when `lstat` raises `FileNotFoundError`. Any
  other error, such as a permission error in a directory of mode 000, is raised to the
  caller and fails the check: `generated_counts.updates` reports it as its one error
  (before the rule, reading the file failed with the same error), and the negative suite
  stops on it. `Path.exists()` would not do: on Python 3.14 it returns False for such an
  error. Each name in a note or a failure is printed as `repr` writes it, so a control
  character in a name cannot forge a line of the terminal. A path that is or passes
  through a symlink is not absent, and each reader treats it as before:
  `generated_counts.updates` refuses it by name; the negative suite's marker copy skips a
  symlink and follows a symlinked directory; and its source copy (`shutil.copy2`)
  follows both, copying the target, and stops with `FileNotFoundError` on a dangling
  one. The check inputs stay listed once, as `scripts/safe_push.py`'s `CHECK_INPUTS`,
  which `generated_counts.py` imports only when a tracked file is absent, so an ordinary
  run of a check never loads the harness.

  `tests/test_negative_tests.py` builds the case in a temporary repository: a commit
  adding a check, its test and a Markdown note, each then unlinked as the pre-flight
  unlinks it. It checks both copies, the list of generated outputs, a tracked file
  absent outside the check inputs, and a directory of mode 000, whose permission error
  both copies raise with nothing noted; against origin/main's `negative_tests.py`, four
  of its five tests stop with that error and the fifth finds no file named.
  `tests/test_generated_counts.py` does the same for the counts, in a temporary
  repository: a Markdown file absent under the check inputs is noted while a stale count
  beside it is still refused, one absent elsewhere is refused by name, a name with
  control characters is printed escaped, a directory of mode 000 fails the run with its
  permission error and is not noted, and a symlink in place of one is still refused as
  a symlink. In the negative suite's source copy, `check_fidelity.py` and `render.py`
  pass with the first tracked Markdown file under `tests/` taken out, noting it, and fail
  naming the first one outside the check inputs taken out; both are chosen at run time
  from Git's list, among the files present. Against origin/main's `generated_counts.py`
  every one of these fails but the symlink case.

  No other reader of Git's tracked files in that pass crashes or fails on such a file:
  `check_style.py`'s S23 passes over a tracked path that is not a file, and its S12 reads
  the names alone; `check_links.py` reads the Markdown files present; and
  `generated_counts.review_stages` reads review records, which are never check inputs. A
  link to a file the commit adds under the check inputs still fails `check_links.py` in
  that pass, rightly: the content then depends on the check change, which lands first.
  `scripts/safe_push.py` is unchanged: dropping the added files from the worktree's index
  as well would change what every check in that pass reads, `check_style.py`'s list of
  tracked files for S12 among them. This is a check change alone. Protected files
  changed: `scripts/negative_tests.py`, `tests/test_negative_tests.py`,
  `scripts/generated_counts.py` and `tests/test_generated_counts.py`.

- **A count moved with its content is a pinned value (#177, #75).** Train T1 (#177) put
  the lock's count of its words in [`Certificate/FIELDS.md`](../../Certificate/FIELDS.md)
  between count markers, which `scripts/render.py` fills and `scripts/check_fidelity.py`
  holds to the lock. FIELDS.md is a check input, and `pinned` in `scripts/safe_push.py`
  did not count a change to it as a value pinned to the edition. A content change that
  adds words to the lock, as the restricted rule of superposition (#75) does, must move
  that count in the same commit, while origin/main's own `check_fidelity.py` fails on the
  lock it changes; so `keep_apart` refused the content branch as a check change kept
  apart, and it could land in no order. A dry run of the pre-flight for
  `lean/superposition-restricted` found it. `pinned` now counts a change to the Markdown
  of the check inputs that are not code, `Certificate/`, `review/SCHEMA.md` and Markdown
  under `tests/` (`COUNTED_PROSE`), as a pinned value while nothing but the values
  between its count markers changes: the same markers stand, by name and in order, every
  byte outside their values is as it was, the file's mode is as it was, and a value
  moves. The markers are read by origin/main's own `scripts/generated_counts.py`, loaded
  from origin/main's tree, since the harness carries only `safe_push.py` and `heath.py`;
  a commit that changes that reader changes `scripts/`, and is kept apart in any case, so
  the commit's own `check_fidelity.py` reads the same markers and holds every value to
  the files it counts. A marker added, removed or renamed, any other byte changed, or the
  file added, deleted or given another mode, is still a check change, and the refusal now
  names such a file. Check code is never pinned by this rule: nothing under `scripts/`,
  and no code under `tests/`. `tests/model/MODEL.md` was already pinned whole, and stays
  so: a count marker in it may still be added, removed or renamed with the model's
  account, as before; holding its markers to stand is a check change of its own, for the
  owner (#187). This is not a weakening: every check still runs, origin/main's failure is
  still noted for the security review, and the commit's own `check_fidelity.py` must still
  pass, holding each moved value exactly to the files it counts; the rule lets through
  only a value that check already pins, and a change it could not judge (a marker added,
  removed or renamed, any other byte, the file's mode, anything under `scripts/`) is still
  kept apart. The docstrings, the comment on the pinned values, the module docstring and
  the refusal's list of pinned values say so. `scripts/test_safe_push.py` gains six tests
  beside the expectations' own: a new word in the lock, with FIELDS.md's count moved,
  lands as content, with origin/main's failure noted and the commit's own pass holding;
  FIELDS.md changed beyond those values (a line, a byte beside the marker, a marker added,
  removed or renamed, the file deleted or made executable) is kept apart; and the same
  count moved is a pinned value under `Certificate/`, `tests/` and `review/SCHEMA.md` and
  never in `scripts/`, in code under `tests/` or elsewhere in `review/`, read by
  origin/main's reader and never the commit's. Three more hold the rest: the text between
  two markers, and their order, stands, and a page added with a count is a check change; a
  page either side cannot read, a symbolic link, and origin/main's reader missing or not
  loading pin nothing; and a count moved to a value the lock does not give is refused by
  the commit's own `check_fidelity.py`, with the pinned values noted. No negative plant is
  added: [WORKFLOW](../WORKFLOW.md), section 8, asks for a focused regression for a guard
  defect, and the harness's own are in its suite. WORKFLOW, section 10, step 4, which
  lists the pinned values, gains a sentence saying a count between count markers in such
  Markdown is one, on the same terms. The protected files changed are
  `scripts/safe_push.py` and `scripts/test_safe_push.py`; `docs/WORKFLOW.md` and this page
  are not protected. A note for the security review: on a file system that ignores case,
  as macOS's does, a case-twin path such as `certificate/FIELDS.md` escapes the
  protected-path rule and `keep_apart`, and its text overwrites the real file in the
  pre-flight's worktree; CI, on Linux, is the backstop. That gap is already on main, and
  this change does not open it (#186). The owner approved this change on 20 October 2026,
  on condition that its reviews and /no-mistakes pass with no blocking finding; the
  independent review judged that it is not a weakening of keep_apart.

## 21 October 2026
- **The Jev client keeps no answer without its model's identifier
  ([#181](https://github.com/jackChallis/stoicheia/issues/181)).** `run` in
  [`scripts/audit/jev.py`](../../scripts/audit/jev.py) wrote a reply with no `model` as a
  successful answer, `score` counted it towards `--bar`, and a resumed run kept it. Each of
  the three now asks for the answering model's identifier, a nonempty string: `run` writes
  such a reply as an error line with the reason, `score` stops with a failure naming the
  answer's id and the reason, and a resumed run reports the output file, line and reason
  before asking the question again. The self-test's two noul cases gain the model they
  lacked. The new `tests/test_jev_models.py` (three tests, twenty-one cases) uses in-process
  replies and no key or network; it fails on the client before this change and passes after
  it, and it runs in CI's `check` job and safe_push's check sequence, immediately after
  `tests/test_release_gate.py`. The audit of Books I and II scores as committed: `score` on
  its answers gives the same output, line for line, before and after, with 95 rows for
  adjudication. The protected files this changes are
  `.github/workflows/ci.yml`, `scripts/audit/jev.py`, `scripts/safe_push.py` and
  `tests/test_jev_models.py`; [WORKFLOW](../WORKFLOW.md), section 8, lists the command.

- **The restricted rule is integrated after axiom wave one (A1).** On 20 October 2026,
  the integration merge at `bd86a7b6` has the restricted-rule revision `9fc4bdc9` as one
  parent and `tooling/superposition-model-check` at `5a848389` as the other. The tooling
  parent already contains main at `7834e3a7`, A1 and both superposition tooling branches.
  This brings the eight proved rules into the restricted-rule branch without restoring
  any retired axiom. A1 has landed; the landing order is A1, then this restricted-rule
  replacement, then wave two (A2, `lean/retire-axioms-2`). A2's landing carries the review
  of `drawsNothing`, its
  supporting prose and the audit pins when cited-law proofs gain construction
  dependencies, as #119 and #150 require. A1 alone does not make that change: I.4's
  cited laws still use the retained `triple_incidence2`, `eq_of_len_eq_zero` and
  `angle_add_of_inside`, not the retired `triple_incidence3` or `inside_of_angle_add`.

  The fuller A2 account, checked against its source at `d2c45450`, includes
  `same_side_symm` and `pasch3` as well as `triple_incidence2` and `eq_of_len_eq_zero`.
  Their proofs use circle intersections and Postulate 3, Postulate 1, Postulate 2 and
  Postulate 3 respectively, with points on straight lines where needed. The laws affected
  in I.4 are `neOfLen`, `rayUnique`, `rayOfAngle` and `rayOfAngleSide`; I.8 also cites
  the first two. This expands the earlier warning in a new entry, leaving the 19 October
  entry as written. Brief 0009 also makes part 4's inspection precise: the fresh symbols
  receive no objects in a hypothesis, but the cited laws quantify over all points and
  straight lines, and the triangle guard over straight lines. No new restriction theorem
  or completion of #150 is claimed here.

  Regenerated on the merge, the lock has 79 axioms (five postulates, Definition I.15 and
  73 tacit rules), with `"Tacit.superposition" = "Elements.Superposition.Rule Elements.primitives"`
  restated, and 208 words of vocabulary: `check_fidelity.py --write-lock` wrote the lock
  exactly as Git had merged it. The earlier 87-axiom and 206/208-word reports above remain
  evidence for their dated revisions; the 19 October preparation entry is unchanged. The
  20 October approval "as prototyped" and round 4 remain in force, with finishing tracked
  in #150.

  The six records the restricted rule changes, for I.2, I.3, I.4, I.8, I.23 and I.44, were
  read in full at `bd86a7b6` by an independent Codex reader, who found every item to pass
  or not to apply, and were stamped there (run "brief 0009 stage full, ship S3
  A1-integration re-read"). After that reading, /no-mistakes removed from
  `mishnah/I/08.md` its sentence on the former, existential rule; an independent review of
  `84a306e0..3ad74e04` found that I.8's commentary item still holds, every remaining
  sentence being as read.

  The protected paths this merge changes from both of its parents are these. Reconciled by
  hand: `Audit/Overlaps.lean`, `Audit/screen.py`, `tests/certificate_expectations.json` (29
  expectations, every one of both sides) and `model/Model/Audit.lean`; merged without
  conflict and kept from both sides: `tests/model/laws.toml`, `tests/model/search.py` and
  `tests/model/hyperbolic.py`. Regenerated: `Certificate/axioms.lock`, the count in
  `Certificate/FIELDS.md` and the model's results, `tests/model/results/angle_check.txt`,
  `tests/model/results/exhaustive.txt`, `tests/model/results/grid_check.txt`,
  `tests/model/results/hyperbolic.txt`, `tests/model/results/mutations.txt`,
  `tests/model/results/search-seed1.txt`, `tests/model/results/search-seed2.txt`,
  `tests/model/results/search-seed3.txt`, `tests/model/results/structured.txt` and
  `tests/model/results/summary.txt`; reconciled by hand with its counts regenerated:
  `tests/model/MODEL.md`; renewed from the lock: `model/lock.sha256` and
  `tests/model/lock.sha256`. Every check and pin of both sides stays.

- **The renderer's words follow the content.** The protected file
  [`scripts/render.py`](../../scripts/render.py) selects its Book III wording from
  `facts.json`, read once for each root through the renderer's guarded paths, as its
  other inputs are: `MixedAngle.ofSegment`, with a companion of III.16 and one of III.31,
  enables the mixed-angle row; `Arc`, `InSegment`, `OnArc` and `Arc.Congruent`, with
  III.24, III.26 and III.28, enable the segment row; `Arc` with `Arc.measure` enables the
  circumference row; `CirclesCut` enables Definition III.3's row, on cutting and
  touching, and the line on that definition on the pages where Heath's brackets cite it;
  `Foot` enables the account of perpendicular feet in Definitions III.4 and III.5,
  including a diameter at no distance from the centre, each row with the companion it
  names, III.14 general or III.15 nearer; and III.24's shared step `BookIII.placement`
  enables the account of its application of one segment to another. That account is
  built from III.24's entry, so that it is true by construction: only when III.24's
  `direct_axioms` leave superposition out, and a proposition `placement` cites rests on
  it, does it say that `placement` uses superposition only through the propositions it
  cites, and it names those of them that call on superposition themselves; otherwise it
  says only that the proof applies the segment by `placement`. Each keeps the present
  wording until its named content, and every proposition and companion it names, is
  there. Comments about III.2's unused overlapping rule are corrected, and the
  clause-map docstring no longer names particular propositions. The renderer
  distinguishes all, some and none of a record's overlapping rules, using `facts.json`'s
  `axioms` for the proof's full dependencies. When the proof uses all or none, the
  status line and Overlap row keep their exact wording, with no added sentence repeating
  the record's note. Only partial use adds a clause naming both the rules used and those
  unused in the status line, the Overlap row and the book summaries. One rule unused
  reads "does not use `b`", two "uses neither `b` nor `c`", and three or more "uses none
  of `b`, `c` and `d`". This applies to every record, including both kinds that contain
  the proposition and rules that supply a step. On main's present content, every
  generated page stays byte for byte unchanged. The protected file
  [`review/SCHEMA.md`](../../review/SCHEMA.md) now states that the line under the
  enunciation and the book's summary say whether the proof rests on all, some or none of
  the named rules, naming each rule used and unused for partial use, and that the
  Overlap row gives the record's note word for word and adds that account only for
  partial use. The protected test file
  [`tests/test_check_style.py`](../../tests/test_check_style.py) gains two wording cases
  beside its cases of the page: the clause for rules left unused, and the account of
  `placement` from `facts.json`, read afresh for each root. Each fails on the renderer
  before this change.
  The protected file [`scripts/scaffold_book.py`](../../scripts/scaffold_book.py) takes
  brief 0008, section 7's approved III.5 signature (`CirclesCut`, without the separate
  inequality of circles) and its comment on cutting and contact within and without,
  exactly as the supplied scaffold patch specifies. A search of `scripts/` and `tests/`
  found no check that reads the scaffold's Book III strings. The scaffold records the
  approved statements; it was not run to rewrite any Lean file.
  This tooling change lands before the content it describes, so that the content's
  pull request changes no check input beyond the values pinned to that content:
  the content's new lock makes main's checks fail, and `scripts/safe_push.py` keeps such
  content apart from an accompanying change to `scripts/render.py`. No check, statement,
  lock or review record changes here, apart from the approved signature in the scaffold
  and the two cases the style test gains.
- **III.1's porism has its whole axiom list pinned.** The first expectation in
  [`tests/certificate_expectations.json`](../../tests/certificate_expectations.json), a
  protected file, gains `equals` holding the porism's full list regenerated from main at
  `2e8aecf` (21 October 2026, after axiom wave one), in `facts.json`'s order. The porism's
  own entry carries every assumption its proof uses: Definition I.15, Postulates 1 to 4
  and the reviewed 55 tacit rules. `Tacit.centre_unique` is a theorem since wave one, so
  the list holds the axioms beneath it. The `ref`, `field` and count of 55 tacit rules
  stay as they are; no other expectation changes. This makes the check stricter on its
  own, before the content it describes: an existing `equals` value and `count.is` may
  move with that content, as pinned values. Train C6b can then reprove the porism by
  Euclid's reductio and move the pinned list and count to that proof's assumptions in
  its content pull request.
  The `axioms` row of [`Certificate/FIELDS.md`](../../Certificate/FIELDS.md), a protected
  file, gave III.1's and its porism's counts as fixed; it now says that the list follows
  each proof's dependencies and that the expectations pin what those two must hold, which
  stays true when a re-proof moves the pinned values. The protected regression test
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) keeps its checks of
  growing and emptying an `includes` list by exercising the still-list-shaped I.5
  expectation, and its simulated future re-proof moves the porism's exact list together
  with the counts. It reads III.1's tacit count from
  `tests/certificate_expectations.json`, so it holds before and after the content it
  describes. No guard is weakened.

- **Heath's letters upright in both figures (#159).** The owner decided on 18 October
  that Heath's letters take one style in the text and in both figures, which the voice
  rules' check change, above, reads as upright. The figures are now set upright. Every
  `figures/<book>/NN.svg` and `NN-idea.svg` of Books I to III, 198 in all, drew the letters
  italic: 83 of Euclid's figures set `font-style="italic"` on the root `<svg>`, and the
  other 16, with all 99 figures at a glance, on the `<g>` that holds the letters. That one
  attribute is removed from each, so the letters take SVG's default, upright. Nothing else
  in a figure changes, and no letter moves. Every text the attribute set italic was one of
  Heath's letters, so nothing italic on purpose is lost. S26 now measures each letter by
  the hull of the upright capital, and every letter still stands 2 clear of every stroke
  and dot: the closest is III.33's F, at 2.05. `scripts/check_style.py` reports no D15.
  The modern figures (`NN-modern.svg`) do not change: their capitals were upright already,
  and the paragraph's own names stay italic, as S25 requires. The switch follows in a
  change of its own to the check
  ([#159](https://github.com/jackChallis/stoicheia/issues/159)):
  `UPRIGHT_LETTERS_REQUIRED` set to `True`, a test that plants an italic letter, and
  STYLE's wording for the switch. Until then S15 and S20 still accept a figure whose
  letters are all italic. No protected file changes.

- **Twenty entries come out of `REACH_PENDING`
  ([#159](https://github.com/jackChallis/stoicheia/issues/159)).** Run on `8e9a1879` with
  Lean, after `lake build` and `lake build Audit`, `scripts/check_style.py` reported 19 of
  the list's 38 entries done, with no finding of any of their rules left, and this change
  takes exactly those out: the fourteen notes of Book Zero, `Elements/Figure/*.lean`
  (S22); `docs/reports/gaps-book-I.md` (S7); `docs/reports/gaps-book-II.md` and
  `docs/reports/read-through-01.md` (S7 and S12); `review/I/09.toml` (S7); and
  `review/II/14.toml` (S12), the two that the progress check of 20 October on #159 named.
  Under `--no-lean` the same check reported 18 of them, the two "S7 S12" entries for S7
  alone and `review/II/14.toml` not at all, since S12 alone asks Lean; with Lean their S12
  is done too, so each of the 19 comes out whole and no entry is left with a rule fewer.
  No rule of the 19 entries that remain was reported done, and none of them changes. D16
  goes from 364 lines to 345 with Lean, and from 202 to 184 under `--no-lean`: the 19 and
  18 done lines go, the findings are line for line the same, and both runs pass with no
  "done" line. The comment over the reports' entries gave the S12 inventory of two of them
  on `bd3b72a`, 147 and 2; it now gives the one left,
  `docs/reports/mixed-angles-prototype.md`. The paragraphs on the list, in the script's
  docstring and in [STYLE](../STYLE.md), section 8, now say that a file with findings on
  19 October "was" listed, since a mended file no longer is; neither holds a count, and no
  count marker counts the list. Of the 19 entries that remain, one names the closed #66
  as its mender and nine name no issue. The protected file changed is
  `scripts/check_style.py`; `tests/test_check_style.py` is unchanged, since
  `test_done_cases` and `test_done_without_lean` already test the done report.
  After origin/main was merged at `17ae8e2a`, where the restricted rule of superposition
  rewrote I.8's Lean, the check reported one entry more done, `Elements/BookI/Prop08.lean`
  (S22, which named #29), both with Lean and without; it comes out too, so 20 entries
  come out and 18 remain, and both runs again pass with no "done" line.

- **Heath's letters upright: required, the switch on
  ([#159](https://github.com/jackChallis/stoicheia/issues/159)).** Every one of the 198
  figures now sets Heath's letters upright (above), so the switch `UPRIGHT_LETTERS_REQUIRED`
  in [`scripts/check_style.py`](../../scripts/check_style.py) is `True`: S15 fails an
  italic letter in Euclid's figure, and S20 one in a figure at a glance, whether one letter
  is italic or every one, and D15 is empty. D15 stays, empty, as D14 did when
  `IDEA_LETTERS_REQUIRED` went `True`: the switch keeps its off position, and D15 is what
  that position reports, so its description and STYLE's row say "while the switch for
  upright letters is off". `GLYPHS_ITALIC` stays too: S26 still measures an italic letter
  as Georgia draws it, and measuring it upright would change two of S26's clearance cases.
  A new case in [`tests/test_check_style.py`](../../tests/test_check_style.py), `Upright`,
  sets `font-style="italic"` in temporary copies of I.1's two figures, on one letter and on
  the root, and requires S15's or S20's finding and no D15; on origin/main's check, where
  the switch is `False`, its four planted cases fail. The figure fixture that the S26 and
  SVG input cases share drew its letters italic, and now draws them upright; the sagitta
  cases placed their near E by its italic hull, and now place the upright E at the same
  clearance (1.975 and 1.981, against 1.979), still nearer 2 than a three-degree chord's
  sagitta. No case is removed or loosened. [STYLE](../STYLE.md), sections 7 and 8,
  describes the finished state: the switch clauses of S15 and S20, the D15 row and the
  switch paragraph; its **[checked]** for upright letters, in Euclid's figure and at a
  glance, now holds whole. The switch is never turned back to quiet a figure: the figure is
  set upright. #159's items on `REACH_PENDING` are untouched. The protected files this
  changes are `scripts/check_style.py` and `tests/test_check_style.py`.

- **Short hashes are read from Git, and the acceptance report's revision has twelve
  digits (#178, items one and three).** `scripts/test_safe_push.py` looked for the commits
  a pull request's body lists by the first seven digits of each hash, and its clone
  pinned `core.abbrev` to 7 to make that so. Git reads `core.abbrev` as a minimum width,
  and its own width grows with the object count: eight digits on a clone of main today.
  The pin is gone. A new helper, `short_sha`, asks the clone under test for a commit's
  short form with `git log -1 --format=%h`, as `scripts/safe_push.py` writes the body,
  and the three tests that sliced seven digits use it; any later test that needs a short
  hash can too. Nothing they check is loosened. The other half of item one was already
  done: the stage test reads the first stage line from `docs/program.toml` (the entry of
  20 October above).
  `scripts/check_acceptance.py` wrote the report's revision with `git rev-parse --short`.
  Since the entry of 20 October on S12 and the word "Revision", S12 takes a hash of 7 to
  40 digits beside "Revision" as a commit, so a regenerated report passed at Git's
  usual widths. Under a `core.abbrev` of 4 to 6, though, the revision is shorter than
  `heath.COMMIT` allows, and when it begins with a letter S12 puts it to Lean as a name;
  and its width differs from one clone to another, so the same files gave different
  reports. The generator now writes twelve digits (`REVISION_DIGITS`, with
  `git rev-parse --short=12`), the width `safe_push.py`'s pre-flight summary gives
  commits, in the form S12 already reads. S12, its exemptions and `REACH_PENDING` are
  unchanged. A new test in
  `tests/test_check_acceptance.py`, `Report.test_a_regenerated_report_passes_s12`, writes
  the report through the generator in a small repository under `core.abbrev` 4, 9 and
  Git's own width, and puts each report to S12's plan: on the old generator, S12 would
  put the four-digit revision to Lean, and the three revisions differ; now each is the
  same twelve digits, and S12 asks Lean about nothing. The committed report's revision,
  `33602846`, is all digits, which S12 does not read as a name, so it passes as it
  stands; its next regeneration writes twelve digits.
  A review of that change found a second way for the report to fail S12, one that no
  regeneration cleared. The style check reads the report a run replaces, and E5 quoted
  each of its findings in the new report with the message's backticks. So a finding on
  the old report, on a revision S12 put to Lean or on a name Lean does not know (B2 and
  E2 quote such names on purpose), came back in the new report away from the word
  "Revision"; S12 put it to Lean again, and each regeneration quoted the last finding
  back. `check_style_rules` now quotes each of the style check's findings whole, as one
  code span whose fence is one backtick longer than the longest run of backticks in it,
  with a space inside each end. E5 still fails, once, with the whole finding, and a
  reader sees it exactly as the check printed it. S12 reads a span as a name only when
  the span is one name or opens with `name :`, and a quoted finding opens with its rule
  and file, so S12 finds no name in it; S1, S7, S8 and S22, the style check's other
  rules for a report, read it outside code and find nothing in it either. So the report
  after a fixed finding passes every rule, not S12 alone. Taking the backticks away, as
  a first version of this change did, closed S12's loop alone: GitHub would read a quoted
  excerpt's `<book>` as an HTML tag and drop it, and set `2*a*b` in italic, and an em
  dash or a curly quotation mark in a quoted excerpt's code would come out of code,
  where S1 or S8 finds it in the next report, and every regeneration quotes it back. The
  code span closes as well an older loop of the same kind, which main's generator has:
  an S1, S8 or S22 finding on the report itself. B2's and E2's own messages are unchanged. A
  second test, `Report.test_a_finding_on_the_old_report_is_not_quoted_back_to_s12`,
  gives the generator three such findings through a stand-in for the style check (the
  old report's four-digit revision, the twelve-digit one and an unknown name) and puts
  the regenerated report to S12's plan: on the previous generator S12 would put all
  three to Lean; now it asks about none, and E5 gives each finding as one code span. Two
  more tests hold the rest. The first,
  `Report.test_quoted_code_is_shown_as_the_style_check_printed_it`, quotes findings
  whose excerpts hold `figures/<book>/NN.svg`, `h : 2*a*b = c` and a name in double
  backticks, and reads each back, as CommonMark reads a code span, exactly as printed.
  The second,
  `Report.test_a_finding_on_the_old_report_is_not_quoted_back_to_the_text_rules`, puts
  an old report with an em dash, a definition without its book and curly quotation
  marks to the style check's rules for a report, quotes their findings through the
  generator with one whose excerpt holds an em dash only in code, and finds that those
  rules and S12's plan find nothing in the regenerated report. Both fail on the
  generator that took the backticks away, whose regenerated report fails S1, S7 and S8
  nineteen times over, and pass now. The protected files changed are
  `scripts/test_safe_push.py`, `scripts/check_acceptance.py` and
  `tests/test_check_acceptance.py`.

- **A carried passage's helper is named by its kind
  ([#163](https://github.com/jackChallis/stoicheia/issues/163)).** The sentence on how to
  read a page's listing said "where a porism is proved as a theorem of its own" for every
  carried passage that names a `helper`. Once III.25's core moves into Elements, its
  companion `Prop25.complete` is to carry the step Heath cites as III. 9, and the page would
  call it a porism. The protected file [`scripts/render.py`](../../scripts/render.py) now
  finds the entry of facts.json's `attached` that the helper names, written in one of three
  ways (`Prop16.porism`, `BookIII.Prop16.porism` or `Elements.BookIII.Prop16.porism`), and
  takes it apart with `heath.parse_ref` (`carried_ref`). The sentence names each such
  theorem by its kind, "a porism" for a porism, "a companion" for a companion; several
  read, for example, "a porism and two companions are proved as theorems of their own". It
  counts theorems, not passages: `Prop25.complete` is to carry the same [III. 9] step in
  each of III.25's three cases, from "Therefore the circle drawn with centre E", from "D
  will be the centre of the completed circle" and from "and if we construct, on the
  straight line BA", and is one companion, as one theorem named two ways is one. A carried
  helper of any other kind stops the render, naming the proposition, the helper and the
  three ways render.py reads such a name: a lemma or another proposition that does a step
  makes a `helper` passage, "Done by" it, and is not a theorem attached to the
  proposition, so a word for it here would put a passage of the wrong kind on the page.
  The comment above `PASSAGE_WORD` says the same, and CERTIFICATE.md's key gives *Proved
  separately* for the kinds the records carry, today "a porism". `use_self_check` gains
  nine cases, `CARRIED_CASES`: a porism; a companion; a porism with two companions, in the
  three ways of naming one; one companion named two ways; one porism carrying two
  passages; that porism beside a companion; and a lemma, another proposition and another
  proposition's companion, each refused. Against origin/main's render.py (`ac6e5389`)
  seven of them fail, the companion's read as "a porism", and the two with a porism alone
  pass. Against this change's first round (`4d261614`), which counted passages, the three
  that repeat a theorem fail, reading "two companions", "two porisms" and "two porisms and
  a companion". The protected file [`review/SCHEMA.md`](../../review/SCHEMA.md) allows a
  companion beside the porism as a carried passage's `helper`, gives the three ways of
  writing it, says how the page names each, counting theorems, and says that render.py
  stops on any other. `heath.py` and `check_fidelity.py` check no carried helper's kind:
  check_fidelity asks only that it is declared, and finds a declaration by more names than
  these three (`Elements.Prop16.porism`, or a short name that ends exactly one declared
  name), so nothing refused a companion, render.py's refusal names the three it reads, and
  no other validation changes. Every generated file stays byte for byte as it was: the three
  pages that print the clause, I.15, III.1 and III.16, each carry a porism. The fourth
  item of #163, III.25's page naming `Prop25.complete` a companion, waits for the core's
  move.

- **The merge gate requires the ruleset's five checks (#142).** On 20 October the owner
  made `formal-model` and `acceptance` required status checks in the ruleset on main,
  beside `check`, `model` and `negative`, as the entry of that date on content kept fresh
  records. Read on 21 October with `gh api repos/{owner}/{repo}/rulesets/25333614`, the
  ruleset's required status checks rule is:
  ```json
  {"parameters":{"do_not_enforce_on_create":false,"required_status_checks":[{"context":"check"},{"context":"model"},{"context":"negative"},{"context":"formal-model","integration_id":15368},{"context":"acceptance","integration_id":15368}],"strict_required_status_checks_policy":true},"type":"required_status_checks"}
  ```
  The integration 15368 is GitHub Actions, and the strict policy asks that a pull
  request's branch be up to date with main before it merges. `REQUIRED_CHECKS` in
  `scripts/safe_push.py` now names the same five, in the ruleset's order, so
  `git safe-push --merge`, and the pre-flight's CI watcher, which judges as it does, give
  "missing" when a pull request has no passing run of `formal-model` or of `acceptance`,
  and "failure" when one fails, as for the first three. A skipped run is not a pass. The
  CI workflow runs on pushes as well as pull requests and skips `acceptance` in the push
  event's run; `judge_checks` counts a pass from any run reported for the head, so the
  pull request's own run, which includes both jobs, is the one that must pass it, and a
  check whose every run was skipped is "missing". GitHub, which accepts a skipped
  required job, makes no such distinction
  ([WORKFLOW](../WORKFLOW.md#8-validation-on-the-integrated-revision), section 8). The
  docstrings of the module and of `judge_checks` name the five checks. In
  `scripts/test_safe_push.py`, `PASSING` holds the five, and `Units.test_judge_checks`
  shows that a missing `formal-model` and a missing `acceptance` each give "missing",
  that a failing one gives "failure", and that a skipped run gives "missing" alone and
  "success" beside a passing one; with main's list of three, the two missing cases give
  "success" and the test fails. Nothing is loosened: no other check, expected value or
  gate changes. WORKFLOW, section 8, and PROGRAM, section 4, no longer describe the gap,
  and PROGRAM's account of 18 October notes the two checks added since. The entries of
  18, 19 and 20 October that call these checks not required, or say that safe_push tests
  for three, are true of their dates. The protected files changed are
  `scripts/safe_push.py` and `scripts/test_safe_push.py`.

- **S24 to S26 grant a name only to a letter that is one, and refuse an arc that SVG does
  not draw as an arc ([#172](https://github.com/jackChallis/stoicheia/issues/172)).** The
  two gaps that the reviews of S24 to S26 left open at train H10 are closed in the
  protected file [`scripts/check_style.py`](../../scripts/check_style.py). The names:
  emphasis through a full stop or an apostrophe was refused only with a bare letter on its
  other side, so `*e*.*g*.` was neither refused nor read as e.g., and granted e and g.
  `modern_markup_findings` now refuses emphasis on either side of the stop or on both, the
  stop escaped or not, and refused markup supplies no names. The same reading found three
  more letters that are no names: `e\.g\.` granted e and g, an invisible format character
  (a zero-width space, a soft hyphen) let a letter of one visible word stand alone, and the
  p of Heath's page, "(vol. 1, p. 389)", was granted on five pages of main, II.6, II.7,
  II.8, II.14 and III.8. The independent review of this change found six more of the same
  kind, none on main's pages: a combining accent (e and U+0301, éxponent), a Cyrillic
  letter (eхponent), an accented word (déjà), a Hangul filler, which Unicode counts as a
  letter and which shows nothing (e and U+3164 before .g.), two spaces in `e.  g.`, and a
  Roman page number (p. ix). `ABBREVIATION` now reads an escaped stop, spaces inside e.g.
  and i.e., and the p of a page before its number, taking a Roman number's letters with
  it (p. ix, pp. v–vii). `modern_names` keeps a letter in its word when a letter of any
  script, Greek too, a mark or a format character stands beside it (the new
  `joins_word`), so that the r of 2πr is a name only in TeX. The markup check refuses a
  format character and the rest of Unicode's default-ignorable characters (the new
  `INVISIBLE`: the Hangul fillers, the variation selectors, the combining grapheme joiner).
  On main the names change only by those five p's, which no modern figure draws, and no
  paragraph is refused. The arcs: by SVG's implementation notes for arcs, every choice of the large-arc
  and sweep flags draws something once radii too short to reach the ends are enlarged
  (F.6.6), for two distinct ends then lie on two ellipses of those radii, or on one when
  the radii only just reach, and the flags take one arc of them from end to end (F.6.5); on
  one ellipse both arcs are halves and the large-arc flag changes nothing. So no flag
  choice is refused. What does not draw as an arc is an arc whose ends are one point,
  which SVG omits, and one with a radius of 0, which it draws as a straight line (F.6.2).
  The new `arc_fault` finds either, wherever the path stands when the arc begins, testing
  the ends first, as F.6.2 does, so that an arc with both is named as drawing nothing; S26's
  `supported_svg` refuses the path, naming what SVG draws; S24's `modern_path` refuses the
  same arcs in the modern figures. None of main's 317 arcs is either, and every figure and
  page on main passes. The protected file
  [`tests/test_check_style.py`](../../tests/test_check_style.py) gains the cases, 95
  subtests that fail on the check before this change and pass after it (two of them the
  clearance case below), and
  `test_arc_flags_always_draw`, which passes before and after: the four flag choices, with
  radii enlarged, just reaching and ample, each draw on the side of the chord the sweep
  flag gives, and the large-arc flag changes the arc only when the radii are ample. One
  clearance case moves: the path whose omitted arc showed that such an arc does not break
  a join is now refused at the figure entry points, so its join claim is held on the
  strokes S26 measures, read directly with the default join, miter and round, as main
  measured it, which equal those of the same path without the arc, itself a case at the
  entry points; the refusal is asserted at both entry points. The
  protected file [`scripts/negative_tests.py`](../../scripts/negative_tests.py) gains item
  19, three plants in real files restored after: `*e*.*g*.` in II.7's modern way with an
  italic e in its figure, an italic p in that figure beside Heath's "p. 389", and the two
  arcs in I.1's figure. Each is caught by this check, and main's check passes each planted
  tree. [STYLE](../STYLE.md), section 8, says each change in the rows of S24, S25 and S26.
  No check, test or expected value is weakened.

- **The centre-given tag says what the statement does, not why (#59).** The meaning of
  `centre-given` in the protected file [`review/terms.toml`](../../review/terms.toml)
  gave a reason: "a circle in Lean has a centre only when a hypothesis or Postulate 3
  gives it one". Train C6a adds the owner's rule `Tacit.exists_centre`, which gives every
  circle a centre, and the reason then becomes false under every record that carries the
  tag, until step 6 of [brief 0008](0008-centre.md) retires their uses. The meaning now
  says what the tag records, which holds before and after the rule: the statement
  gives the circle its centre as a hypothesis, where Euclid's setting-out takes the centre
  or a proof needs one. It also says what the rule makes true: once the rule is in the
  lock, every circle has a centre, so the hypothesis asks only for a centre the circle
  already has and excludes no circle. This is not the new meaning that brief 0008 rejected
  (section 4, and question 9 in section 8), which would have kept the tag on the twelve
  records that name a centre: the tag still leaves all 31 records in step 6, and the term
  leaves `review/terms.toml` in step 7; until then its meaning stays true. The term's kind and
  name do not change, no record changes, and no page changes. It is a check input, so it
  lands in a pull request of its own, before train C6a. Protected file changed:
  `review/terms.toml`.

- **Book Zero's imports are read as Lean reads them
  ([#200](https://github.com/jackChallis/stoicheia/issues/200)).** Rule 3 of
  [`scripts/check_fidelity.py`](../../scripts/check_fidelity.py), that Book Zero
  (`Elements/Figure/`) never imports a proposition, matched `^import Elements\.Book` in the
  raw source: `import`, one space and `Elements.Book` at the start of a line. An
  independent reviewer on ship TT showed five other spellings of that import passing it in
  a planted file, all of which Lean 4.35 accepts: two spaces, a line break between `import`
  and the module, a remark between them, `«Elements»` and `«BookI»`. Tried on Lean 4.35
  itself, more pass as well: nothing between `import` and a «…» part or a remark, a line
  comment or a nested remark between the words, and a second import on the same line. The
  rule also passed the five other forms of an import that the toolchain's header grammar
  (`Lean/Parser/Module/Syntax.lean`) accepts after `module`: `public import`,
  `meta import`, `public meta import`, `import all` and `meta import all`. Lean refuses
  each of them on this edition ("cannot import non-`module` Elements.BookI.Prop01 from
  `module`", checked with Lean 4.35 against the built I.1), since the edition's files are
  not modules, so none can import a proposition today; the rule refuses them all the same,
  and their plants keep it ready for when the files are modules. The rule now reads every
  `import` in the Lean as rule 4 reads it, through `read_lean`, so that a comment never
  hides one and a string, a raw string or a «…» name never makes one, save a string whose
  braces `read_lean` keeps as code. It takes the module named after each import, past
  `all`, and refuses the import when that module, in NFKC and case-folded, begins
  `Elements.Book`. The exception fails closed: rule 4 keeps a string's braces as code when
  its two readings, plain and with holes, end in one place, so an `import` inside them is
  read too. `def s := "{ import Elements.BookI.Prop01 }"`, which Lean reads as text, is
  refused as an import of a proposition, and `"{import Elements.BookI.Prop01}"` as an
  import the scan cannot read; a subtest of the Book Zero tests pins the first. Two more
  ways in came to light in the testing. Lean joins a name's parts into a path:
  `import «Init/Data».List.Basic` loaded `Init/Data/List/Basic`, so
  `«Elements/BookI».Prop01` could load a built proposition. And on a disk that ignores
  case, as macOS's does, `import lean.data.json`, a Kelvin sign for a `k` and a long s
  for an `s` each loaded the module they stand for. So a part that is not a plain name
  once its «…» are off, or a name that whitespace does not follow, is refused as unread,
  failing closed, and modules are compared case-folded. Last, an import of one of the
  edition's own files that brings a proposition in, as `Elements.Companions` does, is
  refused too: the rule follows the edition's files breadth first (`brought_in`) and
  names the file that imports the proposition. Two forms pass the rule, and Lean refuses
  each with an error, so that the build fails: a second module after one `import` (the
  reviewer's I5, "unexpected identifier; expected command", which imports the first
  module alone) and a name beginning `_root_.` ("unknown module prefix"). A tab, a
  no-break space, a «…» part holding a dot and an import after a command, each an error
  in Lean too, are refused by the rule as well. On main the rule reads the 42 imports of
  Book Zero's 16 files, exactly their header lines, and refuses none.

  A new item of [`scripts/negative_tests.py`](../../scripts/negative_tests.py), 20, the
  next after main's highest, plants a new Book Zero file for each of 19 forms, the
  reviewer's five and the fourteen above, and requires each refused on its file and line,
  while a file holding the import only in a comment, a remark, a string and a «…» name,
  beside an import of Book Zero, is not named at all.
  [`tests/test_negative_tests.py`](../../tests/test_negative_tests.py), whose
  `CircleRuleTests` already test one of check_fidelity's rules, gains
  `BookZeroImportTests`: seven tests on a small tree, without Lean, of every planted form;
  text that only holds an import; a comment or a string that hides none; `module`,
  `prelude` and Lean's own modules passing; names the scan cannot read; a proposition
  brought in through two files that import each other; and a file outside Book Zero, which
  rule 3 leaves alone. Against origin/main's check_fidelity (`001620f1`) each of the 19
  forms passes, the plain `import Elements.BookI.Prop01` alone being refused; now all 19
  are refused. Nothing is loosened, and #197's forbidden-command scan is untouched. The
  protected files changed are `scripts/check_fidelity.py`, `scripts/negative_tests.py` and
  `tests/test_negative_tests.py`.
