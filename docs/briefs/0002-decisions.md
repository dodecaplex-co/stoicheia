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
  name in a test in `scripts/test_safe_push.py`, a protected file, waits for a tooling pull
  request of its own.

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

- **The checks, made ready for retiring axioms (proposed, pending the evidence).** The owner
  asked, "Fewer axioms is better. Any more that can go?", and approved retiring axioms in
  principle on 19 October 2026, pending the evidence; nothing lands until the owner has seen
  it. A search found eight that can go with no choice of basis (the retirement's own entry
  names them). Since a check never changes in the pull request of the content it judges,
  this change prepares the checks first, with all 87 axioms in place, and weakens none:
  [`scripts/negative_tests.py`](../../scripts/negative_tests.py) reads the expected count
  from the lock instead of a hard-coded 87;
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) moves its mutation, count
  and membership fixtures to laws and pins that survive (I.5's inherited Postulate 3);
  [`scripts/safe_push.py`](../../scripts/safe_push.py) drops the generators `gs_adj` and
  `gs_lmc_opp` from its allow-list, because
  [`tests/model/hyperbolic.py`](../../tests/model/hyperbolic.py) now samples those two laws
  with generators the other laws use, with byte-identical output;
  [`tests/model/derived.py`](../../tests/model/derived.py) (new) keeps the eight laws'
  configurations as derived properties, which
  [`tests/model/exhaustive.py`](../../tests/model/exhaustive.py),
  [`tests/model/structured.py`](../../tests/model/structured.py) and
  [`tests/model/run.py`](../../tests/model/run.py) run, count and enforce as strongly as the
  laws, [`tests/model/MODEL.md`](../../tests/model/MODEL.md) records that independent
  contract, and [`tests/model/mutations.py`](../../tests/model/mutations.py) changes only
  a description; `model/Check/` compares the eight hand translations directly with the
  Elements declarations, so the comparisons hold whether those are axioms or theorems.
- **One certificate pin dropped, with the owner's approval.** The retirement makes
  `Tacit.centre_unique` a theorem, so no certificate can list it, and the first expectation
  in [`tests/certificate_expectations.json`](../../tests/certificate_expectations.json),
  that III.1 Por.'s assumptions include it, had to go first, as the pin dropped for #60 did.
  On 19 October 2026 the owner approved this first step of a two-step pin flip: commit
  `5d200cf` removes the `includes: ["Tacit.centre_unique"]` pin while retaining its count.
  Deleting that dependency still fails, but a substitution that keeps the count would no
  longer be caught. C6's full `equals` pin remains pending; the retirement then adds stronger
  pins that III.1, III.1 Por., III.2 and II.14 rest on none of the eight. This approval is for
  the first pin change alone; the retirement itself remains pending the evidence and the
  owner's separate decision.
- **Eight axioms retired, 87 to 79.** The owner asked,
  "Fewer axioms is better. Any more that can go?", and approved retiring axioms in
  principle on 19 October 2026, pending the evidence; this lands only when the owner has
  seen it. Each of the eight keeps its name and exact type and becomes a theorem at the
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
  AB (Intersection 3), so that no certificate entry rests on Circle 2 or Circle 3, and new
  pins say so for II.14, III.1 and III.2. The axioms leave
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
  the measured counts of III.1 and its porism (55 tacit rules each) and new pins that III.1,
  III.1 Por., III.2 and II.14 rest on none of the eight. The formal model's generated
  laws, checks and assembly follow from its generator; its proofs in the plane stay, as
  derived facts. Proposition and porism statements, definitions and `--` lines are
  unchanged; the records whose Lean changed were read again and stamped by readers who
  wrote none of them.
- **The certificate's and the schema's examples follow the eight retired axioms.** A
  check-input change of its own, landed after the retirement of the eight (87 to 79), which
  leaves the check inputs alone.
  [`Certificate/FIELDS.md`](../../Certificate/FIELDS.md) updates its axiom examples and
  the counts for III.1 and its porism because `centre_unique` and Circle 2 are now theorems.
  [`review/SCHEMA.md`](../../review/SCHEMA.md) updates its overlap examples to distinguish
  current axioms from proved rules; its fields, requirements and worked TOML examples stay
  unchanged. No check, field or requirement changes.
- **The numerical checks, made ready for the second axiom retirement.** This preparation
  keeps all 79 axioms in place. Under [WORKFLOW](../WORKFLOW.md), section 10, the check
  change lands in a pull request of its own before the retirement it judges. The 31 laws
  due to become theorems also have derived properties, so their numerical checks survive
  removal from the axiom registry. Protected files changed relative to `lean/retire-axioms`:
  [`tests/model/derived.py`](../../tests/model/derived.py) keeps each of those 31 laws'
  predicates word for word, alongside the eight already retained;
  [`tests/model/exhaustive.py`](../../tests/model/exhaustive.py) and
  [`tests/model/structured.py`](../../tests/model/structured.py) call each by its
  `derived.` name on the existing configurations and newly sample the laws they did not
  yet reach, five in the exhaustive harness and ten in the structured harness;
  [`tests/model/MODEL.md`](../../tests/model/MODEL.md) records the 39 derived properties
  and the two harnesses' counts. No check is weakened: comparing each new derived
  predicate's body with its law in `tests/model/search.py` found all 31 byte-identical,
  with the same parameters, guards and conclusions. The eight earlier predicates stay
  unchanged. The added samples let the unchanged `tests/model/run.py` requirement hold
  for every derived property: each exhaustive or structured run must report it with its
  hypotheses met and no counterexample, independently of the axiom registry.
- **The safe-push harness, made ready for the second axiom retirement.**
  [`scripts/test_safe_push.py`](../../scripts/test_safe_push.py) now plants its added law
  beside `Tacit.line_unique`, uses that surviving law for mutation and expected-failure
  fixtures in both numerical models, and uses the same surviving dependency for its III.1
  re-proof and certificate-expectation fixtures. Every test case, exact replacement,
  count decrement and rejection expectation remains in place.
- **Thirty-one more axioms retired, 79 to 48 (proposed, pending the evidence).** The owner
  decided on 19 October 2026: "Please do both. 79 is rather large with so many books in
  front of us." That is, the eight above, and then the largest further set of
  retirements under two constraints: Euclid's six (Postulates 1 to 5 and Definition 15)
  stay explicit assumptions even where they are derivable, and no certificate entry may
  rest on Circle 2 or Circle 3 (`Tacit.inside_of_between`, `Tacit.outside_of_between`).
  This lands only when the owner has seen the evidence. An exact search over every checked
  derivation, the earlier search's and a second search's that avoids Circle 3, found a
  largest set of 31; it is a maximum over the derivations found, not a proof that no
  smaller foundation exists. Among the maximum sets, this one keeps the most of System E's
  plain incidence and order rules (`line_unique`, `between_symm`, `between_cases`,
  `not_between_of_between`, `not_on_line_of_same_side`, `same_side_trans`, `pasch2`,
  `exists_point_on_line`). Each keeps its name and exact type and becomes a theorem in four
  new Book Zero modules, which `Elements/Figure/Basics.lean` imports, so no proposition
  statement or import changes: `centre_inside`, `on_circle_of_len_eq`, `same_side_symm`,
  `exists_point_same_side`, `ne_of_between`, `on_line_of_between_ends`, `pasch4`,
  `same_side_refl`, `triple_incidence1`, `pasch3`, `inside_not_on` and `eq_of_len_eq_zero`
  in [`Elements/Figure/RuleBase.lean`](../../Elements/Figure/RuleBase.lean);
  `inside_of_len_lt`, `len_lt_of_inside`, `ne_of_between_ends`, `on_line_of_between`,
  `between_of_between_left`, `between_of_between_right`,
  `circles_meet_of_on_inside_outside`, `exists_point_opposite_side`,
  `circles_meet_opposite_side`, `exists_point_between`, `line_meets_circle_of_inside`,
  `not_between_of_between_between`, `same_side_or`, `triple_incidence2`, `pasch1` and
  `exists_point_on_line_off_line` in
  [`Elements/Figure/Incidence.lean`](../../Elements/Figure/Incidence.lean); `area_swap` and
  `between_of_area_add` in [`Elements/Figure/AreaRules.lean`](../../Elements/Figure/AreaRules.lean);
  and `exists_point_on_circle` in
  [`Elements/Figure/CirclePoints.lean`](../../Elements/Figure/CirclePoints.lean), all under
  `Elements.Tacit`. Across both waves, all 39 keep their original signatures, binder names
  included: `pasch3` keeps `hB` and `same_side_or` keeps `h`. The 31 replacements use earlier
  retired rules as proved theorems, and their theorem dependencies are acyclic. No
  replacement's axiom closure contains a retired axiom, Circle 2, Circle 3 or superposition,
  and none cites a proposition. No
  certificate entry rests on Circle 2 or Circle 3, and III.1 and its porism rest on 38
  tacit rules each. The constraints cost retirements: within the derivations found, every
  derivation of `between_symm`, `between_of_inside_chord` and `line_circle_between` rests
  on Circle 3 or none was found, and without the Circle constraint the earlier search's
  maximum, 34 in all, put Circle 3 under II.14, III.1 and III.2. The axioms leave
  `Elements/Foundations/Tacit/Constructions.lean`, `Diagram.lean`, `Metric.lean` and
  `Transfer.lean`. Protected files changed with them, as values pinned to the axioms:
  [`Certificate/axioms.lock`](../../Certificate/axioms.lock), written by `--write-lock`;
  [`tests/model/lock.sha256`](../../tests/model/lock.sha256) and `model/lock.sha256`;
  [`tests/model/laws.toml`](../../tests/model/laws.toml), and the 31 laws' code in
  [`tests/model/search.py`](../../tests/model/search.py) and
  [`tests/model/hyperbolic.py`](../../tests/model/hyperbolic.py), the other laws in their
  order and the rest of each file as it was; [`tests/model/MODEL.md`](../../tests/model/MODEL.md)
  follows the smaller lock. The results of `run.py --full --write` are recorded in
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
  [`Audit/Overlaps.lean`](../../Audit/Overlaps.lean) imports the proved rules and updates
  its pinned axiom closures and explanatory comments to follow the retirements, retaining
  every `#guard_msgs` check.
  [`model/Model/Audit.lean`](../../model/Model/Audit.lean) changes only the comment counts
  to 39 retired rules and 48 locked laws, with every individual audit, guard and axiom pin
  unchanged.
  [`tests/certificate_expectations.json`](../../tests/certificate_expectations.json) records
  the measured counts of III.1 and its porism (38 tacit rules each) and new pins that III.1,
  III.1 Por., III.2 and II.14 rest on none of the 31. The accompanying check changes must
  land separately from the content they judge, under WORKFLOW, section 10: the 31 become
  derived properties in [`tests/model/derived.py`](../../tests/model/derived.py), which
  [`tests/model/exhaustive.py`](../../tests/model/exhaustive.py) and
  [`tests/model/structured.py`](../../tests/model/structured.py) run by name, adding runs
  for the ones they did not yet sample; and, in the formal model,
  `model/Check/Generator.lean` extends `comparePlanted` to check the hand `LineMeetsCircle`'s
  type and body against the library's definition before translating it, including binder
  kinds and without unfolding. `model/Check/Intersections.lean` uses it for Intersections 2
  and 3, retaining their kernel comparisons through `original` and a guarded regression:
  making Intersection 3's point A explicit passes `rfl` but fails the structural comparison.
  All 39 retired rules have direct structural comparisons, including binder kinds.
  The formal model's generated laws, checks and assembly
  follow from its generator; its proofs in the plane stay, as derived facts, and
  `model_exists` stays unconditional. Proposition and porism statements, definitions and
  `--` lines are unchanged. The check inputs this retirement leaves stale, the law
  allow-list in `scripts/safe_push.py` (nine entries no remaining law uses, which the
  retirement leaves harmless) and the examples of `Certificate/FIELDS.md` and
  `review/SCHEMA.md`, follow in a check change of their own, landed after this one.
