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
    before. A span passes only in the form GitHub's renderer was found, with sample spans
    on 18 October, to show as written: the dollars paired within the paragraph, never
    `$$`; one line, no white space just inside a dollar; the opening dollar at a line's
    start or after white space or "(", the closing one before white space, a line's end or
    a punctuation mark; balanced braces; no backslash before an ASCII punctuation mark,
    which GitHub's Markdown removes; and no `<`, `>` or `&`, which it escapes twice. Before
    anything else, the script's self-check reads 26 sample mishnahs, six on the allowed
    side and twenty refused, among them TeX outside the dollars in the modern way, `$…$`
    in another paragraph, and each malformed span;
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
