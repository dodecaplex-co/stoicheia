- **The bar each question of the Jev audit must clear on its calibration, stated before
  the calibration is run (#36).** Brief 0005, stage 6, asks that Jev meet "a stated
  accuracy bar" on a seeded calibration set before its answers are trusted, and that below
  the bar its answers be "a secondary signal only". No accuracy bar fixed before the
  calibration of 19 October 2026 survives, and that calibration's answers are not
  preserved, so the audit of Books I and II could not call Jev calibrated
  ([its report](../reports/acceptance/jev/audit-books-I-II.md), "What this audit does not
  show"). On 25 October 2026 the owner chose, of the options put to them, (A): state the
  bar first, in a dated entry made before any calibration run; then calibrate again the
  questions that gate, P13 and P14 included, with planted faults; add Book III's
  questions; and run the audit again with every output committed. The owner's words were
  "yes to all three."; the coordinator's record of the choice is
  [#36](https://github.com/jackChallis/stoicheia/issues/36). This entry states the bar. It
  lands before any request of the new calibration is sent, so that the bar is seen to come
  first.

  **The questions.** Every question the audit asks gates its item, so each has a bar of its
  own: P11 (scope, brief 0005's item 9, which the rows carry as `item`), P12 (citations and
  hypothesis use, item 10), P13 (representations, item 11), P14 (commentary, item 12) and
  P15 (figures, item 13), in the wording that `scripts/audit/jev_questions.py` gives them
  on main when the calibration is generated. For each question, its *clean answer* is the
  one a correct record earns, and its *defect answers* are the options that name a fault:

  | Question | Clean answer | Defect answers |
  |---|---|---|
  | P11 | fully | restricted, exactly as the note says; restricted beyond what the note says |
  | P12 | all do work | a dummy citation; an artificial hypothesis use |
  | P13 | bridge stated | bridge missing or inadequate |
  | P14 | agrees | conflicts |
  | P15 | agrees | disagrees |

  "cannot tell", and P13's "no bridge required", are neither. An option renamed before the
  run needs an entry of its own, stating this table again.

  **The calibration set.** Each question has a file of its own, of 20 rows: 10 controls and
  10 planted faults, so that `jev.py score` judges each question alone. Both lists are
  fixed by rule, here, before the generator that writes them is reviewed.

  - *Order.* For each question and book, the eligible propositions are ranked by the
    SHA-256, in lower-case hexadecimal, of the UTF-8 text `jev-calibration`, a space, the
    question's name, a space and the reference, with no line feed (as
    `jev-calibration P11 I.7`), least first. A proposition is eligible when its record is
    at stage `full` and gives the question's clean answer; for P13, when its record's
    representations item is `pass`, so that no plant lands on a record marked `n/a`.
  - *Controls* are the first four eligible propositions of Book I, the first two of
    Book II and the first four of Book III. A control's row is the audit's own row,
    unchanged. For P12, a control's row and a plant's row are each the main theorem's
    row, never a companion's or a porism's.
  - *Planted faults* are on the next four of Book I, the next two of Book II and the next
    four of Book III: copies of their audit rows, with one fault planted in the generated
    row, never in a file of the edition, as the seeded rows of the audit of Books I and II
    were. Each row records its fault: its kind, what was changed, the row's state before
    and after, and the defect answer it expects.

  At the records of main on the day of this entry, the lists are these (controls; then
  plants):

  | Question | Book I | Book II | Book III |
  |---|---|---|---|
  | P11 | I.23, I.2, I.10, I.34; then I.8, I.19, I.29, I.9 | II.5, II.4; then II.9, II.8 | III.9, III.31, III.16, III.34; then III.37, III.11, III.36, III.28 |
  | P12 | I.27, I.12, I.16, I.33; then I.21, I.45, I.15, I.40 | II.14, II.1; then II.5, II.7 | III.4, III.22, III.7, III.6; then III.37, III.31, III.24, III.36 |
  | P13 | I.42, I.8, I.41, I.38; then I.37, I.46, I.43, I.36 | II.14, II.1; then II.8, II.6 | III.33, III.24, III.26, III.37; then III.28, III.27, III.36, III.29 |
  | P14 | I.37, I.43, I.4, I.21; then I.47, I.38, I.13, I.7 | II.8, II.11; then II.1, II.10 | III.31, III.22, III.29, III.28; then III.25, III.20, III.4, III.14 |
  | P15 | I.44, I.8, I.24, I.43; then I.22, I.34, I.7, I.13 | II.2, II.14; then II.5, II.10 | III.17, III.21, III.6, III.33; then III.1, III.22, III.19, III.15 |

  If the records at the calibration's commit give other lists, nothing is sent, and the
  work stops for a ruling.

  **The kinds of fault.** The ten plants of a question take its kinds in turn: the plants
  in the order of the table above, Book I's four, then Book II's two, then Book III's
  four, and the k-th plant takes the k-th kind in the question's list below, counting round
  from the first. A kind applies to a plant's row when the row passes the kind's test,
  given with the kinds below; a kind with no test always applies. When the kind due does
  not apply, the plant takes the next kind that does, counting round the list in the same
  way, and the generator records why each kind passed over did not apply; if no kind
  applies, nothing is sent and the work stops for a ruling. Within its kind, the change is
  the simplest one that makes the fault: it is written into the generator, and reviewed
  with it, before any request is sent. No change may be
  found by a surface sign, such as a hypothesis named for what it does or a word in the
  state that marks it as planted. The kinds:

  - P11: a hypothesis added that leaves out a configuration Euclid's words admit; a clause
    of the conclusion removed (its test: the main statement's conclusion has two clauses
    or more); a porism or companion removed whose clause the main statement does not
    carry (its test: the row's `attached_statements` is not empty); an object Euclid
    leaves general fixed or narrowed. Each expects "restricted beyond what the note
    says".
  - P12: a call of an unrelated proposition whose result is not used (expects "a dummy
    citation"); a call whose result is bound while the step it is for is done another way
    (expects "a dummy citation"; its test: the unit's body calls a proposition); a
    hypothesis added and used only in a binding nothing
    uses (expects "an artificial hypothesis use"); an existing hypothesis mentioned in a
    step that does no work (expects "an artificial hypothesis use").
  - P13: every supplied bridge removed; an impossible premise added to each bridge; a
    bridge's conclusion changed so that it no longer connects the represented object with
    Euclid's; a premise added that the represented objects cannot meet; the one bridge
    that a needed connection rests on removed, the others kept. The first four kinds'
    test: the row's `bridges` is not empty; the fifth's: it holds two bridges or more.
    Each expects "bridge missing or inadequate".
  - P14: a comparison in the commentary reversed; the proposition that a step of the route
    cites changed to another; the scope misstated, as a case said to be covered that the
    statement leaves out; a named declaration's hypotheses or conclusion misstated; the
    kind of route misstated, as direct for a reductio. Each test reads the commentary
    outside quotation marks, since P14 leaves quotation out: the first kind needs a
    comparison of magnitudes there; the second, a proposition named for a step; the
    third, a claim about what the statement covers; the fourth, a declaration in the row's
    `named_declarations`; the fifth, the form of the proof named. Each expects
    "conflicts".
  - P15: another proposition's figure sent; two letters of the figure exchanged; a
    caption's claim made false of the figure (its test: the caption is not empty); a point
    moved so that an incidence or an
    order the proof needs fails. Each expects "disagrees". A changed figure is a copy that
    the generator makes from the committed figure and writes beside the calibration set,
    recording both files' hashes; `figures/` is not touched.

  Before any request is sent, the generator's review confirms that each control's and each
  plant's row supplies what its record's verdict rests on: for P13, the bridges the record
  checked. A row that does not stops the work for a ruling. A row's expected answer stays
  on this machine, as `jev.py` keeps it, and is never sent.

  **The run.** The calibration is run on the evidence of one commit of main, the commit
  the audit's own questions are then generated from, with `jev.py run` asking the pinned
  model `jev-1.13.0`, its order check on, so that each question is asked in both orders of
  its options. What `jev.py preflight` prints before each file's run, and before each
  continuation, is committed with the outputs. Each file is run once: a run that ends with
  rows unanswered, for whatever cause, may be continued with `--resume` on the same input,
  model and order check, which sends only the rows not yet answered, and the output as it
  stood before each continuation is kept under a name of its own and committed too. No
  answered row is sent again. Every raw output is committed under
  `docs/reports/acceptance/jev/`, with no key and no path to one, whatever it shows.

  **The bar.** A question clears its bar when all four of these hold on the final output
  of its file's run:

  1. every row is answered, by `jev-1.13.0`, and no line of the final output records a
     failed request;
  2. at least 9 of the 10 planted faults are *found*: Jev chose a defect answer in both
     orders;
  3. at most 2 of the 10 controls are *false alarms*: a control on which Jev chose a
     defect answer in either order;
  4. `python3 scripts/audit/jev.py score <output> --bar 0.8` exits 0: Jev's first answer
     is the expected one on at least 16 of the 20 rows.

  Nine of ten is asked, and not eight, because Jev's agreement is to count as an
  independent confirmation: a question that misses one fault in five would clear a bar of
  eight of ten two times in three, and this one little more than one time in three. A
  false alarm costs only an adjudication, since every answer other than a confident clean
  one is adjudicated, so two are allowed.

  **What clearing it means.** For a question that clears its bar, an audit answer given by
  `jev-1.13.0` that agrees with its record in both orders, with confidence 0.5 or more in
  both, counts as an independent confirmation of what that question asks of the item,
  within the limits the generator's manifest lists, among them: P13 asks what the bridges state, not
  where they stand in the order of dependencies; P14 leaves out quotation, attribution and
  voice; P15 looks at Heath's figure only. Every other answer goes to a Claude adjudicator,
  as the brief says, whose own output is committed beside Jev's. Two kinds of answer are
  adjudicated whatever the calibration shows: every P11 answer, as in the audit of Books I
  and II, since scope answers changed with the order of the options there; and every P13
  answer on a record marked `n/a`, which this calibration does not test. Neither counts as
  an independent confirmation on Jev's answer alone.

  **What missing it means.** A question under its bar is reported as under it, with its
  outputs committed; for that question Jev's answers are a secondary signal only. The work
  then stops for the owner's ruling before the audit is run, the brief's fallback to a
  cold reviewer of another model family being the course that ruling is asked about; the
  audit's report says, for each item, which kind of evidence it rests on. The bar is not
  moved, and the question is not asked again under this entry. A question whose wording
  changes after its calibration has been run needs an entry of its own and a calibration
  of its own, and the outputs of this one stay committed.

  The fourteen rows of `docs/reports/acceptance/jev/calibration.jsonl`, sent on
  19 October 2026, are not this calibration, and no bar here judges them.
