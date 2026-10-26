- **The bar each question of the Jev audit must clear on its calibration, stated before
  the calibration is run (#36).** Brief 0005, stage 6, asks that Jev meet "a stated
  accuracy bar" on a seeded calibration set before its answers are trusted, and that below
  the bar its answers be "a secondary signal only". No bar was stated before the run of
  19 October 2026, and its answers are not preserved, so the audit of Books I and II could not
  call Jev calibrated ([its report](../reports/acceptance/jev/audit-books-I-II.md), "What
  this audit does not show"). On 25 October 2026 the owner chose, of the options put to
  them, (A): state the bar first, in a dated entry made before any calibration run; then
  calibrate again the questions that gate, P13 and P14 included, with planted faults; add
  Book III's questions; and run the audit again with every output committed. The owner's
  words were "yes to all three."; the coordinator's record of the choice is
  [#36](https://github.com/jackChallis/stoicheia/issues/36). This entry states the bar. It
  lands before any request of the new calibration is sent, so that the bar is seen to come
  first.

  **The questions.** Every question the audit asks gates its item, so each has a bar of its
  own: P11 (scope, ACCEPTANCE item 9), P12 (citations and hypothesis use, item 10), P13
  (representations, item 11), P14 (commentary, item 12) and P15 (figures, item 13), in the
  wording that `scripts/audit/jev_questions.py` gives them on main when the calibration is
  generated. For each question, its *clean answer* is the one a correct record earns, and
  its *defect answers* are the options that name a fault:

  | Question | Clean answer | Defect answers |
  |---|---|---|
  | P11 | fully | restricted, exactly as the note says; restricted beyond what the note says |
  | P12 | all do work | a dummy citation; an artificial hypothesis use |
  | P13 | bridge stated | bridge missing or inadequate |
  | P14 | agrees | conflicts |
  | P15 | agrees | disagrees |

  "cannot tell", and P13's "no bridge required", are neither.

  **The calibration set.** Each question has a file of its own, of 20 rows: 10 controls and
  10 planted faults, so that `jev.py score` judges each question alone.

  - *Controls* are the audit's own rows, unchanged, for propositions whose record gives the
    clean answer for that question, at stage `full`. In each book they are the eligible
    propositions whose SHA-256, in hexadecimal, of the UTF-8 text `jev-calibration`, a
    space, the question's name, a space and the reference (as `jev-calibration P11 I.7`)
    is least: four from Book I, two from Book II and four from Book III. For P12 the row
    is the main theorem's; for P13, a proposition is eligible when its record's
    representations item is `pass`.
  - *Planted faults* are copies of audit rows with one fault planted in the generated row,
    never in a file of the edition, as the controls of the audit of Books I and II were.
    Each is on a proposition that is no control of the same question; at least two of the
    ten are from each book; at least three kinds of fault are used, and no kind more than
    four times. Each row records its fault: what was changed, the row's state before and
    after, and the defect answer it expects. The kinds are:
    - P11: a hypothesis added that leaves out a configuration Euclid's words admit; a
      clause of the conclusion removed; a porism or companion removed whose clause the
      main statement does not carry; an object Euclid leaves general fixed or narrowed.
      Each expects "restricted beyond what the note says".
    - P12: a call of an unrelated proposition whose result is not used (expects "a dummy
      citation"); a call whose result is bound while the step it is for is done another
      way (expects "a dummy citation"); a hypothesis added and used only in a binding
      nothing uses (expects "an artificial hypothesis use"); an existing hypothesis
      mentioned in a step that does no work (expects "an artificial hypothesis use").
    - P13: every supplied bridge removed; an impossible premise added to each bridge; a
      bridge's conclusion changed so that it no longer connects the represented object
      with Euclid's; a premise added that the represented objects cannot meet; the one
      bridge that a needed connection rests on removed, the others kept. Each expects
      "bridge missing or inadequate".
    - P14: a comparison in the commentary reversed; the proposition that a step of the
      route cites changed to another; the scope misstated, as a case said to be covered
      that the statement leaves out; a named declaration's hypotheses or conclusion
      misstated; the kind of route misstated, as direct for a reductio. Each expects
      "conflicts".
    - P15: another proposition's figure sent; two letters of the figure exchanged; a
      caption's claim made false of the figure; a point moved so that an incidence or an
      order the proof needs fails. Each expects "disagrees". A changed figure is a copy,
      written beside the calibration set; `figures/` is not touched.

  The generator writes both lists, controls and plants, and lands before the calibration
  is run: neither is chosen after any answer is seen. A row's expected answer stays on
  this machine, as `jev.py` keeps it, and is never sent.

  **The run.** The calibration is run once, on the evidence of one commit of main, the
  commit the audit's own questions are then generated from, with `jev.py run` asking the
  pinned model `jev-1.13.0`, its order check on, so that each question is asked in both
  orders of its options. If the model listing does not offer `jev-1.13.0`, nothing is sent
  and the work stops for a ruling. Every raw output is committed under
  `docs/reports/acceptance/jev/`, with no key and no path to one, whatever it shows.

  **The bar.** A question clears its bar when all four of these hold on its file:

  1. every row is answered, by `jev-1.13.0`, and no request failed;
  2. at least 9 of the 10 planted faults are *found*: Jev chose a defect answer in both
     orders;
  3. at most 2 of the 10 controls are *false alarms*: a control on which Jev chose a
     defect answer in either order;
  4. `python3 scripts/audit/jev.py score <file> --bar 0.8` exits 0: Jev's first answer is
     the expected one on at least 16 of the 20 rows.

  Nine of ten is asked, and not eight, because Jev's agreement is to count as an
  independent confirmation of a record: a question that misses one fault in five would
  clear a bar of eight of ten two times in three, and this one little more than one time
  in three. A false alarm costs only an adjudication, since
  every answer other than a confident clean one is adjudicated, so two are allowed.

  **What clearing it means.** For a question that clears its bar, an audit answer that
  agrees with its record in both orders, with confidence 0.5 or more in both, counts as an
  independent confirmation of that item. Every other answer goes to a Claude adjudicator,
  as the brief says, whose own output is committed beside Jev's. Every P11 answer is
  adjudicated whatever its calibration shows, as in the audit of Books I and II, since
  scope answers changed with the order of the options there.

  **What missing it means.** A question under its bar is reported as under it, with its
  outputs committed; for that question Jev's answers are a secondary signal only, and the
  work stops for the owner's ruling, the brief's fallback to a cold reviewer of another
  model family being the course that ruling is asked about. The bar is not moved, and the
  question is not asked again under this entry. A question whose wording changes after its
  calibration has been run needs an entry of its own and a calibration of its own, and the
  outputs of this one stay committed.

  The fourteen rows of `docs/reports/acceptance/jev/calibration.jsonl`, sent on
  19 October 2026, are not this calibration, and no bar here judges them.
