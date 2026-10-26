- **The Jev audit's question generator asks of Book III too, writes the calibration set the
  bar fixes, and judges a calibration against it (#36).** On 25 October 2026 the owner chose,
  of the options put to them, (A) for
  [#36](https://github.com/jackChallis/stoicheia/issues/36): state the bar first, calibrate
  the gating questions again with planted faults, add Book III's questions, and run the
  audit again with every output committed; the owner's words were "yes to all three.", and
  #36 is the coordinator's record of the choice. The bar is stated in
  [its own entry](2026-10-25-jev-calibration-bar.md), which lands before this one. This
  entry records the changes to the generator that the second and third steps need. It
  sends nothing: the generator reads no key and makes no request, and no calibration or
  audit output is committed here.

  **Book III.** `scripts/audit/jev_questions.py` covered Books I and II only. It now asks
  P11 to P15 of all 99 records of Books I to III, which are at the stage `full`, and writes
  them to `audit-books-I-III.jsonl` and its manifest under `docs/reports/acceptance/jev/`;
  the files of the audit of Books I and II stay as they are, as the evidence of that audit,
  and the generator refuses to write over them. For that it learned four things of the
  Lean it reads: a `class` is a declaration, as a `structure` is; a `private` declaration
  is seen only in its own file, as Lean sees it; five core names that Book III's proofs
  use (`intro`, `rfl`, `mem_map`, `mk`, `injEq`) are fields of Lean's own types; and
  Heath's one em dash, in III.16, is written as its JSON escape, so that no output holds
  the character while the decoded text stays Heath's. A record whose representations item
  is `pass` now gets the definitions and bridges its connection rests on, and one marked
  `n/a` none. For Book III these are the bridges that tie each represented object to
  Euclid's: the segment given by its circle, base and a point on its side (III.21), the
  measure of a circumference by the angle standing on it and its congruence, the kind of a
  segment against two right angles, the angle with a circumference read as a region near its
  vertex, the foot of a perpendicular, and Book II's `rect` and `sq` for III.35 to III.37.
  I.4's and I.8's rows now supply what their records say they checked, the meanings of the
  rule of superposition's symbols and their bridges. A later book's bridge never serves an
  earlier book.

  **I.40's control.** A commentary control planted its fault at a sentence of I.40's
  commentary that a read-through removed on 21 October (7d4e6866c), so the generator
  refused at main, saying the anchor was not unique when it occurred no times
  ([#350](https://github.com/jackChallis/stoicheia/issues/350)). The control's anchor is now
  a sentence present both at main and at the evidence commit of the audit of Books I and
  II, and the control still reverses a claim the commentary makes; the refusal now says how
  many times the anchor occurs.

  **The calibration set.** `--calibration` writes the set that
  [the bar's entry](2026-10-25-jev-calibration-bar.md) specifies: for each of P11 to P15 a
  file of 20 rows, 10 controls and 10 planted faults, on the propositions the entry's hash
  rule gives at the commit named, with a manifest. The generator holds the entry's table of
  lists and writes nothing if the records give other lists. Each plant takes the kind the
  entry's rule gives it, by the kind's test run on the generated row, and the manifest
  records the kinds passed over and why, the change, the row's state before and after, and
  why the change is the expected defect. Nothing in what a row sends names its role. A P15
  plant that changes a figure sends a copy written beside the calibration set, never a
  change to `figures/`; since `docs/` holds no SVG, the copy is not committed as a file, and
  the manifest carries its exact text and hash instead, from which `--restore-figures`
  writes it again. `--tally` reads one calibration file and the output `jev.py run` wrote
  for it, refuses an output made from other questions or without the order check, prints
  each row's finding, and exits 0 only when the entry's four conditions hold.

  This entry approves, in `scripts/audit/jev_questions.py`, the changes above: the three
  books, the bundles and their guards, the Lean it reads, I.40's control, the escape, and
  the modes `--calibration`, `--restore-figures`, `--tally` and `--manifest`.

  This entry approves, in `tests/test_jev_questions.py`, the cases for those changes. The
  case that generates the controls at the evidence commit of the audit of Books I and II,
  and at the head, now reads that commit with its own two books, since it holds none of
  Book III's words; its expectations there are unchanged.
