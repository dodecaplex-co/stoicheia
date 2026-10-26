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
  is seen only in its own file, as Lean sees it; five names of Lean's own library that the
  rows now quote (`And.intro`, `Iff.rfl`, `List.mem_map`, `List.map_congr_left`,
  `List.Pairwise.sublist`) are known by their whole names, as are the constructor `X.mk`
  and its lemma `X.mk.injEq` of a structure or class `X` that the generator has read, and
  any other name ending as these do is still reported unresolved; and Heath's one em dash,
  in III.16, is written as its JSON escape, so that no output holds the character while the
  decoded text stays Heath's. A record whose representations item is `pass` now gets the
  definitions and bridges its connection rests on, and one marked `n/a` none; a guard
  refuses a row that leaves out a declaration its record's representation note names, or
  one the generator's tables say the record checked. For Book III these are the bridges
  that tie each represented object to Euclid's: circles touching one another, read of the
  whole circles and proved the same as Definition III.3 read at the point of contact
  (III.13, whose words of touching at a point the generator now reads from the foundations),
  the segment given by its circle, base and a point on its side (III.21), the measure of a circumference by the angle standing on it and its congruence, the kind of a
  segment against two right angles, the angle with a circumference read as a region near its
  vertex (for III.18 also that every straight line from the point of contact into the
  circle names the same angle of contact near that point), the foot of a perpendicular, and
  Book II's `rect` and `sq` for III.35 to III.37.
  I.4's and I.8's rows now supply what their records say they checked: the meanings of the
  rule of superposition's symbols and their bridges, the cited laws, their meanings, and the
  statements of the theorems that establish them, and for I.8 `SameSideOf.of_line`. I.45's and II.14's rows supply the outline of a
  figure, its region and area, and the bridges by which their records connect a figure
  divided into pieces with its area. A later book's bridge never serves an earlier book.

  **I.40's control.** A commentary control planted its fault at a sentence of I.40's
  commentary that a read-through removed on 21 October (7d4e6866c), so the generator
  refused at main, saying the anchor was not unique when it occurred no times
  ([#350](https://github.com/jackChallis/stoicheia/issues/350)). The control's anchor is now
  a sentence present both at main and at the evidence commit of the audit of Books I and
  II, and the control still reverses a claim the commentary makes; the refusal now says how
  many times the anchor occurs.

  **The calibration set.** `--calibration` writes the set that
  [the bar's entry](2026-10-25-jev-calibration-bar.md) specifies, with
  [the rulings entry](2026-10-26-jev-calibration-rulings.md) beside it, which governs where
  the two differ: for each of P11 to P15 a file of 20 rows, 10 controls and 10 planted
  faults, on the propositions the entry's hash rule gives at the commit named, with a
  manifest. The generator holds the entry's table of lists, with P13's list for Book III as
  the rulings entry restates it, and writes nothing if the records give other lists. Each
  plant takes the kind the entry's rule gives it, P12's counting round the three kinds the
  rulings entry keeps, by the kind's test run on the generated row, save a kind that
  [the kind ruling](2026-10-26-jev-kind-not-applying.md) names in the generator's table as
  making no genuine fault on its base; the manifest records the kinds passed over and why,
  naming that ruling where it is the reason, the change, the row's whole state before it with
  its hash, the hash of the state after it (the row itself, in its questions file), and why
  the change is the expected defect. Nothing in what a row sends names its role. A P15
  plant that changes a figure sends a copy written beside the calibration set, never a
  change to `figures/`; since `docs/` holds no SVG, the copy is not committed as a file, and
  the manifest carries its exact text and hash instead, from which `--restore-figures`
  writes it again. `--tally` reads one calibration file and the output `jev.py run` wrote
  for it. It checks that the questions file has the shape the entry fixes: 20 rows of one
  question, 10 controls and 10 plants, on the entry's lists as the rulings entry restates
  them, with labels and expected
  answers that fit each row's role. It does not itself prove that the rows are the ones the
  generator wrote: that is what `--check` and the manifest's hashes show. It refuses an
  output any line of which is not consistent with that file as `jev.py run` writes it: made
  from other questions, without the order check, with a request other than the one the row
  builds, or with an `agrees` that does not follow from its choice; an unsuccessful request
  counts as a failed one. It prints each row's finding, and exits 0 only when the entry's
  four conditions hold, the fourth judged by `jev.py score --bar 0.8` itself.

  This entry approves, in `scripts/audit/jev_questions.py`, the changes above: the three
  books, the bundles and their guards, the Lean it reads, I.40's control, the escape, and
  the modes `--calibration`, `--restore-figures`, `--tally` and `--manifest`.

  This entry approves, in `tests/test_jev_questions.py`, the cases for those changes. The
  case that generates the controls at the evidence commit of the audit of Books I and II,
  and at the head, now reads that commit with its own two books, since it holds none of
  Book III's words; its expectations there are unchanged.
