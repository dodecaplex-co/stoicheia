- **An overlap's further combinations of rules, each held to the audit (#293).** Card
  #293, measurement 3a: `Audit/Overlaps.lean` proves III.5 from three combinations of our
  rules, Diagram-segment 2 with Generalities 4 (`Audit.III_5`), Definition I.15 with
  Diagram-segment 4 and a magnitude law (`Audit.III_5_crossing`), and Definition I.15
  with Diagram-segment 3's second half and Generalities 4 (`Audit.III_5_radius`), while a
  review record's `[overlap]` could carry only one, in `rule` and `also`. III.5's record
  describes all three in its note, in that order, yet the summary that CERTIFICATE.md and
  Book III's index print names the first alone. So `[overlap]` gains an optional key,
  `ways`: a list of the further combinations that contain the proposition, each a list of
  axioms named as facts.json names them, while `rule` with `also` stays the first. This
  discloses what `Audit/Overlaps.lean` already proves. It changes no statement, porism or
  definition, no published statement's scope, no rule and no lock, and no record: the
  records that add III.5's two further combinations come in a later train.

  Only an overlap of the kind `states` or `gives` may have `ways`, since a rule that
  supplies a step does not contain the proposition. Each combination is a different set of
  rules from the first and from every other, and names no rule twice; `heath.load_review`
  refuses any other. The audit file is the one source. For an overlap that states or gives
  the proposition, every combination, the first among them, must be exactly the axioms of
  a theorem in the file's section "Rules that state a proposition, give it at once, or
  supply its step" whose type is the proposition's own, as that theorem's `#guard_msgs`
  pin of `#print axioms` gives them, less Lean's own `propext`, `Classical.choice` and
  `Quot.sound`. `Audit.I_7`, the section's circular derivation of I.7 through I.7's own
  corollary, is named as proving no overlap, and is not read. The check reads the file's
  text, whose pins `lake build Audit` checks, and a fault names the record, the
  combination, and the theorems the file proves the proposition by, with their rules.

  Lean elaborates a theorem's type where the check reads it as written, so the check
  reads each theorem's full name in the namespaces Lean puts it in, wherever a command
  stands and a dotted namespace a part at a time, and refuses the whole file, naming the
  line, where its text could make a type mean other than it reads: an import outside
  `Elements`; a `variable`, `include` or `export` before the section's end; a namespace
  or declaration, a constructor among them, whose name has a part `Elements`; or a
  theorem of the section whose name the file declares twice. Main's file has none of
  these.

  The check holds soundness alone, that each combination a record names is proved there.
  Completeness, that each combination the file proves is in its record, would refuse
  main's III.5 today, and follows those records. On main, III.2 (two audit theorems with
  one combination), III.5 and III.6 pass the new check unchanged.

  Where a record has `ways`, the line under the enunciation says how many combinations
  contain the proposition and, in a few words, whether our proof rests on all, some or
  none of the rules of each. The page's Overlap row and the book's summary, which heads
  its index, its section of CERTIFICATE.md and its row of README.md, name every
  combination, the first one first, and say of each, as of a single one, which of its
  rules our proof rests on, from facts.json's `axioms`. A record with no `ways` is worded
  as before: on this change, `render.py` leaves every generated file byte for byte as it
  was. No check, test, expected value, lock or schema rule is weakened.

  The warrant is the coordinator's, 22 October: "Disclosing what is essential to the
  representation is within the owner's delegation." This entry claims no approval of the
  owner.

  This entry approves the change to `review/SCHEMA.md`, whose `[overlap]` section gains
  `ways`, says what the check reads and refuses in the audit file and how the pages word
  several combinations, and lists what the machine checks of them.

  This entry approves the change to `scripts/heath.py`: `validate_review` reads `ways`,
  and refuses it on a `step` overlap, a combination that repeats another and a rule named
  twice in one, with self-test cases that are accepted and refused.

  This entry approves the change to `scripts/check_fidelity.py`, whose review check holds
  each combination of a `states` or `gives` overlap to `Audit/Overlaps.lean`
  (`overlap_proofs`, `check_overlap_ways`), leaves out the theorems of
  `AUDIT_NOT_OVERLAPS`, refuses the file where `declared_in` finds what could make a
  theorem's type mean other than it reads, and looks for each rule of `ways` among
  facts.json's axioms, as it looked for those of `rule` and `also`.

  This entry approves the change to `scripts/render.py`, which counts the combinations of
  `ways` in the line under the enunciation, with a few words on what our proof rests on,
  and names each, with the rules our proof rests on, in the Overlap row and the book's
  summary.

  This entry approves the change to `scripts/negative_tests.py`, whose new plant,
  `unproved_way`, gives III.5's record a combination the audit does not prove, the rules
  of `Audit.III_5_crossing` without Definition I.15, which `check_fidelity.py` must
  refuse.

  This entry approves the change to `tests/test_negative_tests.py`, which puts small Lean
  texts in place of `Audit/Overlaps.lean`, never built, to test how the check reads them,
  each way such a text could mislead it among them, and tests the record the plant writes.

  This entry approves the change to `tests/test_check_style.py`, whose wording cases now
  hold the words for `ways` in the line under the enunciation, the Overlap row and the
  summary, and the ordinals the row numbers the ways by.
