- **What the field guide, the review schema, one message and the certificate's
  expectations say of Circle 3, made true after its retirement (tooling,
  [#428](https://github.com/jackChallis/stoicheia/issues/428)).** The coordinator's orders
  of 24 October 2026 assign card #428, which blocks the release: since Circle 3
  (`Tacit.outside_of_between`) became a theorem, proved after III.2
  ([its retirement](2026-10-24-circle-3-retired.md)), several sentences written while it
  was an axiom are no longer true, and some of the certificate's expectations that name it
  can no longer fail, though their reasons read as if they could. The retirement left its
  examples in the field guide and the review schema to a separate change; this is that
  change, with those expectations and the rewraps its last review asked for. No Lean file,
  lock, statement, definition or `--` line changes, and `facts.json` is as it was.

  The guide to `facts.json` said, in its row for `own_axioms`, that III.2 has 11 of its
  own and that Circle 2 is proved from Circle 3 in `Elements/Figure/Circles.lean`. At
  commit 95b7491, `facts.json` lists 12 for III.2, and the row now gives that number, at
  that commit, as its row for `axiom_types` gives 87 at another. It is plain text, not a
  count marker: `scripts/generated_counts.py` offers no count of one entry's field, and
  adding one would be a change to the checks beyond this card. The row now says too that
  Circle 2 and Circle 3 are both theorems, proved since 24 October after III.2 in
  `Elements/BookIII/Prop02.lean` from `Prop2.within`, so that neither is in any entry's
  `axioms` and a proof using either cites III.2. The guide's other sentences on the
  circle rules stay true, and its one count marker, the vocabulary's, stands unchanged.

  The review schema's example of an `[overlap]` table's `rule` named Circle 3, which an
  overlap may not name now, since `check_fidelity.py` asks that its rule be an axiom of
  `facts.json`. It now names `Tacit.circle_eq`, Diagram-segment 2, which is in the lock
  and which the overlap tables of III.5 and III.6 name. Its bullet for the kind `gives`
  listed III.2 from Circle 3 among its present examples; III.2's record has had no
  overlap since the retirement, so that example is now history, as the bullet for
  `states` already makes Circle 2's, while III.5's and III.6's stay as their records give
  them. The vocabulary of terms names neither rule, and the retirement made nothing in it
  false.

  The reader of review records gives, when an overlap's `rule` or `also` holds
  whitespace, an example of a name as facts.json writes it; that example was Circle 3,
  and is now `Tacit.circle_eq`, the same as the schema's. Only the string changes. No test
  reads that message.

  Ten of the expectations name Circle 2 or Circle 3. Every one stays, with every name it
  lists. Two, on III.2's `own_axioms` and `inherited`, exclude Circle 2, a theorem since
  19 October, and their reasons leaned on a third, on III.2's `axioms`, whose exclusion
  of Circle 3 could fail only while Circle 3 was an axiom. The three reasons now say what
  each pin once checked, that it cannot fail since both rules are theorems, and what holds
  III.2 off them now, which is Lean: a proof of III.2 cannot use a theorem proved from
  III.2. The one on III.2's `axioms` also no longer says that III.2 cites III.1, which
  it has not done since III.1's call was dropped; it cites I.5, I.16 and I.19. The pins
  on III.1's and II.14's `axioms` now say the same, and each gains a new expectation,
  of its own, that can fail: that the entry's `cites` excludes III.2. A proof of III.1
  or II.14 that used Circle 2, Circle 3, Points 9 or Intersection 2 would cite III.2,
  since the walk that finds an entry's citations in `Certificate/Facts.lean` goes on
  through every declaration of the project that it meets, but the entries and the Common
  Notions, as the four rules' `proved_rule_cites` and the pin on II.1's citing I.13
  show; and Lean would admit such a proof, since `Elements/BookIII/Prop02.lean` imports
  neither `Elements/BookIII/Prop01.lean` nor `Elements/BookII/Prop14.lean`, directly or
  through another file. In two scratch copies of `facts.json`, III.2 added to III.1's
  citations and then to II.14's, `check_fidelity.py --facts` failed each time on the new
  expectation, naming the entry, beside its refusal of a later citation; on an unchanged
  copy it passed. The pin on the top-level `construction_rules` now says that two of the
  rules it excludes are theorems, Tacit.pasch3 since the second wave and Circle 3 since
  24 October, so that excluding them cannot fail. The four pins listing the eight names
  retired on 19 October keep their reasons, which were true and stay so.

  Three paragraphs of the catalogue of overlaps and one of section 7 of the formalization
  guide, left with ragged lines by the retirement, are wrapped again within 90 columns,
  the width of their neighbours; `git diff --word-diff` shows no word changed.

  This entry approves the change to `Certificate/FIELDS.md`, whose `own_axioms` row now
  gives III.2's count of 12 and says where the two circle rules are proved.

  This entry approves the change to `review/SCHEMA.md`, where the `rule` example is now
  `Tacit.circle_eq` and III.2 from Circle 3 is history in the `gives` bullet.

  This entry approves the change to `scripts/heath.py`, one example in one message of its
  `[overlap]` check, nothing else in the file altered.

  This entry approves the change to `tests/certificate_expectations.json`, where six
  reasons are restated, two expectations on citations are added, and no expectation or
  listed name is removed.
