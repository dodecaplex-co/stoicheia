- **Book Zero on the radius rule: III.5 and III.6 rest on neither Diagram-segment 2 nor
  Circle 1 (Book Zero, #473).** On 25 October 2026, at about 22:45 Pacific time, the owner
  answered "yes to all three." to three recommendations the coordinator had put to them.
  Those words are the owner's. The one this entry carries out further, recorded by the
  coordinator on #473, was to add one axiom, the radius rule, and then to carry out the
  scoping's plan: to prove again, without `Tacit.circle_eq`, the parts of Book Zero that
  use its lemma that a radius is not nothing, so that III.5 and III.6 no longer rest on
  `circle_eq`, with the overlap notes made true, and with no statement, porism or
  definition changed. The axiom came first, in the change that
  [the radius rule's entry](2026-10-25-radius-rule.md) records; this entry records the
  second step. No proposition's or porism's statement, no definition, no `--` line and no
  proposition's Lean changes here, and no axiom comes or goes: the lock keeps its 49.

  What changes in Book Zero. Every lemma keeps its name and exact type; only proofs change.
  In `Elements/Figure/RuleBase.lean`,
  `RuleProofs.Circle.radius_ne_zero` is now the rule itself, `Tacit.radius_ne_zero`, where
  it was proved by Circle 1 (`Tacit.between_of_inside_chord`) and, through
  `RuleProofs.Circle.on_circle_of_len_eq_of_ne`, by Diagram-segment 2.
  `RuleProofs.Circle.right_eq_zero_of_add_eq_zero` is retained unchanged.
  `RuleProofs.Circle.on_circle_of_len_eq_of_ne` retains its name and type below
  `Tacit.on_circle_of_len_eq`, and its new proof delegates to that theorem; no other Lean
  file names either helper. `RuleProofs.Circle.length_pos` keeps its proof, over the lemma.
  Diagram-segment 3's half, `Tacit.on_circle_of_len_eq`,
  moves below Generalities 3 (`Tacit.centre_inside`), which its new proof uses: the centre
  is excluded by the rule; a point within would be nearer the centre than the place where
  the straight line from the centre through it, produced, meets the circle (Intersections
  5), and a point without farther than the place where that line leaves the circle
  (Intersections 4). That is the scoping's proof from Metric 1, with the lengths taken from
  the rule. Metric 1, `Tacit.eq_of_len_eq_zero`, is proved from the rule by Postulate 3: a
  circle drawn about one end through the other has the straight line for a radius. In
  `Elements/Figure/Circles.lean`, `ne_of_centre_of_on` is proved by the rule, where it was
  proved by Generalities 3 and 4. So no proof in `RuleBase.lean` or `Circles.lean` uses
  `circle_eq`, and no proved rule of Book Zero rests on it. In Book Zero only
  `exists_inside_both`, in `Elements/Figure/Regions.lean`, still calls it, for the
  companions of III.16 and III.31. Circle 1's other uses, among them Generalities 4
  (`Tacit.inside_not_on`) and the second `ne_of_centre_of_on`, in
  `Elements/Figure/Incidence.lean`, are untouched: they are #477's.

  What it proves, read from `facts.json` after `lake build` and
  `lake env lean Certificate/Facts.lean`. III.5 rested on 21 axioms and now rests on 15:
  Definition I.15, Postulates 1 and 3, and 12 tacit rules, among them the radius rule. It
  loses `circle_eq`, Circle 1, `exists_point`, `exists_point_inside_circle`, `len_symm`,
  `line_circle_between` and `lt_trans`. III.6 rested on 21 and now rests on 19, with 16
  tacit rules: it loses `circle_eq`, Circle 1 and `exists_point`, and keeps the other four
  that III.5 loses through `centre_inside`, which ends contact without. Each gains `Tacit.radius_ne_zero`.
  The scoping had foreseen 16 and 19, counting the rule and Postulate 3; III.5 comes to one
  fewer, since `ne_of_centre_of_on` no longer passes through `centre_inside`. At the
  140-entry comparison revision 121258a, before these Book Zero proofs changed, all 140
  certificate entries rested on `circle_eq`; 134 did so through an entry's own proof and
  the proved rules beneath it, without the propositions it cites. Of the 147 entries at
  this revision, 15 rest on it: III.10, which calls it itself; III.23, through III.10; the
  companions `circlesTouch_iff` and `touchesInternally_iff` of III.13; the three
  companions of III.16; the companions `acute`, `contact_locallyEqual`, `contact_lt` and
  `semicircle_gt` of III.18; the companions `complete` and `of_circle` of III.25; and the
  two companions of III.31. Counting only an entry's own proof and the proved rules
  beneath it, without the propositions it cites, 11 now do. At the same 140-entry
  comparison revision, all 140 rested on Circle 1, 133 by an entry's own proof; now 142
  of 147 do, 58 by an entry's own proof. I.1, I.2, I.4, III.5 and III.6 rest on it no
  longer. All 147 rest on the radius rule, 139 by their own proofs.

  What it does not prove. Diagram-segment 2 still gives III.5 at once, with Generalities 4,
  and III.6 with Generalities 3 and 4, as `Audit.III_5` and `Audit.III_6` show; so their
  overlaps stay catalogued and their records keep their `[overlap]` tables. The change is
  that neither proposition rests on that rule any more. The radius rule gives neither: it
  says only that a radius is something. Circle 1 stays an assumption, and 142 entries
  still rest on it; its retirement after III.2 is #477's. Nothing here is a proof that
  Diagram-segment 2 or Circle 1 is independent of the other rules.

  Pinned values that move with the proofs. In `tests/certificate_expectations.json`, the
  expectation on III.1 Por.'s axioms moves only in its `equals` list, where
  `Tacit.radius_ne_zero` stands in place of `Tacit.circle_eq`; its count of 38 tacit rules
  stands, and its `why` gains a sentence saying so. The count of 39 for III.1 stands too,
  for the same swap, and `check_fidelity.py` finds no other expectation that moves. The
  `#print axioms` pins of four audit files move with the axioms Lean now reports, and the
  prose beside them that said the proofs rest on Diagram-segment 2 is made true.

  This entry approves the change to `tests/certificate_expectations.json`, the III.1 Por.
  expectation's `equals` list and `why`, and nothing else in the file.

  This entry approves the change to `Audit/Centre.lean`, whose one pin, on III.1's
  construction, has the radius rule in place of `circle_eq`.

  This entry approves the change to `Audit/Crossing.lean`, whose pins of III.5 and III.6
  lose `circle_eq`, Circle 1 and `exists_point`, III.5's four more, and gain the radius
  rule; whose seven bridge pins gain the radius rule and keep `circle_eq`, which
  `cut_point` calls itself and `within_point` reaches through III.10; and whose two
  paragraphs on what the proofs rest on now say that III.5 and III.6 rest on neither rule,
  and that Postulate 3 enters through Metric 1 and, for III.6, through
  `RuleProofs.Circle.length_pos` beneath `centre_inside`.

  This entry approves the change to `Audit/Overlaps.lean`, whose pins of `III_5_crossing`
  and `III_5_radius` lose `circle_eq` and gain the radius rule, `III_5_radius` with
  `between_symm`, `line_circle_between`, `lt_irrefl` and `lt_trans` besides; whose pins of I.7's, III.2's two, III.24's, III.26's,
  III.27's, III.30's, Diagram-angle 3's and Circle 2's and Circle 3's derivations have the
  rule beside or in place of `circle_eq`; whose pin of `III_6` gains the rule; whose pin
  of `III_5` does not move; and whose module text and four docstrings now say which of
  these proofs rest on Diagram-segment 2, `III_5`'s that Book Zero's lemmas beneath our
  III.5 rest on the radius rule, which gives neither III.5 nor III.6.

  This entry approves the change to `Audit/Superposition.lean`, whose pins of I.4, I.8,
  `onLine_of_angle_eq_named`, I.8's adapter of I.7, `Cited.holds_all` and the four laws
  `holds_neOfLen`, `holds_rayUnique`, `holds_rayOfAngle` and `holds_rayOfAngleSide` have
  the rule beside or in place of `circle_eq` and Circle 1, the first two laws with
  Postulate 3 as their only construction rule now; and whose module text says so of the
  four laws.

  The companions are sentences this change makes false, changed with it: the `[overlap]`
  notes of `review/III/05.toml` and `review/III/06.toml`, which said each proof rests on
  Diagram-segment 2 all the same; the note on Diagram-segment 3's half in
  `review/II/14.toml`, which said it is proved from Postulate 3 and `circle_eq`; in the
  catalogue of overlaps, `docs/reports/overlaps.md`, the current rows' "First enters", the
  paragraph beneath them, the notes on III.5 and III.6, three rows of the former overlaps,
  the paragraph on the two short audit proofs of III.5, with a dated paragraph at its head,
  and the paragraph on small certificates, which gave III.5 and III.6 18 tacit rules each;
  the rows of Diagram-segment 3's half and Metric 1 in section 7 of
  `docs/FORMALIZATION.md`; in `docs/reports/gaps-book-III.md`, the account of
  Generalities 3 and the notes on III.8, III.27 and III.33, which said Diagram-segment 3's
  half is proved from Postulate 3 and `circle_eq`; the paragraph of III.27's page,
  `mishnah/III/27.md`, on where K falls, which gave that rule's old proof; and the row for
  `Audit/` in `README.md`. The Book III brief, `docs/briefs/0004-book-III.md`, gains a dated
  note, its text unchanged, that the radius rule is a second rule of ours and that III.5
  and III.6 rest on it. Brief 0009, `docs/briefs/0009-superposition.md`, gains a dated
  note after its table of what the laws' proofs draw, its table unchanged, giving what
  three of its cells now read: distinct ends and one point at one distance use Postulate 3
  alone, and one ray's straight line seven other construction rules, not eight. The pages
  of III.5 and III.6 (`mishnah/III/05.md`, `mishnah/III/06.md`) and Book III's
  introduction were read for the same claims and make none, so they do not change. The
  records of II.14, III.5 and III.6 are stale for their text until a reader of the other
  family reads and stamps them; Book Zero has no records, and no `PropNN.lean` changes, so
  no record is stale for its Lean.
