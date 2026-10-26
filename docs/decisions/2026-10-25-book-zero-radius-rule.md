- **Book Zero on the radius rule: III.5 and III.6 rest on neither Diagram-segment 2 nor
  Circle 1, and no proof of Book Zero calls Diagram-segment 2 (Book Zero, #473).** On 25
  October 2026, at about 22:45 Pacific time, the owner answered "yes to all three." to
  three recommendations the coordinator had put to them. Those words are the owner's. The
  one this entry carries out further, recorded by the coordinator on #473, was to add one
  axiom, the radius rule, and then to carry out the scoping's plan: to prove again, without
  `Tacit.circle_eq`, the parts of Book Zero that use its lemma that a radius is not
  nothing, so that III.5 and III.6 no longer rest on `circle_eq`, with the overlap notes
  made true, and with no statement, porism or definition changed. The axiom came first, in
  the change that [the radius rule's entry](2026-10-25-radius-rule.md) records; this entry
  records the second step. On 26 October 2026 the coordinator added to it, from an analysis
  of the shape of the axioms, the rewriting of the one proof of Book Zero that still called
  `circle_eq`, in `Elements/Figure/Regions.lean`. No proposition's or porism's statement,
  no definition, no `--` line and no proposition's Lean changes here, and no axiom comes or
  goes: the lock keeps its 49.

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
  `circle_eq`, and no proved rule of Book Zero rests on it. The last call of it in Book Zero
  was in `Elements/Figure/Regions.lean`: `exists_inside_both`, that of two circles about
  one point one lies within the other, made the two one circle when their radii were
  equal. That case now compares lengths, as the other two cases do: a point within the
  first circle is nearer the centre than a point of that circle (`len_lt_of_inside`), so
  nearer than a point of the second circle, which is as far, and so within the second
  circle (`inside_of_len_lt`): the two directions of Diagram-segment 4, proved in
  `Elements/Figure/Incidence.lean`. The lemma keeps its name and exact type. So no proof
  in Book Zero calls `circle_eq`, and Lean's `collectAxioms` finds it beneath none of the
  1417 declarations of Book Zero's modules. In `Elements` five proofs still call it, each
  to conclude that two circles with one centre and a common point are one: Circle 4's
  (`Tacit.not_same_side_of_circles_meet`), after I.7 in `Elements/BookI/Prop07.lean`,
  which no entry uses; III.10's last step, in `Elements/BookIII/Prop10.lean`;
  `TouchesInternallyAt.between`, in `Elements/BookIII/Prop13.lean`, beneath III.13's
  companion `touchesInternally_iff`; III.25's companion `Prop25.complete`, in
  `Elements/BookIII/Prop25.lean`; and `Arc.eq_of_aligned`, in
  `Elements/BookIII/Squares.lean`, which no entry uses. Circle 1's other uses, among them
  Generalities 4 (`Tacit.inside_not_on`) and the second `ne_of_centre_of_on`, in
  `Elements/Figure/Incidence.lean`, are untouched: they are #477's.

  What it proves, read from `facts.json` after `lake build` and
  `lake env lean Certificate/Facts.lean`. III.5 rested on 21 axioms and now rests on 15:
  Definition I.15, Postulates 1 and 3, and 12 tacit rules, among them the radius rule. It
  loses `circle_eq`, Circle 1, `exists_point`, `exists_point_inside_circle`, `len_symm`,
  `line_circle_between` and `lt_trans`. III.6 rested on 21 and now rests on 19, with 16
  tacit rules: it loses `circle_eq`, Circle 1 and `exists_point`, and keeps the other four
  that III.5 loses through `centre_inside`, which ends contact without. Each gains
  `Tacit.radius_ne_zero`.
  The scoping had foreseen 16 and 19, counting the rule and Postulate 3; III.5 comes to one
  fewer, since `ne_of_centre_of_on` no longer passes through `centre_inside`.

  How many entries rest on each rule, read from two fields of each entry of `facts.json`.
  An entry rests on a rule in total when its `axioms` hold it, counting the entries it
  cites; directly when its `direct_axioms` hold it, through its own proof and the lemmas
  and proved rules beneath it, without the entries it cites or a Common Notion. The
  comparison revision, 121258a, before these Book Zero proofs changed, has 140 entries: 99
  propositions, 3 porisms and 38 companions. This revision has 149: 99 propositions, 3
  porisms and 47 companions, the nine added since being three companions of III.13, four
  of III.18 and two of III.20. So each count is given of all the entries at its revision,
  and, to compare like with like, of the 140 entries of 121258a.

  Diagram-segment 2 (`circle_eq`). At 121258a, 140 of the 140 entries rested on it in total
  (99 of 99 propositions, 3 of 3 porisms, 38 of 38 companions), and 134 of 140 directly (96
  propositions, 3 porisms, 35 companions). Now 6 of the 149 rest on it in total: 2 of the
  99 propositions, III.10, which calls it itself, and III.23, through III.10; none of the 3
  porisms; and 4 of the 47 companions, III.13's `touchesInternally_iff` and, through it,
  `circlesTouch_iff`, and III.25's `complete` and, through it, `of_circle`. 3 of the 149
  rest on it directly: III.10, `touchesInternally_iff` and `complete`, that is 1
  proposition, no porism and 2 companions. Of the 140 entries of 121258a, 4 rest on it now
  in total, III.10, III.23, `complete` and `of_circle` (2 propositions, no porism, 2
  companions), and 2 directly, III.10 and `complete` (1 proposition, 1 companion). Before
  the change to `exists_inside_both`, 15 of the 149 rested on it in total and 11 directly;
  that change takes off it the nine entries that reach the lemma, all companions: III.16's
  `acute`, `remaining` and `semicircle`, III.18's `acute`, `contact_locallyEqual`,
  `contact_lt` and `semicircle_gt`, and III.31's `greater` and `less`.

  Circle 1 (`between_of_inside_chord`). At 121258a, 140 of the 140 rested on it in total,
  and 133 of 140 directly (96 propositions, 3 porisms, 34 companions). Now 144 of the 149
  rest on it in total (94 propositions, 3 porisms, 47 companions) and 59 of 149 directly
  (34 propositions, 1 porism, 24 companions); of the 140 entries of 121258a, 135 in total
  (94 propositions, 3 porisms, 38 companions) and 52 directly (34, 1 and 17). I.1, I.2,
  I.4, III.5 and III.6 rest on it no longer. The change to `exists_inside_both` moves none
  of these counts.

  The radius rule (`radius_ne_zero`). At 121258a it was in the lock and no entry rested on
  it. Now all 149 rest on it in total (99 propositions, 3 porisms, 47 companions), and 141
  of 149 directly (96 propositions, 3 porisms, 42 companions); of the 140 entries of
  121258a, all 140 in total and 133 directly (96, 3 and 34). The eight that do not rest on
  it directly are I.19, I.23, I.25, I.40's `join`, I.45's `apart`, II.14's `apart`,
  III.13's `circlesTouch_iff` and III.25's `complete`. The change to `exists_inside_both`
  moves none of these counts either.

  What it does not prove. That the proofs of III.5 and III.6 no longer depend on
  `circle_eq` is what the certificate shows, and no more: neither entry's `axioms` in
  `facts.json` holds `Tacit.circle_eq`, nor Circle 1; their rows in `CERTIFICATE.md` count
  12 and 16 tacit rules, without either; and the pins of `Elements.BookIII.Prop5` and
  `Elements.BookIII.Prop6` in `Audit/Crossing.lean`, which `lake build Audit` checks, list
  neither. The rule itself remains in the lock, and so does its catalogued overlap with
  the two propositions: Diagram-segment 2 still gives III.5 at once, with Generalities 4,
  and III.6 with Generalities 3 and 4, as `Audit.III_5` and `Audit.III_6` show; so their
  overlaps stay catalogued and their records keep their `[overlap]` tables. The change is
  that neither proposition rests on that rule any more. The radius rule gives neither: it
  says only that a radius is something. Circle 1 stays an assumption, and 144 of the 149
  entries still rest on it; its retirement after III.2 is #477's. Nothing here is a proof
  that Diagram-segment 2 or Circle 1 is independent of the other rules.

  Pinned values that move with the proofs. In `tests/certificate_expectations.json`, the
  expectation on III.1 Por.'s axioms moves only in its `equals` list, where
  `Tacit.radius_ne_zero` stands in place of `Tacit.circle_eq`; its count of 38 tacit rules
  stands, and its `why` gains a sentence saying so. The count of 39 for III.1 stands too,
  for the same swap, and `check_fidelity.py` finds no other expectation that moves. The
  `#print axioms` pins of four audit files move with the axioms Lean now reports, and the
  prose beside them that said the proofs rest on Diagram-segment 2 is made true. The
  change to `exists_inside_both` moves no pin and no expectation: no audit lemma reaches
  it, `lake build Audit` passes with every `#guard_msgs` as it stood, and
  `check_fidelity.py` passes.

  What the change to `exists_inside_both` touches. Its consumers are `Surrounds.and` and
  `LocallyWithin.trans` in `Elements/Figure/Regions.lean`, with `LocallyEqual.trans` over
  the second; `NearVertexOpen.mono_near`, twice, and `exists_near_across`, beneath
  `near_across`, in `Elements/BookIII/MixedAngles.lean`; and `Prop16.horn_locallyEqual`,
  in `Elements/BookIII/Prop16.lean`. A walk of Lean's proof terms finds nine entries that
  reach the lemma, all companions, and they are the nine whose certificates move: III.16's
  `acute`, `remaining` and `semicircle`, III.18's `contact_locallyEqual`, `contact_lt` and
  `semicircle_gt`, and III.31's `greater` and `less`, by their own proofs, and III.18's
  `acute` through III.16's `acute`, which it cites. Each loses `Tacit.circle_eq` from its
  `axioms`, and all but III.18's `acute` from its `direct_axioms` and `inherited`; nothing
  else in `facts.json` changes but the line numbers of the later lemmas of `Regions.lean` in
  `inherited`. Their pages, and their rows in `CERTIFICATE.md`, are generated, and now
  count 39 tacit rules where they counted 40. No `PropNN.lean` changes, so no record's
  Lean stamp is stale, and `check_fidelity.py` finds none. The records of III.16, III.18
  and III.31 describe what these companions rest on, the rules beneath `near_across`,
  `Prop16.horn_lt` and the like, so they need a semantic re-read by a reader against the
  new certificate; read for this change, none of them names `circle_eq` or
  Diagram-segment 2, and no sentence in them is made false. Their commentary,
  `mishnah/III/16.md`, `mishnah/III/18.md` and `mishnah/III/31.md`, makes no claim about
  the rule.

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
  `between_symm`, `line_circle_between`, `lt_irrefl` and `lt_trans` besides; whose pins of
  I.7's, III.2's two, III.24's, III.26's,
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
  alone, and one ray's straight line seven other construction rules, not eight. Brief
  0008, `docs/briefs/0008-centre.md`, gains a dated status note, its text and earlier
  notes unchanged, since its note of 19 October 2026 says that the axioms pinned for III.5
  and III.6 in `Audit/Crossing.lean` include `circle_eq`, which they no longer do; the
  new note adds that the step of the mixed-angle prototype that its section 7 says used
  Diagram-segment 2, now the equal-radius case of `exists_inside_both`, uses it no longer.
  The pages of III.5 and III.6 (`mishnah/III/05.md`, `mishnah/III/06.md`) and Book III's
  introduction were read for the same claims and make none, so they do not change. For the
  second step, the catalogue of overlaps, the Book III brief and the audit files, changed in
  the first as above, were read again for claims that Book Zero, the mixed angles or their
  companions rest on `circle_eq`; they make none, so the second step changes none of them.
  The records of II.14, III.5 and III.6 were subsequently read in full and stamped after
  their notes changed. Book Zero has no records, and no `PropNN.lean` changes, so no record
  is stale for its Lean.
