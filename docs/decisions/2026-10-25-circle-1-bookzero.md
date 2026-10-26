- **Book Zero, III.1 and III.2 off Circle 1, the rule still assumed (Book Zero and Book
  III, #477).** On 25 October 2026, at about 22:45 Pacific time, the owner answered "yes to
  all three." to three recommendations the coordinator had put to them; those words are the
  owner's. The coordinator's record on #477 reads the answer as approving, with #473, the
  radius rule and the plan to retire Circle 1 (`Tacit.between_of_inside_chord`) into a
  theorem proved in `Elements/BookIII/Prop02.lean` after III.2, keeping its name and type,
  with preparation first, so that no check fails on main at any commit. This entry records
  the preparation step that takes Circle 1 out of Book Zero and out of III.1, its porism and
  III.2, while the rule is still an axiom; the retirement itself is a later change. No
  proposition's, porism's or companion's statement, no definition and no `--` line changes,
  and no axiom comes or goes: the lock keeps its 49.

  What changes in Book Zero. Every lemma keeps its name and exact type, and only proofs
  change. Generalities 4 (`Tacit.inside_not_on`, in `Elements/Figure/RuleBase.lean`) is
  proved from the circle's centre: the point is not the centre, by the radius rule, and the
  straight line from the centre through it, produced beyond it, meets the circle
  (Intersections 5), where the radius would be the radius to the point and something more.
  Generalities 2 (`Tacit.centre_unique`, in `Elements/Figure/Circles.lean`) is proved by
  producing the straight line through two supposed centres beyond each to the circle: the
  radius from one centre would be less than itself. Intersection 4
  (`Tacit.circles_meet_of_on_inside_outside`, in `Elements/Figure/Incidence.lean`) takes the
  first circle's centre from our rule that every circle has a centre (`Tacit.exists_centre`),
  for System E's rule names none, and gives it to a new lemma placed before it,
  `circles_meet_of_centre`, which takes the centre as a hypothesis and carries the proof: if
  the centre is on the second circle it is the witness, and otherwise a crossing of the
  second circle lies between that centre and a point on or within the first circle, and so
  within it. That lemma uses neither Circle 1 nor our rule. Intersection 4's former helper
  `RuleProofs.Intersections.inside_between_inside_on`, whose only caller it was, is removed;
  no other Lean file names it. The two lemmas the new proof uses, `InsideCircle.of_between_centre` and `InsideCircle.of_between_centre_of_inside`,
  move up from `Circles.lean` into `Incidence.lean` with their names and types. A new lemma,
  `between_of_centre_chord` in `Circles.lean`, is Circle 1 where the point within is the
  centre, proved from Definition I.15, Between 6 and the radius rule: either other order of
  the three points would make one radius a part of the other.
  `RuleProofs.Order.ne_of_centre_of_on`, in `Incidence.lean`, is proved by the radius rule,
  as its twin in `Circles.lean` already was. Once Generalities 4 no longer used Circle 1
  this lemma did not reach it, but it would have reached `exists_centre` through
  Generalities 4's new proof, and Diagram-segment 4 (`Tacit.len_lt_of_inside`), beneath much
  of Book I, uses it: proved through Generalities 4, it would leave 91 of the 149 entries
  newly resting on that rule, from I.3 on, all of them among the 140 of d0eb44ca, the
  comparison revision below; proved by the radius rule, and with I.22's change below, none.

  What changes in Book I. One line of a proof. `Prop22.meet`, the step of I.22 that makes its
  two circles meet, has the centre G of the first among its hypotheses, and in
  `Elements/BookI/Prop22.lean` it now calls `circles_meet_of_centre` with G where it called
  Intersection 4. No statement, docstring or `--` line of the file changes. Intersection 4
  keeps its name and type, and no proof in the library now calls it.

  What changes in Book III. III.1's four uses of Circle 1 at the centre (in `Prop1.within`,
  in its reductio, in the step that puts the centre between C and E, and in its porism's
  case of a centre on AB), III.2's use when AB passes through the centre, and
  `Aligned.centre_between` in `Elements/BookIII/Squares.lean` use `between_of_centre_chord`
  in its place. `foot_between`, whose last step is Circle 1 at the foot of a perpendicular,
  not at the centre, moves unchanged from `Squares.lean` to a new file,
  `Elements/BookIII/Feet.lean`, after III.2, which `Elements.lean`, III.14, III.15, III.35
  and III.36 import: III.1 and III.2 import `Squares.lean`, so a step that is to use the
  theorem proved after III.2 cannot stand there. It still uses the axiom. Section 6 of
  `docs/FORMALIZATION.md` names the new file among the homes of shared steps, and the Book
  III brief gains a dated note, its text unchanged.

  What it proves, read from `facts.json` after `lake build` and
  `lake env lean Certificate/Facts.lean`. III.1 rested on 44 axioms and now rests on 43, with
  38 tacit rules where it had 39; III.1's porism on 43 and now 42, with 37; III.2 on 44 and now
  43, with 38. Each loses Circle 1 and gains nothing, and none rests on Diagram-segment 2
  (`Tacit.circle_eq`). I.22 rested on 31 axioms and now rests on 30, with 26 tacit rules
  where it had 27: it loses Circle 1 and gains nothing, and rests on neither Circle 1 nor
  `exists_centre`.

  How many entries rest on a rule is read, as in
  [the entry for Book Zero on the radius rule](2026-10-25-book-zero-radius-rule.md), from
  two fields of each entry of `facts.json`: an entry rests on a rule in total when its
  `axioms` hold it, counting the entries it cites, and directly when its `direct_axioms`
  hold it, through its own proof and the lemmas and proved rules beneath it; a proof names
  the rule itself when the entry's `own_axioms` hold it. The comparison revision, d0eb44ca,
  before these proofs changed, has 140 entries: 99 propositions, 3 porisms and 38
  companions. This revision has 149: 99 propositions, 3 porisms and 47 companions, the nine
  added since being three companions of III.13, four of III.18 and two of III.20. So each
  count is given of all the entries at its revision, and, to compare like with like, of the
  140 entries of d0eb44ca; the three figures after a count are its propositions, porisms
  and companions.

  Circle 1. At d0eb44ca 135 of the 140 entries rested on it in total (94, 3, 38), 53
  directly (35, 1, 17), and 21 proofs named it themselves (14, 1, 6). Now 37 of the 149 rest
  on it in total (23, 0, 14), the first of them III.7, 23 directly (16, 0, 7), and 17 proofs
  name it (11, 0, 6); of the 140 entries of d0eb44ca, 35 in total (23, 0, 12), 22 directly
  (16, 0, 6) and 17 by name (11, 0, 6). One of these moves is not this change's: III.21's
  proof, by Euclid's argument since
  [the entry on the angle at the centre](2026-10-25-routes-iii-centre.md), neither names
  Circle 1 nor rests on it directly, though III.21 still rests on it through III.20, which
  it cites. Just before this change 144 of the 149 rested on it in total and 59
  directly, as the radius rule's entry counts, and 20 proofs named it. No entry of Books I
  and II rests on it now, proposition, porism or companion, nor do III.1 to III.6, III.9,
  III.10, III.12, III.16 to III.19 and III.25, nor the porisms of III.1 and III.16.

  What else moves. No entry rests on `exists_centre` that did not before this change: 53 of
  the 149 rest on it in total (28, 0, 25), as just before it, the first of them III.1, and
  III.1's porism is not among them. At d0eb44ca 43 of the 140 did (27, 0, 16), and of those
  140, 44 do now (28, 0, 16): the one more is III.20, whose proof takes a centre from the
  rule itself since the entry on the angle at the centre. Had I.22 kept calling
  Intersection 4, 54 would rest on the rule that do not: I.22 and the 53 entries that cite
  it, directly or not, and do not rest on the rule otherwise. Generalities 4 now takes its
  centre from the rule, so 15 entries of Book III, from III.7, five of them companions, rest
  on it directly, through their own proofs and the proved rules beneath them, where before
  they rested on it only through a proposition they cite: counted so, 46 of the 149 rest on
  it (26, 0, 20) where 31 did just before this change (16, 0, 15); at d0eb44ca 25 of the 140
  did (15, 0, 10), and of those 140, 39 do now (26, 0, 13): 13 more by this change, and
  III.20 by its own proof. 23 proofs name it themselves (15, 0, 8), as just before this
  change; at d0eb44ca 18 did (14, 0, 4), and of those 140, 19 do now (15, 0, 4), III.20
  again the one more.

  No proof of Intersection 4 that uses neither Circle 1 nor a centre can be had. The review
  of this change argued it informally, in the manner of `tests/model/MODEL.md`; the argument
  is not a proof checked in Lean. Add to the plane, with its circles, one circle more, γ,
  with no centre, whose circumference is two circles far apart that do not meet and whose
  interior is their two open discs. The laws that speak of a centre (Definition I.15,
  `circle_eq`, the radius rule, Intersections 8) never apply to γ; superposition speaks of
  no circle; a point within (Points 8) and the crossings of a straight line (Intersections 4
  and 5) are found on γ disc by disc; and Intersection 5 holds between γ and any circle, γ
  itself included, with two crossings each time. Circle 1 and `exists_centre` fail for γ,
  and so does Intersection 4: take γ for the first circle and for the second an ordinary
  circle about γ's first disc that misses its second, A on the first disc's circumference and
  B within the second disc; the second circle meets neither of γ's circumferences. So a
  proof of Intersection 4 needs Circle 1 or a centre, and System E's rule gives it none. The
  scoping found that the general step the old proof took from Circle 1, that a point between
  a point within a circle and a point on it is within, is the disc's convexity, which the
  library first has from III.2.

  What it does not prove. Circle 1 stays an assumption: III.7 and the later propositions
  of Book III that use it, and `foot_between`, still call it, and 37 of the 149 entries
  rest on it. Its retirement after III.2 is the next step of #477's plan.

  Pinned values that move with the proofs, each read from the run named above.

  This entry approves the change to `tests/certificate_expectations.json`: the expectation
  on III.1 Por.'s axioms loses `Tacit.between_of_inside_chord` from its `equals` list and
  has 37 for its count of tacit rules where it had 38; the expectation on III.1's axioms
  counts 38 where it counted 39; the `why` of each says what moved and why; and one new
  expectation pins that III.2's axioms exclude Circle 1, with a `why` naming the state it
  holds, the rule still an axiom. Nothing else in the file changes.

  The pin of `Audit/Centre.lean`, on III.1's construction, loses Circle 1 and nothing else,
  and its prose stays true, so this entry approves that file with the one pin regenerated.

  In `Audit/Crossing.lean` two bridge pins, `III_6_today` and `within_point`, lose Circle 1,
  as Lean now reports; the pins of III.5 and III.6, and the other bridges', do not move.
  This entry approves the file so changed.

  For `Audit/Overlaps.lean` this entry approves ten regenerated pins: those of `I_7`,
  `III_2`, `III_2_outside`, `adjacent_eq_of_right`, `inside_of_between` and
  `outside_of_between` lose Circle 1; `III_5_crossing` loses it with `exists_point`,
  `exists_point_inside_circle`, `len_symm`, `line_circle_between` and `lt_trans`;
  `III_5_radius` loses it with `exists_point` and gains `exists_centre`; `III_6` loses the
  same two and gains `exists_centre` and `between_symm`; and `III_5` loses the same two and
  gains Definition I.15, Postulate 3, the radius rule, `exists_centre` and nine rules of
  magnitude, length and order, all through Generalities 4's new proof. Its prose stays true.

  `Audit/Superposition.lean` is approved with three pins regenerated, of I.8, of I.8's
  adapter of I.7 and of `Cited.holds_all`, each without Circle 1; the four laws' pins do not
  move, and since Circle 1 is no construction rule, no law's construction rules change.

  The companions are sentences this change makes false, changed with it: in
  `docs/FORMALIZATION.md`, the rows of Generalities 2 and 4 and of Intersection 4 among the
  rules now proved, and section 6; in the catalogue of overlaps, `docs/reports/overlaps.md`,
  a dated paragraph and the former-overlap rows of Generalities 2, 3 and Diagram-segment 3's
  half, which said those proofs or their audit lemmas rest on Circle 1 or `exists_point`, or
  gave the porism's counts as 38 and 39; in `docs/reports/gaps-book-I.md`, the notes on
  I.22's Intersection 4 and I.31's Points 3; in `docs/reports/gaps-book-III.md`, the account
  of Generalities 2, the note on III.1's centre between C and E, and the account of the
  shared steps, which put `foot_between` in `Squares.lean`; the same account in Book III's
  introduction, `mishnah/intro/III.md`; the note in `review/III/01.toml` on that step; the
  note in `review/III/02.toml` on AB through the centre; the note in `review/I/22.toml` on
  Intersection 4; the notes in `review/I/11.toml` and `review/I/31.toml` that Points 3 used
  Circle 1; and the module note of `RuleBase.lean`, whose proofs use no circle chord now. The
  records of I.11, I.22, I.31, III.1 and III.2 are stale for their text, and those of I.22,
  III.1, III.2, III.14, III.15, III.35 and III.36 for their Lean, until a reader of the other
  family reads and stamps them.
