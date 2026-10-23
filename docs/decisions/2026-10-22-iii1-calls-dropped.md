- **The five calls of III.1 that do no work are dropped, and brief 0008's rule for a
  bracket is corrected (#131).** On 22 October 2026 the coordinator decided to drop the
  calls of III.1 that stand under Heath's "[III. 1]" in III.2, III.4, III.8, III.14 and
  III.17, for none of them does any work, and a citation that does no work counts against
  the argument ([FORMALIZATION](../FORMALIZATION.md), section 5, "No dummy citations").
  The decision is the coordinator's, made within the authority that
  [WORKFLOW](../WORKFLOW.md), section 2, gives that role over the correction of a frozen
  brief; it is not the owner's approval, and this entry claims none. The analysis, with
  the table of every call of III.1 in Book III, is in the
  [routes report](../reports/routes-book-III.md), under #131, and
  [the entry on Euclid's routes in Book III](2026-10-21-routes-book-iii.md) left this
  question to #131's own train, which carries the decision out.

  [Brief 0008](../briefs/0008-centre.md) is frozen, so this entry is its correction, in
  the five parts that WORKFLOW, section 2, "Correcting a frozen brief", names.

  - **The case that fails.** Five calls of III.1 do no work. Each of the five proofs
    keeps nothing of what III.1 returns but the centre, and `Tacit.exists_centre`, the
    rule that every circle has a centre, gives one as well. In III.14 the statement
    already names the centre E, and the proof followed its call of III.1 with
    `Tacit.centre_unique` only to show that the centre found was E. In III.17 the call
    went through `Prop1.of_circle`, which chooses two points of the circle and runs III.1
    on them.
  - **The current declaration.** Brief 0008 adopted the rule "a bracket means III.1, none
    means the rule": in its section 4, before the table of the nineteen propositions; in
    that table, whose rows for III.2, III.4, III.8 and III.17 take the centre by III.1
    under "[III. 1]"; in the row of its Appendix B on III.35 to III.37, which adopts the
    rule; and in its question 8, under which III.17 takes its centre by
    `Prop1.of_circle`. FORMALIZATION, section 3, gave the same rule in its row for a
    circle's centre: "proofs cite III.1 where Heath does".
  - **The corrected declaration.** A proof takes a centre from the rule wherever a call
    of III.1 would do no work, and Heath's "[III. 1]" stays on the page as his reference,
    shown beside the Lean's citations. It now stands in FORMALIZATION, section 3, in the
    row for a circle's centre, and in [brief 0004](../briefs/0004-book-III.md), under
    "Circles and their centres", with a dated note.
  - **The reason.** FORMALIZATION, section 5, says "Never add a theorem call to make the
    Lean's dependencies match Heath's references." Brief 0008 reasons the same way of
    III.10's last step, where it declines to cite III.5 only to match Heath's bracket. A
    reference with no call has precedents in III.24's [III. 10] and I.22's [I. 20].
  - **The consumers.** The five proofs. Their review records, `review/III/02.toml`,
    `review/III/04.toml`, `review/III/08.toml`, `review/III/14.toml` and
    `review/III/17.toml`, whose Lean stamps the change makes stale, and
    `review/III/15.toml`, whose note says that III.15 rests on the rule through III.14 and
    III.2, and does now through III.2 and its corollary `Prop2.within` alone. Their
    pages, which the integrator makes afresh, with CERTIFICATE.md and GRAPH.md. The commentary that described the calls:
    the mishnah of III.2, III.14 and III.17, Book III's introduction, the gap catalogue
    and the overlap catalogue. The axiom pins downstream of III.2 and III.8 in `Audit/`.
    And [brief 0012](../briefs/0012-book-IV.md), whose plan to find a centre in Book IV by
    III.1, under Heath's bracket, falls under the corrected declaration wherever that call
    would do no work. And [brief 0007](../briefs/0007-stage-4b.md), which is frozen, and
    whose account of III.17 says that the outside case takes its centre through
    `Prop1.of_circle`: since this correction it takes it from the rule, as the on-circle
    case does.

  No statement changes: no proposition's, porism's or companion's type, no definition, no
  axiom and no lock. III.1 and `Prop1.of_circle` stay as they are; no proof in
  `Elements/` now calls either but `Prop1.of_circle`'s own call of III.1; III.9 and III.10
  still cite III.1's porism, which no longer rests on III.1.

  This entry approves the change to `Elements/BookIII/Prop02.lean`, whose proof takes the
  centre D from `Tacit.exists_centre` in place of III.1, and which no longer imports III.1's
  file.

  This entry approves the change to `Elements/BookIII/Prop04.lean`, whose proof takes the
  centre F from the rule, and which no longer imports III.1's file; the conditions that
  AC and BD are not through the centre, said of every centre, apply to it as they did.

  This entry approves the change to `Elements/BookIII/Prop08.lean`, whose proof takes the
  centre M from the rule, and which no longer imports III.1's file; the condition that M
  lies between G and A, said of every centre, applies to it as it did.

  This entry approves the change to `Elements/BookIII/Prop14.lean`, whose proof loses its
  call of III.1 and of `Tacit.centre_unique`, since its statement names E, and which no
  longer imports III.1's file.

  This entry approves the change to `Elements/BookIII/Prop17.lean`, whose proof takes the
  centre E from the rule in place of `Prop1.of_circle`, and which no longer imports
  III.1's file.

  This entry approves the change to `Audit/Crossing.lean`, a protected path: its seven
  pins of the bridges' axioms are renewed from Lean's own output, and its note on what the
  bridges rest on no longer says that they reach the rule through III.1.

  This entry approves the change to `Audit/Overlaps.lean`, a protected path: its pins of
  `Audit.III_26_any`, `Audit.III_27_any`, `Audit.III_24_measure` and
  `Audit.III_30_measure` are renewed from Lean's own output, and the note of `Audit.III_2`
  says that our III.2 takes its centre from the rule.

  Each of the eleven renewed pins still holds the whole list Lean prints, which has lost
  `Tacit.exists_point_same_side`, a rule the five proofs no longer reach through III.1,
  and gained no name. So no pin is loosened: none comes to list `Tacit.circles_meet`,
  `Tacit.circle_eq` or `Tacit.exists_centre` where it did not before, nor any of the four
  names that brief 0008's question 7, as its section 3 corrects it, forbids,
  `Tacit.inside_of_between`, `Tacit.outside_of_between`, `Tacit.centre_unique` and
  `sorryAx`. The pin of `Audit/Centre.lean` holds without change.
