- **III.4, III.8 and III.17 find the centre by III.1's construction under Heath's
  "[III. 1]", and a call that does Euclid's step by his means is no dummy citation
  (Book III, [#547](https://github.com/jackChallis/stoicheia/issues/547),
  [#381](https://github.com/jackChallis/stoicheia/issues/381)).** The owner's decision of
  26 October 2026, which the coordinator has recorded on #547, reads in full:
  "Yes - follow Euclid when possible." Those words are the owner's whole part here.
  Everything else in this entry is the coordinator's, given in the orders of the same day
  that carry the decision out, and the entry claims no further approval of the owner's.

  On 22 October the coordinator read #131 the other way, in
  [the entry that dropped five calls of III.1](2026-10-22-iii1-calls-dropped.md), which is
  history and stays as written. That reading took a call of III.1 under Heath's bracket to
  do no work whenever the proof went on to keep only the centre, since the rule
  `Tacit.exists_centre` would supply a centre as well, and so treated it as a dummy
  citation. This entry corrects that reading. A dummy citation is a call put in so that the
  Lean's citations match Heath's references. A call that obtains what Euclid's step
  obtains, by Euclid's means, is not one. III.1's construction finds the centre the way
  Euclid finds it, so its call under "[III. 1]" does the work of his step, even where the
  proof then keeps the centre alone; the centre is all that Euclid takes from III.1 in
  those places too. The rule remains for a centre that Euclid takes with no reference, as
  in III.35 to III.37.

  What this train does. Under Heath's "[III. 1]", III.4's proof now takes its centre F,
  III.8's its centre M, and III.17's its centre E from `Prop1.of_circle` (#381), which
  chooses two points of the circle, the ends of a straight line drawn through it at random,
  and runs III.1 on them. The companion's step `Prop8.partner`, and `Prop17.general` when A
  is on the circle, find their centres in that same way. Every one of these proofs keeps
  the centre and nothing else. Where a remark said that III.1 was not needed, a new remark
  says that the centre is found by III.1's construction, as Euclid finds it. No statement
  changes, nor any porism, companion, definition, axiom, lock or `--` line, and
  `Prop1.of_circle` keeps its statement. In the three review records the step at the
  centre is now a `helper` passage that names `Prop1.of_circle`. With no passage of theirs
  argued another way, III.4 and III.17 take the route `euclid`; III.8 stays `modified` for
  its last step alone, which the train before this one left as it is. The records wait
  for an independent reader's stamp.

  What follows. `Prop1.of_circle` is to be registered in `Elements/Companions.lean` as a
  companion of III.1, its statement unchanged, which gives it a certificate entry of its
  own and a place on III.1's page. III.2, which still takes its centre D from the rule
  under "[III. 1]", is then to find it by III.1's construction in the same way. Both wait
  until ship C7's train P3 ([#477](https://github.com/jackChallis/stoicheia/issues/477))
  has landed.

  By the coordinator's delegation, this train rewrites two passages of
  [FORMALIZATION](../FORMALIZATION.md) with the fewest words it can. Section 3's row for a
  circle's centre now says that proofs take the centre by III.1's construction where
  Heath's "[III. 1]" stands, and from the rule where Euclid takes one without a reference.
  Section 5's paragraph on dummy citations now adds that a call obtaining what Euclid's
  step obtains, by his means, is no dummy citation even when the proof uses less than the
  call returns.

  [Brief 0008](../briefs/0008-centre.md) is frozen. Its dated note of 22 October, and the
  22 October entry's correction of its section 4, its table and its question 8, say
  otherwise, so this entry corrects it in the five parts of
  [WORKFLOW](../WORKFLOW.md), section 2, "Correcting a frozen brief".

  - **The discrepancy.** The reading of 22 October counted the calls of III.1 under
    "[III. 1]" in III.4, III.8 and III.17 as calls that do no work, though each found the
    centre by Euclid's construction, which is the work his step does. Under the owner's
    decision such a call is no dummy citation, and these proofs take the centre so again.
  - **The current declaration.** Section 4 of the brief froze the rule "a bracket means
    III.1, none means the rule", its table taking the centres of III.2, III.4 and III.8 by
    III.1, and question 8 that of III.17 by `Prop1.of_circle`. The 22 October entry put in
    its place a centre taken from `Tacit.exists_centre` wherever a call of III.1 would do no
    work, with Heath's reference left on the page; the brief's own dated note of that day
    lists III.2, III.4, III.8 and III.17 among the proofs taking the rule's centre; and
    FORMALIZATION's row for a circle's centre agreed.
  - **The corrected declaration.** Where Heath's "[III. 1]" stands, a proof finds the
    centre by III.1's construction, through `Prop1.of_circle`; where Euclid takes a centre
    with no reference, it takes the rule's; other centres come from the geometric data, as
    before. In substance the frozen rule of section 4 holds again, with question 8 for
    III.17; its rows for III.4 and III.8 are carried out through `Prop1.of_circle`, as the
    coordinator's orders give them, and its row for III.2 waits for that proposition's
    train. The brief's dated note of 22 October is overtaken for III.4, III.8 and III.17
    from this train, and for III.2 from its own. FORMALIZATION, section 3, now gives the
    corrected declaration.
  - **The reason.** The owner's decision quoted above. FORMALIZATION, section 5, forbids a
    call made only so that the citations agree with Heath's; this call carries the step
    itself. The same section asks the Lean, where the page promises Euclid's argument, to
    follow the propositions he uses, in his order, and it now says outright that a call of
    this kind is no dummy citation.
  - **The consumers.** `Elements/BookIII/Prop04.lean`, `Elements/BookIII/Prop08.lean` and
    `Elements/BookIII/Prop17.lean`, which import III.1's file again; `review/III/04.toml`,
    `review/III/08.toml` and `review/III/17.toml`, which the change makes stale, to be
    read again by a reader who wrote none of it; Book III's introduction and the gap
    catalogue, whose sentences on the centre taken from the rule are made true with the
    least change; FORMALIZATION's two passages; the note in `Audit/Crossing.lean` on what
    the bridges rest on; and the pages, CERTIFICATE.md and GRAPH.md, which the integrator
    makes afresh, where III.1 now stands among the Lean's citations of III.4, III.8 and
    III.17 beside Heath's reference. In this train too, a dated update to the [overlap
    catalogue](../reports/overlaps.md) under III.1's corollary, and an addendum to the
    [routes report](../reports/routes-book-III.md). Left to their owners, with text
    proposed: a dated note in [brief 0004](../briefs/0004-book-III.md) under "Circles and
    their centres", and a dated note in brief 0008 that points here. For Book IV, [brief
    0012](../briefs/0012-book-IV.md) finds a centre, where a construction needs one, by
    III.1, as Euclid finds it under Heath's bracket; that plan agrees with the corrected
    declaration as it is written. [Brief 0007](../briefs/0007-stage-4b.md), also frozen,
    says that III.17's outside case takes its centre through `Prop1.of_circle`, which is
    true again, and that its case on the circle takes it through `exists_centre`, which
    this train overtakes, for that case too now finds its centre by `Prop1.of_circle`.
    Later, with III.2, its Lean file, record and page; and with the registration,
    `Elements/Companions.lean` and III.1's record and page. Since the statement of III.14
    names its centre E, its proof takes no centre at all, and this train leaves it alone.

  `Audit/Crossing.lean`, a protected path, is approved here for a change to its note on
  what the bridges rest on, and to nothing else in it: the note said that no bridge
  reached III.1, and now says that each of the seven reaches it through III.8, and that
  every axiom `Prop1.of_circle` rests on already stood in their lists. Its nine pins are
  untouched. With the change, `lake build Audit` passes, and every list is the one Lean
  printed before; none gains or loses a name, so none comes to list `Tacit.circles_meet`,
  `Tacit.circle_eq` or `Tacit.exists_centre` where it did not, nor any of the four
  names `Tacit.inside_of_between`, `Tacit.outside_of_between`, `Tacit.centre_unique`
  and `sorryAx`. `Audit/Overlaps.lean` and `Audit/Centre.lean` do not change, and their
  pins hold.
