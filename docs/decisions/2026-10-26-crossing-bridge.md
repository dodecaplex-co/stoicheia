- **The crossing bridge moves into `Elements`, and III.10 ends by III.5 (Book III,
  [#475](https://github.com/jackChallis/stoicheia/issues/475),
  [#547](https://github.com/jackChallis/stoicheia/issues/547)).** On 26 October 2026 the
  owner decided, as the coordinator records on #547, which asks among other things that
  III.10's last step cite III.5: "Yes - follow Euclid when possible." That decision is the
  owner's whole part in this entry, which claims no other approval of the owner's. The coordinator's orders
  of the same day carry it out: first #475, the bridge from two circles meeting at two
  points to circles that cut, proved in `Elements` after III.8 beside the other words of
  Definition III.3, with `Audit/Crossing.lean` checking it against the moved theorem; then
  III.10's last step by III.5.

  The bridge, `CirclesCut.of_meet`, and its step `CirclesCut.cut_point` were proved in
  `Audit/Crossing.lean` as `Audit.CirclesCut.of_meet` and `Audit.cut_point`. They are now
  `Elements.CirclesCut.of_meet` and `Elements.CirclesCut.cut_point`, in a module of their
  own, `Elements/BookIII/Cutting.lean`, which imports III.2, III.7 and III.8 and is
  imported by the root right after III.8 and by III.10. Their statements and proofs are
  unchanged, and Lean prints both statements, in full, exactly as before, the names aside.
  No statement of a proposition, porism or companion changes, nor any definition, axiom,
  lock or `--` line.

  III.10 now ends by `Prop5`, applied to what `CirclesCut.of_meet` gives: the two circles,
  different by the reductio's supposition and meeting at B and G, cut one another, and
  III.5 forbids their one centre P. Its record's route becomes `euclid`, its last passage
  a `helper` naming the bridge. `Tacit.circle_eq` leaves III.10's own Lean and stays beneath it,
  through the bridge, which tells the two centres apart by it. III.10's `own_axioms` still
  exclude `Tacit.line_circle_beyond`.

  Brief 0008 is frozen, and its section 7, under III.10, says that the restated III.5
  cannot serve there and that III.10 no longer imports or cites III.5; this entry is its
  correction, in the five parts of WORKFLOW, section 2.

  - **The discrepancy.** The section declined III.5 because III.10 is stated for circles
    that cut or only meet, and gives them only common points, while the restated III.5
    asks that they cross. The bridge shows that two different circles meeting at two
    points do cross, so III.5 serves.
  - **The current declaration.** III.10's last line applies `circle_eq` to the common
    centre P and the common point B; its route is `modified`, with a `different` passage
    at "therefore the two circles ABC, DEF which cut one another".
  - **The proposed declaration.** III.10 imports III.5 and the bridge's module and ends by
    III.5 through `CirclesCut.of_meet`; the passage is a `helper` naming the bridge, and the
    route is Euclid's.
  - **The reason.** The owner's decision recorded on #547, above. The call of III.5 does the work of
    the last step, so it is no dummy citation under FORMALIZATION, section 5.
  - **The consumers.** `Elements/BookIII/Prop10.lean`; `review/III/10.toml`, which the
    change makes stale, for an independent reader of the other family to read again;
    `mishnah/III/10.md`, Book III's introduction and the III.10 entry of the gap
    catalogue; the pages, certificate and graph, which the integrator makes afresh;
    `Audit/Crossing.lean`; and the sentences that place the bridge in `Audit/`: the row on
    circles cutting in FORMALIZATION, section 3, the overlap catalogue under III.5, the
    III.5 entry of the gap catalogue and the README's row on `Audit/`, each made true in
    this train with the least change, and a sentence of the routes report that named the
    old pins.

  This entry approves the change to `Audit/Crossing.lean`, a protected path: the file stops
  proving its own copy of the crossing bridge and its step, checks with two examples by
  `rfl` that the theorems now in `Elements/BookIII/Cutting.lean` have exactly the
  statements it proved before, and proves the earlier statement by the theorem in
  `Elements`; its later bridges cite that theorem; its notes say where the bridge now
  lives.

  This entry approves the two pins of `Audit/Crossing.lean` that move from the old names
  to the new: the axiom list of `Elements.CirclesCut.cut_point` stands where that of
  `Audit.cut_point` stood, and the list of `Elements.CirclesCut.of_meet` where that of
  `Audit.CirclesCut.of_meet` stood, each list name for name as Lean printed it before.
  The other five pins of the file are unchanged, and `lake build Audit` passes with all
  seven. No pin loses a name or gains one, so none comes to list `Tacit.circles_meet`,
  `Tacit.inside_of_between`, `Tacit.outside_of_between`, `Tacit.centre_unique` or
  `sorryAx` where it did not.
