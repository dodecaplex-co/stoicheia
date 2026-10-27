- **Circle 1 retired after III.2, and the lock down to 48 axioms (foundations, certificate
  and model, [#477](https://github.com/jackChallis/stoicheia/issues/477), with #473).**
  Three answers of the owner's carry this change; the words quoted are the owner's, and
  #473 and #477 are the coordinator's records of them. On 25 October 2026, at about 22:45
  Pacific time, the owner answered three recommendations of the coordinator's, among them
  the radius rule and the plan to retire Circle 1 into a theorem proved in
  `Elements/BookIII/Prop02.lean` after III.2, keeping its name and type: "yes to all
  three." On 26 October 2026, at about 07:20 Pacific time, the owner approved the
  migration's sequence, P0, F1, L1 and F2, of which F2 is this retirement: "Yes to all of
  these." And at about 09:40 Pacific time that day, on whether the retirement should stay
  before the release (#477): "Yes retire Circle 1". So Circle 1
  (`Tacit.between_of_inside_chord`), that a point within a circle on a straight line lies
  between the two points where the straight line meets the circle, is no longer an
  assumption. The preparations went first, so that no check fails on main at any commit:
  the numerical model keeps the rule's predicate as a derived property
  ([its entry](2026-10-25-circle-1-derived.md)), its law draws from a kind of a generator
  other laws use ([its entry](2026-10-25-circle-1-law-inlined.md)), and Book Zero, III.1,
  its porism and III.2 stopped using the rule
  ([its entry](2026-10-25-circle-1-bookzero.md)).

  What moved. The axiom leaves `Elements/Foundations/Tacit/Diagram.lean`, whose module text
  now says that Circle 1 is proved after III.2 with Circle 2 and Circle 3, and whose
  section on circles says that all four of System E's circle rules are proved. The theorem
  `_root_.Elements.Tacit.between_of_inside_chord` stands in `Prop02.lean` after
  `Prop2.within`, first among the rules that III.2 gives back. Its proof: the point A
  within is neither B nor C, which are on the circle (Generalities 4), so of the three
  points one is between the other two (Between 6); were B or C between the others, it would
  be between a point on the circle and a point within it, and so within the circle by
  `Prop2.within`, not on it. It keeps the axiom's name and exact type, its binder names and
  its implicit binders included. Outside the repository, a scratch file printed the axiom's
  binders before the change and the theorem's after it, A, B, C, L and α implicit and hA,
  hB, hC, hAin, hBon, hCon and hBC explicit, with no universe parameter, and the two
  printed types were the same; another checked by `rfl` that the theorem's type is the type
  the lock printed for the axiom.

  Every later call compiles unchanged, for every caller already imports `Prop02.lean`,
  directly or through `Elements/BookIII/Feet.lean`. Of the 32 calls, 26 stay. Six, where
  the point within is the centre, now take the step from Book Zero's
  `between_of_centre_chord`, which proves Circle 1 for a centre from Definition I.15,
  Between 6 and the radius rule: the three in `Prop14.general`, one each in
  `Prop15.le_diameter` and `Prop15.nearer`, and one in `Prop36.through_centre`. No record
  and no commentary describes those steps by Circle 1, and each change spares an entry a
  citation it would otherwise gain: III.14 general, III.15 le_diameter, III.15 nearer and,
  through `Prop36.through_centre`, III.37 would cite III.2, and III.15 le_diameter would
  rest on `exists_centre`, which its record says it does not. The calls kept at a centre
  are those that records or commentary describe as Circle 1, in III.7, III.11, III.13,
  III.20, III.28, III.35 and III.36; the others are in `Prop24.angle_type`, `Prop29.size`,
  III.29 and `angleAtCentre.size`, where the change would make a record stale and spare no
  entry a citation, and in `Arc.measure_eq_iff`, which no entry uses, so that it would gain
  nothing. `Prop35.lean` and `Prop36.lean`, whose proofs name the theorem, did not import
  its file directly but reached it through other files, `Feet.lean` and
  `Circumferences.lean` among them; they now import `Prop02.lean` directly, as section 6
  of `docs/FORMALIZATION.md` asks. `foot_between`, which uses the theorem at the foot of a
  perpendicular, adds `[III. 2]` to its docstring's citations, and the module note of
  `Feet.lean` says the rule is now proved.

  What it proves, read from `facts.json` after `lake build` and
  `lake env lean Certificate/Facts.lean`. The certificate has 48 axioms and the 268 words
  of the vocabulary, as before. `proved_rules` holds Circle 1, resting on III.2's 43
  axioms, and `proved_rule_cites` gives it III.2 alone. Of the 149 entries, 99
  propositions, three porisms and 47 companions, none rests on Circle 1 as an axiom. Just
  before this change, at 8362dd77, 37 rested on it in total, the first III.7 (23
  propositions, no porism and 14 companions), 23 through their own proofs and the proved
  rules beneath them (16, 0 and 7), and 17 proofs named it themselves (11, 0 and 6). Now 36
  entries use the proved rule, counting the entries they cite (23, 0 and 13), as their
  `proved_rules` show, and 19 use it through their own proofs and the lemmas beneath them
  (15, 0 and 4), as a scratch file that walks the proof terms as the certificate's walk
  does found: III.7, III.8, III.11, III.13, III.14, III.15, III.20, III.22, III.24, III.26
  to III.29, III.35 and III.36, and the companions III.20 special, III.24 equalCircles,
  III.24 equalMeasure and III.31 less. Each of the 19 cites III.2, and III.14, III.35 and
  III.36 cite it for the first time; 40 entries cite III.2 where 37 did. Every other
  entry's axioms are as they were, Circle 1 apart, except that III.14 and its companion
  III.14 general now rest on `exists_centre`, which III.2 takes its centre from: 55 entries
  rest on it (29, 0 and 26) where 53 did, and through their own proofs 48 (28, 0 and 20)
  where 46 did, III.11 and III.14 joining, since Generalities 4, beneath the new theorem,
  takes its centre from the rule. No proposition's, porism's or companion's statement, no
  definition and no `--` line changes.

  A use before III.2 is refused. Facts.lean's walk goes on through every Tacit theorem it
  meets, so an entry that used Circle 1 would cite III.2, and the check on later citations
  refuses that in Books I and II and in III.1. In a copy of the tree outside the
  repository, II.14's proof was given a use of the theorem and an import of `Prop02.lean`,
  which Lean admits; there `facts.json` gave II.14 a citation of III.2, and
  `check_fidelity.py` failed with "II.14: cites III.2, which does not come before it",
  beside the expectation that II.14 cites no III.2.

  The audits stay, and say what they now show. Nine pins lose Circle 1 and gain nothing: in
  `Audit/Overlaps.lean` those of `III_26_any`, `III_27_any`, `III_24_measure` and
  `III_30_measure`, whose prose stays true, and in `Audit/Crossing.lean` those of
  `III_5_today`, `III_11_today`, `III_13_today`, `cut_point` and `CirclesCut.of_meet`,
  whose prose now says that Circle 1 is proved after III.2 and cannot appear in a list.
  Every audit lemma and every `#guard_msgs` stays. The overlap screen's list of circle
  rules, `CIRCLE` in `Audit/screen.py`, drops Circle 1, as it dropped Circle 3 when that
  rule was retired, and keeps nine names; so the screen, which stops on a name the
  certificate does not hold as an axiom, does not stop. Whether the radius rule joins the
  list is left to the screen's owner (#416). The certificate's expectation that III.2's
  axioms exclude Circle 1 can no longer fail, as its reason, written while the rule was an
  axiom, already says: once Circle 1 is proved after III.2, its name is in no entry's
  axioms, and Lean keeps III.2 off it, since it admits no circular proof.

  The formal model follows its generator: `Check/Write.lean` wrote `Model/Laws.lean`, 48
  laws reaching 152 words, `Check/Laws.lean` and `Model/Assembly.lean` again, without
  Circle 1's law, its check or its field. The two hand translations of Circle 1, in
  `Model/Laws/circles.lean` and `Model/Laws/intersections.lean`, are now compared with the
  theorem's type by `comparePlanted`, binder kinds included, in `Check/Circles.lean` and
  `Check/Intersections.lean`, which import `Prop02.lean` already. The plane's two proofs of
  Circle 1 stay, as derived facts with their audits: 41 retired rules and 48 locked laws.
  `model/README.md` counts them so and drops Circle 1's row from the table of laws the
  assembly gathers. The model builds, and `check_model_kernel.py` replays all 55 of its
  compiled modules. The numerical harness drops Circle 1's law and keeps checking its
  predicate as `derived.between_of_inside_chord`. The kind `'chord'` of `gs_cm` in
  `hyperbolic.py`, which only that law drew from, stays. Only the kind's code had to stay:
  the guard, `laws_move_with_axioms` in `scripts/safe_push.py`, compares a harness's code
  outside its laws with main's and leaves comments out, as the correction of 25 October
  2026 says ([its entry](2026-10-25-circle-3-retired-wording.md)). The kind's comment,
  which names the law the file no longer has, stays with it for now; both go in a later
  change, P5 of #477. The counts go from 49 axioms to 48, and from 43 tacit rules to 42.

  What it does not prove. Circle 1 is proved from III.2, so it is not independent of III.2,
  and no proof before III.2 may use it. The steps the later propositions take from it are
  the same steps, now argued from III.2; their routes, as their records give them, do not
  change. The records of III.2, III.14, III.15, III.35 and III.36 are stale for their Lean,
  and those of III.7, III.8, III.11, III.13, III.14, III.15, III.20, III.22, III.24,
  III.28, III.31 and III.35 for their text, until a reader of the other family reads and
  stamps them.

  This entry approves the change to `Certificate/axioms.lock`, which loses the one line of
  `Tacit.between_of_inside_chord` and gains none, 48 axioms with 268 words.

  This entry approves the change to `Elements/Foundations/Tacit/Diagram.lean`, from which
  the axiom of Circle 1 goes, its module text now saying where the circle rules are proved.

  This entry approves the change to `model/lock.sha256`, renewed to the hash of the lock
  without Circle 1, with a paragraph dated 26 October 2026 on what moved in the formal
  model.

  This entry approves the change to `tests/model/lock.sha256`, renewed to the same hash,
  with a paragraph dated 26 October 2026 on what moved in the numerical harness.

  This entry approves the change to `tests/model/laws.toml`, whose line naming the law of
  `Tacit.between_of_inside_chord` goes, and no other.

  This entry approves the change to `tests/model/search.py`, from which the function for
  Circle 1's law goes, with the blank lines after it, the rest of the file untouched.

  This entry approves the change to `tests/model/hyperbolic.py`, from which Circle 1's
  hyperbolic law goes in the same way, its kind of `gs_cm` and every other line kept.

  This entry approves the change to `tests/model/derived.py`, one clause of its opening
  note, which said that Circle 1 is still an axiom and now says that its retirement
  followed.

  This entry approves the change to `tests/model/MODEL.md`, whose prose now counts
  forty-one former axioms, places Circle 1 among them and gives its reason in the section
  on circles.

  This entry approves the change to `model/Model/Audit.lean`, two comments only, which now
  count 41 retired rules and 48 locked laws, with every audit, guard and pin kept.

  This entry approves the change to `Audit/Overlaps.lean`, four pins regenerated from
  Lean's report, each without Circle 1 and with nothing added, and no other line.

  This entry approves the change to `Audit/Crossing.lean`, five pins regenerated without
  Circle 1, and two comments made true now that Circle 1 is a theorem after III.2.

  This entry approves the change to `Audit/screen.py`, whose `CIRCLE` list drops Circle 1,
  leaving nine names, so that the screen does not stop on a name that is no longer an
  axiom, and whose account of its runs names this retirement and the counts of the lock it
  leaves.

  The numerical model's results were written again on this harness:
  `python3 -I tests/model/run.py --full --write` ran at commit `5ef38f3f2a55`, this train's
  head with the law removed, where every check passed: no counterexample in the plane, 15
  mutations of 15 caught, and in the hyperbolic plane only Postulate 5 failing, as it must.
  Configurations meeting an axiom's hypotheses in the plane come to 4,063,299, where they
  came to 4,063,054 at P2's run; the three random searches draw again without the law and
  give 408,083, 408,046 and 407,697 where they gave 407,895, 408,049 and 407,637. The
  derived properties, Circle 1 among them since P1, keep their 9,895,990. The run also
  rewrote the counts between MODEL.md's own markers.

  Each result file that run rewrites is approved in a sentence of its own. The angle and
  area check's output, `tests/model/results/angle_check.txt`, is approved. The full grid
  enumeration's output, `tests/model/results/exhaustive.txt`, is approved. The second exact
  grid check's output, `tests/model/results/grid_check.txt`, is approved. The hyperbolic
  run's output, `tests/model/results/hyperbolic.txt`, is approved. The weakened statements'
  output, `tests/model/results/mutations.txt`, is approved. The random search's first seed,
  `tests/model/results/search-seed1.txt`, is approved. Its second seed,
  `tests/model/results/search-seed2.txt`, is approved. Its third seed,
  `tests/model/results/search-seed3.txt`, is approved. The structured search's output,
  `tests/model/results/structured.txt`, is approved. The table drawn from them all,
  `tests/model/results/summary.txt`, is approved.
