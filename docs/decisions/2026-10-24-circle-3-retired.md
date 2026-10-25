- **Circle 3 retired after III.2, and the lock down to 48 axioms (foundations, certificate
  and model, #294).** Under the coordinator's orders of 24 October 2026, which assign this
  train of #294, part of #152, Circle 3 (`Tacit.outside_of_between`) is no longer an
  assumption. It says that a straight line which has left a circle does not come back,
  and so it gives III.2 at once: were a point between two points of the circle not within
  it, the second point would be outside.
  An axiom that holds a proposition of Book III is one we would rather prove, and III.2
  proves this one in two lines, through its corollary `Prop2.within`. So #294's question,
  whether to retire Circle 3 after III.2 or to say why it stays, is answered by retiring
  it. The theorem keeps the axiom's name and exact type, its binder names and implicit
  binders included.

  What moved, and where. The axiom leaves `Elements/Foundations/Tacit/Diagram.lean`, whose
  module text now says where Circle 2, Circle 3, Points 9 and Intersection 2 are proved.
  The theorem `_root_.Elements.Tacit.outside_of_between` follows `Prop2.sameSide` in
  `Elements/BookIII/Prop02.lean`. Three Book Zero theorems whose proofs used Circle 3 left
  `Elements/Figure/Circles.lean` for the same place after III.2, each under its own name
  and with its own type: Circle 2 (`Tacit.inside_of_between`), which is now the term
  `Prop2.within`, since that corollary has its statement; Points 9
  (`Tacit.exists_point_outside_circle`), with its private helper `inside_point_of_chord`;
  and Intersection 2 (`Tacit.line_meets_circle_of_opposite_sides`), with its private
  helper `circle_intersections_of_inside`. The proofs of Points 9 and Intersection 2 keep
  their steps, but take the one that Circle 3 took from III.2 itself, by `Prop2` and
  `Prop2.within`, so nothing in the file uses Circle 3. `between_at_crossing`, which
  Triple incidence 3 in Circles.lean calls as well and which uses no rule about circles,
  stays there as a public Book Zero lemma with a docstring of its own.
  `Elements/Figure/OnCircles.lean` loses `Triangle.of_onCircle`,
  `exists_onCircle_oppositeSidesOf` and `exists_onCircle_sameSideOf`, which rested on
  Circle 2 and had no user in `Elements/`, `Staging/`, `Audit/` or `model/`; III.2's
  corollaries `Prop2.triangle`, `Prop2.oppositeSide` and `Prop2.sameSide` give the same
  facts for any circle, as the module text of OnCircles.lean now says.

  Why it is safe. The route was laid by the entry of 23 October,
  [the circle rules from III.2](2026-10-23-circle-rules-from-iii2.md): `check_lock` takes a
  forbidden circle rule missing from the lock as a theorem only when its
  `proved_rule_cites` in `facts.json` holds III.2, with III.2 proved and resting on
  neither rule. The regenerated certificate gives exactly that for all four moved rules,
  each citing III.2 alone, and III.2 cites I.5, I.16 and I.19. Citations are gathered by
  a walk that goes on through every Tacit theorem it meets, so any proof using one of the
  four would cite III.2, and the check on later citations refuses that in Books I and II
  and in III.1; III.2 cannot use them, since Lean admits no circular proof. Book Zero still
  cites no proposition: nothing left in it calls the moved rules. No entry's axioms or
  citations change; `facts.json` moves only the line numbers recorded for the Book Zero
  lemmas that follow the ones taken out. No proposition's or porism's statement, no
  definition and no `--` line changes. `review/III/02.toml` drops its `[overlap]` table,
  whose rule must be an axiom, and III.2's row moves to the catalogue's former overlaps.

  The audits stay, and say what they now show. In `Audit/Overlaps.lean`, `Audit.III_2`
  and `Audit.III_2_outside` reach III.2 through its own corollaries, as `Audit.I_7`
  reaches I.7, and `Audit.inside_of_between` and `Audit.outside_of_between`, each rule
  derived from the other, reach III.2 through the other: each of the four pins moves from
  Lean's three axioms with Circle 3 to the 47 that Lean prints for III.2 itself, Lean's
  three and 44 of ours. Every audit lemma and every `#guard_msgs` stays. The overlap
  screen leaves Circle 3 out of its list of circle rules, since it tries axioms alone and
  would stop on a name the certificate does not hold as one.

  The formal model follows its generator: the generated laws, checks and assembly lose
  Circle 3's law, and the two hand translations of Circle 3 are now compared with the
  theorem's type by `comparePlanted`, binder kinds included, in place of the generated
  field, in Check files that import the module where the moved rules live. The plane's
  proofs of Circle 3 stay, as derived facts with their audits; 40 retired rules and 48
  locked laws, which reach 152 words, as before. The numerical harness drops Circle 3's
  law and keeps checking its predicate as `derived.outside_of_between`, as the preparation
  of 24 October arranged. The helpers that only this law called, `in_or_on` in both
  harnesses and `gs_convex` in `hyperbolic.py`, went before it, in the preparation that
  narrowed the law allow-list of `scripts/safe_push.py` by them
  ([its entry](2026-10-24-circle-3-law-inlined.md)); the examples that
  `Certificate/FIELDS.md` and `review/SCHEMA.md` give of Circle 3 as an axiom follow in a
  change of their own. The kind `'out'` of `gs_cm`, into which that preparation moved
  Circle 3's sampler, stays though no law draws from it now: a harness may change here
  only in the laws that move with their axioms, so it goes later, in a change of its own.
  The counts
  go from 49 axioms to 48, and from 43 tacit rules to 42; the vocabulary stays at 262
  words. Section 2 of `docs/FORMALIZATION.md` also says now, for #420, that I.4 and I.8
  supply lists of names from which `Symbols.ofList` computes the numbering.

  This entry approves the change to `Certificate/axioms.lock`, from which one axiom,
  `Tacit.outside_of_between`, is removed, and to which none is added.

  This entry approves the change to `Elements/Foundations/Tacit/Diagram.lean`, the
  foundations file that no longer declares Circle 3 and points to its new home.

  This entry approves the change to `Elements/Foundations/Tacit/Constructions.lean`, a
  comment alone: its module text now places Points 9 after III.2.

  This entry approves the change to `model/lock.sha256`, renewed to the smaller lock's
  hash with a dated paragraph on what moved in the model.

  This entry approves the change to `tests/model/lock.sha256`, renewed likewise for the
  numerical harness, with a paragraph of its own.

  This entry approves the change to `tests/model/laws.toml`, which loses only the line
  that named Circle 3's law.

  This entry approves the change to `tests/model/search.py`, from which Circle 3's law
  function goes, every other law in its place and the rest of the file untouched.

  This entry approves the change to `tests/model/hyperbolic.py`, from which Circle 3's
  hyperbolic law goes in the same way, nothing else in it altered.

  This entry approves the change to `tests/model/MODEL.md`, whose prose now counts forty
  former axioms and puts Circle 3 among them, with its count markers standing as they were.

  This entry approves the change to `model/Model/Audit.lean`, where two comments now say
  40 retired rules and 48 locked laws, every audit, guard and pin kept.

  This entry approves the change to `Audit/Overlaps.lean`, whose four pins on the III.2
  and circle audits print III.2's axioms now, with headers and docstrings to match.

  This entry approves the change to `Audit/Centre.lean`, whose comment on reading each
  renewal now says why Circle 2 and Circle 3 cannot appear in its pinned list.

  This entry approves the change to `Audit/Crossing.lean`, two comments on the bridges and
  on III.5 and III.6, made true now that the circle rules are theorems.

  This entry approves the change to `Audit/screen.py`, whose `CIRCLE` list drops Circle 3
  and whose account of its runs gives the counts of this lock.

  The numerical model's results were written again on this harness:
  `python3 -I tests/model/run.py --full --write` ran at commit `2ce08a8eaf9b`, and every
  check passed: no configuration of the plane broke an axiom, each of the 15 weakened
  statements was caught, and in the hyperbolic plane only `Postulate5` failed, as it must.
  With one law fewer drawing on the random numbers, the search's three seeds and the
  hyperbolic run meet the other laws' hypotheses a little differently, so the plane's
  axiom total moves from 4,097,933 to 4,098,108; the derived properties' stays at
  9,855,030. MODEL.md carries the counts as the run wrote them.

  This entry approves, one at a time, each result file that this run wrote:
  - `tests/model/results/angle_check.txt`, from the angle check at this commit;
  - `tests/model/results/exhaustive.txt`, from the exhaustive enumeration at this commit;
  - `tests/model/results/grid_check.txt`, from the lattice check at this commit;
  - `tests/model/results/hyperbolic.txt`, from the hyperbolic plane at this commit;
  - `tests/model/results/mutations.txt`, from the mutation run at this commit;
  - `tests/model/results/search-seed1.txt`, from seed 1 of the search at this commit;
  - `tests/model/results/search-seed2.txt`, from seed 2 of the search at this commit;
  - `tests/model/results/search-seed3.txt`, from seed 3 of the search at this commit;
  - `tests/model/results/structured.txt`, from the structured run at this commit;
  - and `tests/model/results/summary.txt`, the table of all of them at this commit.
