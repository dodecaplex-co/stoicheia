- **Four pins keep the eight retired rules from beneath III.1, its porism, III.2 and
  II.14, read from each entry's proved rules (certificate,
  [#168](https://github.com/jackChallis/stoicheia/issues/168)).** This is the second and
  last train of card #168, which the coordinator gave to ship ER on 26 October 2026 and
  which holds every release while it stays open. The first train
  ([its entry](2026-10-26-proved-rules-per-entry.md)) gave every certificate entry a list
  of the proved rules beneath it, `proved_rules`, found by a walk that the run holds to
  Lean's `collectAxioms`; this train puts that list to work.

  Decided: `tests/certificate_expectations.json` gains four expectations, one for each of
  III.1, III.1 Por., III.2 and II.14, which read the entry's `proved_rules` and exclude
  all eight tacit rules that the retirement of #119 made theorems. In name order they are
  `Tacit.adjacent_eq_of_right`, `Tacit.centre_unique`,
  `Tacit.exists_point_outside_circle`, `Tacit.inside_of_angle_add`,
  `Tacit.inside_of_between`, `Tacit.line_meets_circle_of_opposite_sides`,
  `Tacit.not_same_side_of_circles_meet` and `Tacit.triple_incidence3`.

  Why: #168 calls for stronger pins excluding the eight beneath these four entries, to
  follow the retirement's first pin change. The pins written then put the eight names in
  `excludes` on each entry's `axioms`, where a theorem's name never appears, so they could
  not fail. A proved rule leaves only its own axioms in an axiom list, but its name in
  `proved_rules`; a pin there fails when an entry comes to rest on one. On 21 October 2026
  the owner chose, of the options the coordinator put to them, "Remove the uses first",
  and #168 holds the coordinator's record of it. With those uses gone, none of the eight
  lies beneath the four entries today, so each new pin excludes all eight, where their
  first draft, written before the removal, excluded seven of them (the porism's six) and
  held the porism's list to exactly two.

  The card also asks that III.1 Por.'s pin be restored to full strength, in the `equals`
  form planned for train C6. The first expectation of the file already has that form: it
  holds the porism's `axioms` to exactly the list of its proof by Euclid's reductio, with
  `Tacit.centre_unique` excluded and its tacit rules counted. This train leaves its list,
  its count and its exclusion untouched. Six older pins on `axioms` now point to the new
  pins in their reasons: the two at the head of the file, on III.1 and its porism, and
  the four that exclude the eight. Only those reasons are reworded, and every expectation
  on main keeps its `includes`, `excludes`, `count` and `equals`.

  The new plant, `retired_rule_used`, writes one line into III.2's proof, a use of
  `Tacit.centre_unique`, builds, regenerates the certificate and runs
  `scripts/check_fidelity.py`, which must refuse the use by the pin on III.2's
  `proved_rules` and by no pin on III.2's `axioms`; then it puts the source and
  `facts.json` back byte for byte and rebuilds. That rule was chosen because every axiom
  beneath it already lies beneath III.2 and it cites no entry, so III.2's `axioms` and
  `cites` come out exactly as before, and only the new pin can see it; the plant fails if
  either field changes. Of the other seven, `Tacit.triple_incidence3` would serve as well;
  three are proved from III.2 and cannot be used in its proof; the remaining three would
  make III.2 cite I.13 or I.7. Run alone on 26 October, the plant took 93 seconds,
  restoration included.

  Our warm thanks to ship TS, whose branch `tooling/proved-rules-per-entry` held the
  plant, its tests on a stand-in tree and the first form of the four pins, all written on
  21 October, while the uses were still there. This train carries them over: the plant
  into a file of its own, as plants are written now, finding the pin it names by `ref` and
  field even past expectations that have no `ref`; the tests to that form, with cases for
  a refusal by another entry's pin, for a changed `cites`, for a build or certificate that
  fails or is interrupted, and for a file without the pin; and the pins brought up to all
  eight.

  Small fixes left by the first train's reviews come with it. The test of the
  certificate now runs a copy whose walk for proved rules stops at each rule, and sees
  the run fail; and its fixture reaches a rule through a Common Notion. Two comments in
  the certificate's source now speak of every walk of a proof, as its field guide already
  does, since the walk for the vocabulary does not read through `mentions`; the field
  guide loses a stray reference to a stage. Section 8 of
  [WORKFLOW](../WORKFLOW.md) describes the new cases of the certificate's tests.

  The protected file `tests/certificate_expectations.json` takes the four new pins and
  six reworded reasons, and nothing in it is weakened.

  A new protected file, `scripts/negative/retired_rule_used.py`, holds the plant itself.

  Inside the protected runner `scripts/negative_tests.py`, only its module docstring is
  touched: seven plants build now, and the list of them names the new one.

  The protected `tests/test_negative_tests.py` gains `RetiredRulePlantTests`, six tests
  that fail when the plant is not caught, is caught by the wrong pin, or does not put the
  tree back.

  The protected `tests/test_certificate.py` gains the self-check case and the route
  through a Common Notion, its fixture declaring stand-ins for the seven declarations by
  which the certificate knows the five Common Notions.

  The protected `Certificate/FIELDS.md` names, in its row for the entry field
  `proved_rules`, the four pins that read it and the plant, lists them among what the
  fidelity check reads, and drops a stray "(stage 1b)".

  The protected `Certificate/Facts.lean` changes in two comments alone; regenerated, it
  writes `facts.json` byte for byte as before.
