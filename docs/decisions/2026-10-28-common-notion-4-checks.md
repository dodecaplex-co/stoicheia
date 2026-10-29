- **I.4's area clause by Common Notion 4: the checks land first, and hold I.4 to one of
  two states (checks, [#517](https://github.com/dodecaplex-co/stoicheia/issues/517)).** On
  28 October 2026 the owner chose, of the options put to them, "Euclid's C.N. 4"; issue
  #517 is the coordinator's record of it. I.4's clause that "the triangle will be equal to
  the triangle" (Heath's enunciation, `heath/I/04.md`) is to rest on Common Notion 4 for
  figures, a new axiom, `Tacit.figures_coincide`, in the place of Metric 9
  (`Tacit.area_congruent`), which then retires.

  #517 is split, and this train, its check change, lands first and alone, before the
  content. When origin/main's checks fail on a commit, as they will on the content, which
  changes the axiom lock, the pre-flight lets that commit change a check input only where
  the change is a value pinned to the edition (`keep_apart` and `pinned` in
  `scripts/safe_push.py`, and WORKFLOW, "Landing work: pull requests"). So the changes
  below to the checks themselves go ahead of the content. Each holds on main as it
  stands, where no entry names the new axiom and Metric 9 is still I.4's. Each holds of
  the content's certificate too, read with this train's code and its expectations, once
  the content has moved the values it pins with its lock, as the axioms listed for III.1
  Por. in the first expectation.

  Nothing is loosened. The coordinator ruled on 28 October 2026, after the owner's choice,
  that the checks ask no less of I.4 at any time, the time between the two trains
  included: "No loosening, not even between two trains." So the expectations keep every
  demand main makes of I.4, and add one, and the content restores nothing, since nothing
  was relaxed for it.

  The two states. `check_expectations` in `scripts/check_fidelity.py` reads a new form,
  an expectation with `one_of`: an entry's `ref`, a `why`, and two states or more, each
  with a name of its own and a nonempty list of that entry's ordinary expectations, every
  one read by the same code as an expectation that stands alone. It passes only when
  exactly one state holds. When none does, it fails once, naming each state with the
  failures that sank it, so a reader sees how far the tree is from either; when two hold,
  the states were not exclusive, and it fails too. A malformed one fails with its own
  message. I.4's two expectations that named Metric 9's law, that its `cited_laws` are
  exactly seven, `areaCongruent` among them, and that the area law is proved with no
  construction rule, are now the state "Metric 9", asking word for word what they asked
  on main, with one demand more that marks the state: Common Notion 4 for figures is not
  among I.4's `own_axioms`. The state "Common Notion 4 for figures" is the content's: the
  six laws without the area law, numbering six, and `Tacit.figures_coincide` among I.4's
  `own_axioms`, pinning by name the axiom the clause rests on, where main pinned Metric 9
  only through its law.

  Nothing between passes. The two counts, seven and six, cannot both hold, so the states
  exclude each other. A tree with the new axiom while I.4 still cites seven laws fails
  "Metric 9" by its `own_axioms` and the other state by its count; a tree with the six
  laws and without the new axiom fails "Metric 9" by the law and the count, and the other
  state by the axiom. There is no switch to choose a state, and no state that asks less
  than main did. Nor can the content change a state: `kept_expectations` in
  `scripts/safe_push.py` compares a key it does not know, as `one_of` is, by equality, so
  a commit that drops a state, or loosens or even rewords an expectation inside one, does
  not keep main's expectations, and with origin/main's checks failing on it, the
  pre-flight refuses it. This follows #629, which holds the circle to its old
  representation profile or the new one, and to nothing between.

  The restriction. `check_fidelity.py` now holds `Tacit.figures_coincide` to I.4, beside
  the rule that holds superposition to I.4 and I.8: an entry other than I.4 that has it
  among its `direct_axioms` fails, with a message of the same form as superposition's,
  "I.5: uses Common Notion 4 for figures directly (only I.4 may)". Any other entry that
  rests on the axiom may then reach it only through what it cites or through a Common
  Notion, the two routes `direct_axioms` leaves out; on the content, every one of them
  reaches it through what it cites, as I.5 does through I.4. On main no entry names it,
  so the rule holds of every entry there. A plant, `figures_coincide_used`, gives the
  name to I.5 and to I.4 among their direct axioms on a copy of facts.json; the check must
  fail naming I.5 and must not blame I.4.

  A second plant, `i4_between_states`, puts I.4 between the states on a copy of
  facts.json, in two trees: the new axiom among its `own_axioms` while it cites the seven
  laws, and the six laws without the axiom. It builds each from whichever state
  facts.json is in, so it keeps its force once the content has landed, and the check must
  fail each by the expectation with `one_of`, naming both states.

  The Jev bundle. The question generator named, for the representation rows of I.4 and
  I.8, the proof of each law their derivations cite, I.4's
  `Superposition.Cited.holds_areaCongruent` among them. The content deletes that proof,
  and since no file under `scripts/` is a pinned value, the content could not change the
  generator's list. The generator now reads the proofs from the certificate: for each of
  the two, every proof of every entry of its `cited_laws` in facts.json, with `Elements.`
  before it, both in the bridges its row supplies and in what its record is held to have
  checked. I.8 keeps `SameSideOf.of_line` as a named extra, since the certificate gives
  `BookI.Prop8.holds_prop7` as the proof of I.7's law, and that proof turns I.7's same
  side of a straight line into the same side of its two points through it. On main the
  names read are those the generator named before, in the same order, and its rows, for
  each proposition it does not refuse, are byte for byte those it gave before; the content
  need not change the list. Its test now
  holds the bridges to the checked set with the proofs read from facts.json and the extra,
  still asserts by name a core of laws that I.4 and I.8 cite on both sides, and refuses an
  entry that gives no cited law, or a law no proof, in a case of its own.

  Approved here: the changes to `scripts/check_fidelity.py`, which let I.4 alone name
  Common Notion 4 for figures among its direct axioms, and read an expectation with
  `one_of`, through the same code as every other expectation.

  Approved here as well: the new plant `scripts/negative/figures_coincide_used.py`, which
  must see I.5 refused for that axiom and I.4 let through.

  This entry approves the new plant `scripts/negative/i4_between_states.py`, which must
  see I.4 refused in both trees between its two states.

  The edit to `tests/certificate_expectations.json` is approved by this entry: I.4's
  expectation of seven cited laws and its expectation of the area law's construction
  rules, unchanged in what they ask, become the state "Metric 9" of one expectation with
  `one_of`, beside the state "Common Notion 4 for figures", each with its demand on I.4's
  own axioms.

  The cases added to `tests/test_certificate.py` are approved here: each state of I.4
  passing alone, both trees between them failing once with each state named, two states
  that hold at once failing, and every malformed `one_of` failing with its message.

  `scripts/audit/jev_questions.py` may read the cited-law proofs of I.4 and I.8 from
  facts.json instead of naming them; this entry approves that change.

  This entry also approves the change to `tests/test_jev_questions.py`, whose case of the
  superposition rows reads those proofs from facts.json and keeps a literal core.
