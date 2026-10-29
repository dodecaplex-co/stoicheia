- **I.4's area clause by Common Notion 4: the checks land first (checks,
  [#517](https://github.com/dodecaplex-co/stoicheia/issues/517)).** On 28 October 2026 the
  owner chose, of the options put to them, "Euclid's C.N. 4"; issue #517 is the
  coordinator's record of it. I.4's clause that "the triangle will be equal to the
  triangle" (Heath's enunciation, `heath/I/04.md`) is to rest on Common Notion 4 for
  figures, a new axiom, `Tacit.figures_coincide`, in the place of Metric 9
  (`Tacit.area_congruent`), which then retires.

  #517 is split, and this train, its check change, lands first and alone, before the
  content. When origin/main's checks fail on a commit, as they will on the content, which
  changes the axiom lock, the pre-flight lets that commit change a check input only where
  the change is a value pinned to the edition (`keep_apart` and `pinned` in
  `scripts/safe_push.py`, and WORKFLOW, "Landing work: pull requests"). So the changes
  below to the checks themselves go ahead of the content. Each holds on main as it
  stands, where no entry names the new axiom and Metric 9 is still I.4's, and each holds
  of the content's certificate, read with this train's checks.

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

  The expectations. Two expectations of I.4 in the certificate's expectations name Metric
  9's law, `areaCongruent`, and the content makes both false. The first asked that I.4's
  `cited_laws` include seven laws, the area law among them, and number seven: the area
  law leaves its `includes`, while its count stays at seven, so that on main the number
  still holds the list to those six and one law more, and its `why` now says so. The second asked that the area
  law, among I.4's cited laws, be proved with no construction rule; it goes, for the
  content leaves no such law to read. Between the two trains, then, the file asks less of
  I.4 than it did. The content is to ask more again, and more strongly: it moves the count
  to six, which pins the list exactly without the law, and it adds an expectation that
  I.4's `own_axioms` include `Tacit.figures_coincide`, pinning by name the axiom the
  clause rests on, where Metric 9 was pinned only through its law, by the law's name and the construction
  rules of its proof; and the restriction above, which no expectation could give, holds that axiom to
  I.4.

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

  Approved here: the change to `scripts/check_fidelity.py` that lets I.4 alone name
  Common Notion 4 for figures among its direct axioms.

  Approved here as well: the new plant `scripts/negative/figures_coincide_used.py`, which
  must see I.5 refused for that axiom and I.4 let through.

  The edits to `tests/certificate_expectations.json` are approved by this entry: the
  area law out of I.4's list of seven, with its count kept, and the area law's own
  expectation removed.

  `scripts/audit/jev_questions.py` may read the cited-law proofs of I.4 and I.8 from
  facts.json instead of naming them; this entry approves that change.

  This entry also approves the change to `tests/test_jev_questions.py`, whose case of the
  superposition rows reads those proofs from facts.json and keeps a literal core.
