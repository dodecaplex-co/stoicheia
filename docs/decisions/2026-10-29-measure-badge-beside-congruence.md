- **The measure's badge beside circumferences that coincide (tooling,
  [#662](https://github.com/jackChallis/stoicheia/issues/662)).** The coordinator's orders
  of 29 October 2026 give this change card #662, filed from a reader's review of Book
  III's work of 28 October (GPT-6 Astra), which judged the fault material; the card
  blocks the release. It
  builds on [the entry of 26 October](2026-10-26-generated-phrases-read-through-03.md),
  which kept the badge of `angle-measure` to statements that use the measure.

  What was false. Each clause of III.26 and of III.28 concludes two things: that the
  circumferences are equal in our measure (`Elements.circumference`), and that they
  coincide (`Elements.Arc.Congruent`); their records read Euclid's "equal circumferences"
  as both. Yet the line under each enunciation said "proved, as Euclid states it, in our
  measure of circumferences", as if the measure were the whole reading. Beside them,
  III.24's main statement concludes `Arc.Congruent` and names no measure, which only its
  companions `equalCircles` and `equalMeasure` use, and its line said nothing of the
  measure at all. The queued train that swaps III.27 and III.29 gives each the same shape
  as III.24: a main statement in `Arc.Congruent` alone, with a new companion,
  `of_measure`, in the measure. Under the rule of 26 October the badge would leave their
  lines once it lands, and those pages too would be silent about the measure their
  companions carry.

  The rule. The badge is now chosen from what the statement states, and, where needed,
  what its companions state: from the Lean words of each, as `statement_names` reads
  them, and from no list of propositions. Beside `BADGE_WORDS`, the measure's words,
  `scripts/render.py` gains `BADGE_BESIDE`, the words of the reading the measure stands
  beside: for `angle-measure`, `Elements.Arc.Congruent` alone. For a tag of
  `BADGE_WORDS`, four cases follow.
  - A statement that uses the measure and not `Arc.Congruent` keeps "in our measure of
    circumferences" (III.30, and III.27 and III.29 as main holds them today). It is true,
    since the measure is the only reading of the circumferences the statement gives.
  - A statement that uses both reads "and in our measure of circumferences", so that the
    line says "proved, as Euclid states it, and in our measure of circumferences" (III.26
    and III.28). It is true, since the statement proves the circumferences equal in both
    the senses its record reads Euclid's words in: they coincide, and their measures are
    equal.
  - A statement that uses `Arc.Congruent` and not the measure, with a companion whose
    statement uses the measure, reads "with a companion in our measure of circumferences"
    (III.24, and III.27 and III.29 once the swap lands). It is true, since the main
    statement reads Euclid's equal circumferences as circumferences that coincide, which
    needs no measure, and the measure comes in only in a companion the page attaches.
    That wording is the reader's least change.
  - Any other statement has no badge (III.25, whose main statement names neither).

  A tag that `BADGE_WORDS` does not name gives its badge to every statement it is on, as
  before. The two new wordings are made from the tag's own `badge` in
  `review/terms.toml`, with "and " or "with a companion " before it, so the file keeps
  its three keys, the only ones `heath.load_terms` accepts. A companion's statement
  decides only whether the third case applies: a companion that names `Arc.Congruent`, as
  `equalMeasure` does, never moves its main statement from the first case to the second.

  The certificate's dagger, which its key glosses as "a statement read in our measure of
  circumferences", stays with a statement that itself uses the measure, the first two
  cases: III.26, III.28 and III.30, and III.27 and III.29 until the swap. III.24 gains no
  dagger, nor will III.27 and III.29 keep theirs once it lands. The key's words do not
  change.

  The change is to what `scripts/render.py` writes and to the comment at the head of
  `review/terms.toml`: no tag, meaning or badge there changes, and no check, test,
  expected value or lock is weakened. The pages of III.24, III.26 and III.28 change on
  their line under the enunciation, and `CERTIFICATE.md` does not change. P4 of
  `scripts/check_acceptance.py` still asks for the line `in_lean_line` gives; that
  function now finds a statement's companions in facts.json when it needs them, so the
  check gets the page's line with no change of its own.

  This entry approves the change to `scripts/render.py`: the new `BADGE_BESIDE`, the four
  cases in `representation_badge`, which reads the companions facts.json attaches when
  no list of them is given, and `certificate_row`, which gives it none, so its dagger
  needs the measure in the statement.

  This entry approves the change to `review/terms.toml`, whose header comment now says how
  the renderer words the badge and when the certificate's row is marked.

  This entry approves the change to `tests/test_check_style.py`, a new test,
  `MeasureBadge`, which builds facts held in memory and checks the line and the dagger in
  each case, and that `Other.Arc.Congruent` or a quoted "Elements.Arc.Congruent" is not
  the word.
