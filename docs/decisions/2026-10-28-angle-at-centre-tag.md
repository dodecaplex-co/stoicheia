- **The angle at the centre gets a tag of its own, and five meanings in the terms list are
  made true (checks, [#524](https://github.com/dodecaplex-co/stoicheia/issues/524),
  [#370](https://github.com/dodecaplex-co/stoicheia/issues/370)).** Book III's reviews of
  26 October 2026 showed tag meanings in the terms list whose lists of propositions
  disagree with the records that carry them (the table of tags and records in
  [the limitations review](../reports/limitations-01.md) gives the records), and that
  III.20's record has no tag for its reading of the angle at the centre. This change
  answers them, in two pull requests. This one, to the terms list and the renderer, lands
  first. III.20's record, which takes up the new tag, and the tag cell of
  [FORMALIZATION](../FORMALIZATION.md)'s row for the angle at the centre follow, because a
  check input changed with the record it judges is refused at landing.

  III.20 reads the angle at the centre as `angleAtCentre`, the angles BEF and FEC
  together, so that it may be two right angles or more. That reading is ours, made after
  Heath's notes on III.20 and III.21. The new tag, `angle-at-centre`, is a representation
  with no badge, for on Euclid's own figures the angle it names is his angle BEC. The word
  `angleAtCentre` came into `Elements/` by
  [the entry for #129](2026-10-25-routes-iii-centre.md), and the reading of touching at
  the point by [the entry for #126](2026-10-25-routes-iii-touching.md), both of 25 October
  2026; this entry approves only what the terms list and the front page say of them.

  Five meanings change with it:

  - `touching-whole-circles` names the reading of touching at the point of contact, which
    Heath prefers and which is defined beside ours, and III.13's companions, which prove
    the two readings agree for any two circles and any point. No statement reads
    differently, so that reading has no tag of its own.
  - `redundant-hypothesis` says what the entry on Euclid's idle hypotheses
    ([22 October 2026](2026-10-22-euclids-idle-hypotheses.md)) decided: the tag marks a
    hypothesis that our representation makes idle, and one Euclid's own argument leaves
    idle, as in III.8, stays untagged. It now marks as well a hypothesis idle for one
    clause of the conclusion, as the equal bases are for the measure clause of III.24's
    companion `Prop24.equalCircles`, where it asked that the whole conclusion hold without
    it. Its propositions are now III.24 and III.27, where they were III.24, III.26 and
    III.27.
  - `angle-measure` adds III.20's companion `Prop20.circumference`, which proves that a
    circumference's measure is its angle at the centre.
  - `mixed-angles-local` adds III.18, whose companions carry the angle of contact.
  - `segment-with-circle` lists every proposition whose record carries it, III.23 to
    III.25, III.30, III.33 and III.34, where it listed III.24 and III.25 alone.

  Book III's front page now says the same of Definition III.3: its row names the reading at
  the point, `TouchesInternallyAt`, `TouchesExternallyAt` and `CirclesTouchAt`, and the
  companions of III.13 that prove it equivalent to ours. The renderer writes those
  sentences only when facts.json holds the three definitions and the three companions.

  This entry approves the change to `review/terms.toml`: the new tag `angle-at-centre`,
  and the meanings of `touching-whole-circles`, `redundant-hypothesis`, `angle-measure`,
  `mixed-angles-local` and `segment-with-circle`.

  This entry approves the change to `scripts/render.py`: in `content_wording_at`, the
  `at_point` test and its added sentences for Definition III.3 on Book III's front page.
