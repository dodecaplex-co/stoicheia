- **The angle at the centre gets a tag of its own, and five meanings in the terms list are
  made true (checks, [#524](https://github.com/dodecaplex-co/stoicheia/issues/524),
  [#370](https://github.com/dodecaplex-co/stoicheia/issues/370)).** Book III's reviews of
  26 October 2026 found that the terms the review records use left out a reading of ours
  and listed propositions wrongly. This change answers them, in two pull requests: this
  one, to the terms list and the renderer, lands first; III.20's record, which takes up the
  new tag, and the guide's row that names it follow, because a check input changed with
  the record it judges is refused at landing.

  III.20 reads the angle at the centre as `angleAtCentre`, the angles BEF and FEC
  together, so that it may be two right angles or more. That reading is ours, made after
  Heath's notes on III.20 and III.21, and until now the record had no tag to say so. The
  new tag, `angle-at-centre`, is a representation with no badge, for on Euclid's own
  figures the angle it names is his angle BEC.

  Five meanings change with it:

  - `touching-whole-circles` names the reading of touching at the point of contact, which
    Heath prefers and which is defined beside ours, and III.13's companions, which prove
    the two readings agree for any two circles and any point. No statement reads
    differently, so that reading has no tag of its own.
  - `redundant-hypothesis` says what the entry on Euclid's idle hypotheses
    ([22 October 2026](2026-10-22-euclids-idle-hypotheses.md)) decided: the tag marks a
    hypothesis that our representation makes idle, and one Euclid's own argument leaves
    idle, as in III.8, stays untagged. Its propositions are now III.24 and III.27.
  - `angle-measure` adds III.20's companion `Prop20.circumference`, which proves that a
    circumference's measure is its angle at the centre.
  - `mixed-angles-local` adds III.18, whose companions carry the angle of contact.
  - `segment-with-circle` names the propositions given a segment: III.23 to III.25,
    III.30, III.33 and III.34.

  Book III's front page now says the same of Definition III.3: its row names the reading at
  the point, `TouchesInternallyAt`, `TouchesExternallyAt` and `CirclesTouchAt`, and the
  companions of III.13 that prove it equivalent to ours. The renderer writes those
  sentences only when the three definitions and the three companions are all present.

  This entry approves the change to `review/terms.toml`: the new tag `angle-at-centre`,
  and the meanings of `touching-whole-circles`, `redundant-hypothesis`, `angle-measure`,
  `mixed-angles-local` and `segment-with-circle`.

  This entry approves the change to `scripts/render.py`: in `content_wording_at`, the test
  `at_point` and the sentences it adds to the row of Definition III.3 on Book III's front
  page.
