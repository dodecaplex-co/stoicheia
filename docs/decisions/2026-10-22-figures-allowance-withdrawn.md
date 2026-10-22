- **The acceptance allowance for I.45 and II.14 is withdrawn (#116).**
  Approval 6 of [brief 0013](../briefs/0013-figures.md), listed in its section 10 under
  "What remains for #116: the owner's approvals", withdraws the allowance by which P3 of
  [ACCEPTANCE](../ACCEPTANCE.md) let I.45 and II.14 stand as restricted statements, and
  asks that this be done in a change to the check of its own. The owner answered those
  approvals on the morning of 22 October 2026, about 06:40, in these words: "as propose
  1-6,8 as is. 7 with amendment." The coordinator records them in
  [#116's comment of that morning](https://github.com/jackChallis/stoicheia/issues/116#issuecomment-6342080363),
  and this entry claims no more than those words and that record give. The change before
  this one returned both records to `full`, through their outline companions, so neither
  rests on the allowance; once it is gone, a restricted or partial statement of either
  fails P3, as does any limitation that ACCEPTANCE's table leaves out.

  This entry approves the change to `scripts/check_acceptance.py`, in which the two
  entries of `ALLOWED_LIMITS` for I.45 and II.14 are withdrawn, together with their
  comment on the interim decision of 20 October 2026; the entries for III.16 and III.31
  stay, and nothing else in the script differs.

  This entry approves the change to `tests/test_acceptance_limits.py`, whose expectations
  are brought to the withdrawal with every case of P3 still covered: the list it expects
  holds III.16 and III.31 alone; a restricted or partial I.45 or II.14 now fails, whatever
  its tags; a full statement passes, tagged or not; the allowed limitation passes and
  fails, by its tag and its scope, through III.16 and III.31; and an alternative route
  still fails.

  With them, ACCEPTANCE's item B4 now says that I.45 and II.14 are full, and its table of
  the limitations allowed loses their two rows and the paragraph that followed it.

  This entry approves the change to `review/terms.toml`, where the meaning of the tag
  `figure-with-dissection` now names the older companions of I.45 and II.14, which take a
  figure given with a checked division into triangles, and no longer says that a figure's
  division, or the independence of its area, is unproved: Book Zero, promoted before this change, proves both, the independence after
  David Hilbert's theory of content.
