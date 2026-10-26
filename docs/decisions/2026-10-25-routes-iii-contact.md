- **The three drafts of Euclid's routes in Book III approved, and the angle of contact after
  III.18 moved into `Elements/` (Book III, #130).** On 25 October 2026 the owner chose, of
  the options put to them in item 15 of the coordinator's decisions waiting, "A": to
  approve the three drafts of Euclid's routes in Book III, #126, #129 and #130, as they
  stand. The coordinator's record of that ruling is on #130 and #332. It gives the approval
  that the [routes entry of 21 October 2026](2026-10-21-routes-book-iii.md) left to the
  owner, for the reading of Definition III.3 at the point of contact (#126), for the angle
  at the centre of any size and III.20 for it (#129), and for III.16's comparisons carried
  by III.18 to every straight line touching a circle (#130).

  Under that approval, and as part of #332, this train moves #130's draft. The seven
  theorems of `Staging/Routes/AngleOfContact.lean` go into `Elements/BookIII/Prop18.lean`,
  after III.18's proof, in the namespace `Elements.BookIII`: the three steps
  `Prop18.diameter`, `Prop18.parts` and `Prop18.branch`, and the four statements
  `Prop18.contact_locallyEqual`, `Prop18.contact_lt`, `Prop18.semicircle_gt` and
  `Prop18.acute`. Their statements are as staged, hypothesis names included, which Lean
  confirmed by comparing each moved type with the staged one before the staged copy was
  deleted; only the namespace changes. Their docstrings and remarks come with them, revised
  only where a sentence spoke of staging or approval. `Prop18.lean` now imports I.23, III.16
  and the mixed angles' shared module, none later than III.18.

  The four statements become companions of III.18, listed in `Elements/Companions.lean`
  and certified as "III.18 contact_locallyEqual", "III.18 contact_lt", "III.18
  semicircle_gt" and "III.18 acute"; the three steps are not companions. The staged file is
  deleted and `Staging.lean` no longer imports it, so `Staging/Routes/` holds #126's and
  #129's files alone, which wait for a move of their own. III.18's review record names the
  companions and gains a route note and the representation tag `mixed-angles-local`, and
  its mishnah a paragraph on them; the record is to be read again by a reader who did not
  write it, and stamped then. The report,
  [docs/reports/routes-book-III.md](../reports/routes-book-III.md), records the move in an
  addendum of this date.
