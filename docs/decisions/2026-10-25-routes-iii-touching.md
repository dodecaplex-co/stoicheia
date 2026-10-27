- **Definition III.3 read at the point of contact moved into `Elements/` (Book III, #126).**
  On 25 October 2026 the owner chose, of the options put to them (the coordinator's
  decisions-waiting item 15), "A": to approve the three drafts of Euclid's routes in Book
  III, #126, #129 and #130, as they stand. The coordinator's record of that ruling is on
  #126 and #332, as it is on #129 and #130. The
  [entry of the same day for #130](2026-10-25-routes-iii-contact.md) moved #130's draft;
  this one moves #126's.

  Under that approval, and as part of #332, the four definitions of the staged
  `Staging/Routes/Touching.lean` go into the foundations' definitions of Book III, beside
  the whole-circle contact, in the namespace `Elements`: `Touching.Near`,
  `TouchesInternallyAt`, `TouchesExternallyAt` and `CirclesTouchAt`, their bodies, binder
  names and docstrings as staged, save two changes made in review to the docstring of
  `Touching.Near`: an added sentence, saying that it is `Surrounds p C`, its arguments in
  the other order (Lean accepts the two as equal by `rfl`), and its pointer to
  `LocallyWithin`, which now says "below" where it named the file; the module text of
  that file gains a clause naming
  the reading at the point among its words. The fourteen theorems go into
  [Elements/BookIII/Prop13.lean](../../Elements/BookIII/Prop13.lean), after III.13's proof,
  in the namespace `Elements.BookIII`, their statements as staged. Before the staged copy
  was deleted, Lean compared every moved type, and every moved definition's value, with
  the staged one, the staged names read as the moved ones, binder names and universe
  parameters included, and found all eighteen the same, and their docstrings too, before
  those two changes. The three
  agreements become companions of III.13, named by FORMALIZATION's rule for companions
  `Prop13.touchesInternally_iff`, `Prop13.touchesExternally_iff` and
  `Prop13.circlesTouch_iff`, listed in `Elements/Companions.lean` and certified as "III.13
  touchesInternally_iff", "III.13 touchesExternally_iff" and "III.13 circlesTouch_iff". The
  other eleven are steps, and keep their staged names under `Elements.BookIII`
  (`Touching.small`, `TouchesInternallyAt.between` and the rest). The staged agreements for
  contact within and without each paired two of those steps, one for each way, and so came
  down to helpers alone, which `scripts/sweep_citations.py` lists and FORMALIZATION,
  section 5, has fixed rather than declared; each agreement's proof now carries both ways
  itself, and the four steps for the ways, `TouchesInternallyAt.of_whole`,
  `TouchesInternallyAt.whole` and their counterparts for contact without, keep their
  statements and docstrings and follow the agreements, cited from them. Two of the steps,
  `TouchesInternallyAt.between` and `TouchesExternallyAt.between`, reach the conclusions of
  III.11 and III.12 by a route that is not Euclid's; they come after III.13 and cite
  neither, and the overlap catalogue,
  [docs/reports/overlaps.md](../reports/overlaps.md), gains a dated entry among its near
  misses that says so. Two of that report's sentences which this move makes untrue are
  corrected with it: the number of files left in `Staging/Routes/`, and the remark under
  III.6 that agreement with Heath's reading at the contact is not established. Book III's
  brief, [docs/briefs/0004-book-III.md](../briefs/0004-book-III.md), keeps its dated
  sentence of 19 October that contact read at the point has not been formalised, and gains
  a dated note below it saying that the sentence is overtaken.

  No staged theorem's statement is a fact already in `Elements/`, as Lean confirmed: the
  four copies the staged file once held left it at 4a6d9a49, and the five facts it shares
  with the mixed angles and Book Zero are cited from their homes. `Prop13.lean` now
  imports I.20, I.24 and the mixed angles' shared module, none later than III.13, and
  nothing beneath the moved theorems rests on Circle 2 or Circle 3 or reaches a
  proposition after III.13. The staged file is deleted, and `Staging.lean` no longer
  imports it, so `Staging/Routes/` holds #129's files alone. III.13's review record names
  the three companions, with notes on its statement, its route and its representation, and
  its mishnah gains a paragraph on them. III.11's mishnah now says that the reading at the
  point is formalised, and III.11's record gave up its verdicts on commentary and sign-off
  with that sentence until it was read again. An independent reader who wrote neither
  then read both records in full against `d87e0632f`, and both were
  stamped in this train, every applicable verdict passing, III.11's on representations
  being `n/a`. The report,
  [docs/reports/routes-book-III.md](../reports/routes-book-III.md), records the move in an
  addendum of this date.

  The coordinator, owner of the foundations, ordered on 25 October 2026 that these four
  definitions enter `Elements/Foundations/DefinitionsIII.lean`, and those orders are this
  train's authority to change that file.
  `Certificate/axioms.lock` is written again here by its own tool,
  `check_fidelity.py --write-lock`, on the approval the coordinator gave in those orders as
  the lock's owner for these four words alone: its vocabulary grows from 263 words to 267,
  and its 48 axioms are left as they were.
  `Certificate/FIELDS.md` differs only in its generated count of that vocabulary, 263 now
  267.
  `model/lock.sha256` takes the new lock's sha256,
  9dbedf61bac8740ae5da9818b3af0f675839bd5b2715b0cc4f165bcbb83983f3, under a note dated
  25 October 2026 explaining that no law of the formal model reaches the four words; the
  generator `Check/Write.lean` then wrote `model/Model/Laws.lean` afresh, the line that
  records the lock's hash being its one change, and the model builds.
  `tests/model/lock.sha256`, the numerical harness's hash, takes that same new value under
  a dated note of its own, since only the statements of III.13's companions use the four
  words and none of the harness's laws changes.
