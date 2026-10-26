- **S12 judges Book I's front page (tooling,
  [#479](https://github.com/jackChallis/stoicheia/issues/479)).** The coordinator's orders
  of 25 October 2026 ask that `book/I/front.md` leave `REACH_PENDING` once card #479 has
  mended its table of definitions. `REACH_PENDING` in `scripts/check_style.py` holds a
  file that had findings of a rule's new reach on 19 October: while it is listed, those
  findings are reported rather than failed, and once the file is mended a change to the
  check takes it out; Book I's front page was held for S12, since `FRONT_LEAN_I` in
  `scripts/render.py` named `Circumference.semicircle` without its `BookIII.` namespace.
  The change that mended the page ([its entry](2026-10-25-book-i-front-definitions.md))
  lands first, and the check reports the page done, with no finding of S12 left. A check
  is never changed with the content it judges, so this change of its own takes the page
  and its comment out of `REACH_PENDING`, and S12 now fails any finding on it, as on the
  front pages of Books II and III. It only tightens the check: nothing is loosened, and no
  page, record or Lean file changes.

  This entry approves the change to `scripts/check_style.py`: `book/I/front.md` and its
  comment taken out of `REACH_PENDING`.
