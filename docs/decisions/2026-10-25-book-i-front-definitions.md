- **Book I's front page names for each definition only what the Lean represents (tooling,
  [#479](https://github.com/jackChallis/stoicheia/issues/479)).** The coordinator's orders
  of 25 October 2026 assign card #479, which blocks the release, to this change, a check
  train of its own. The table of definitions on [Book I's front page](../../book/I/front.md)
  comes from `FRONT_LEAN_I` in `scripts/render.py`, and several of its rows said more than
  the Lean holds. Definitions I.2 and I.3 were given `Line`, but Euclid's line is any
  breadthless length, curved or straight, and our `Line` is a whole straight line
  (`Elements/Foundations/Words.lean`). The rows for I.14 and I.19 said that the Lean has no
  general word for a figure, overlooking `Figures.Outline`, a figure given by its straight
  sides with one boundary or more, and `Rectilineal` and `Apart`, a figure given with its
  triangles; and they listed `quadArea`, an area, as a figure, as the row for I.22 did for
  a trapezium. The rows for I.17 and I.18 named `Circumference.semicircle` without its
  `BookIII.` namespace, the finding of S12 that `REACH_PENDING` in
  `scripts/check_style.py` held back on that page.

  Now I.2 and I.3 say "none", each noting that `Line` is the straight line of Definition
  I.4, and I.3 adds how a finite straight line is given, by its ends. I.14 names
  `Figures.Outline`, then `Circle` and a segment by its arc (`Arc`) for figures with a
  curved boundary, and says that no Lean word is every figure. I.19 names
  `Figures.Outline`, `Rectilineal` and `Apart`, and `Triangle` for the trilateral, and says
  that quadrilaterals and multilaterals have no word of their own, `quadArea` being the
  area of a four-sided figure. I.22's trapezium is "none", measured in I.35 by `quadArea`;
  I.17's parallelogram is cut by its diameter into two triangles whose areas together are
  `quadArea A B C D`; and I.17 and I.18 write `BookIII.Circumference.semicircle`.
  `book/I/front.md` is rendered again, and it leaves `REACH_PENDING`, so S12 now judges it
  as it judges every page; it passes.

  The change tightens S12's reach by one page and loosens nothing: no check, test,
  expected value or lock is weakened, and no record, Lean file, mishnah or figure changes.

  This entry approves the change to `scripts/render.py`: the rows for Definitions I.2,
  I.3, I.14, I.17, I.18, I.19 and I.22 in `FRONT_LEAN_I`.

  This entry approves the change to `scripts/check_style.py`: `book/I/front.md` and its
  comment taken out of `REACH_PENDING`.
