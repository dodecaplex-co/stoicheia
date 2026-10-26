- **Book I's front page names for each definition only what the Lean represents (tooling,
  [#479](https://github.com/jackChallis/stoicheia/issues/479)).** The coordinator's orders
  of 25 October 2026 assign card #479, which blocks the release, to this change, a train
  of its own. The table of definitions on [Book I's front page](../../book/I/front.md)
  comes from `FRONT_LEAN_I` in `scripts/render.py`, and several of its rows said more than
  the Lean holds, or less. It corrects the rows given by the entry "Book I's definitions
  map, from Argon's second review"
  ([#64](https://github.com/jackChallis/stoicheia/issues/64)) in [the decisions
  record](../briefs/0002-decisions.md): those for I.2, I.3 and I.14, and the namespace in
  I.17 and I.18, as [the second read-through](../reports/read-through-02.md) found, and
  the rest as this change's review found.

  Definitions I.2 and I.3 were given `Line`, but Euclid's line is any breadthless length,
  curved or straight, and our `Line` is a whole straight line
  (`Elements/Foundations/Words.lean`). The row for I.14 said that the Lean has no general
  word for a figure, and the row for I.19 gave none for a rectilineal figure, overlooking
  `Figures.Outline`, a figure given by its straight sides with one boundary or more, and
  `Rectilineal` and `Apart`, a figure given with its triangles; and both, with the row for
  I.22's trapezium, listed `quadArea`, an area, as a figure. The page says above the table
  that words with no Lean partner are never used in a Lean proof, which was untrue of
  I.13's boundary, which `Figures.Outline.Boundary` gives in the proofs for I.45 and
  II.14. I.8 gave the plane angle only the rectilineal `∠ A B C`, where the Lean has
  `MixedAngle` too, and I.18 left out `Arc.Semicircle`, which "III.25 kind" states. The
  rows for I.17 and I.18 named `Circumference.semicircle` without its `BookIII.`
  namespace, the finding of S12 that `REACH_PENDING` in `scripts/check_style.py` holds
  back on that page.

  Now I.2 and I.3 say "none" for a line in general, as the card asks, and name the kinds
  of line the Lean has, so that the sentence above the table stays true: I.2 `Line`, the
  straight line of Definition I.4, and, of curved lines, the circumference of a circle and
  its arcs; I.3 `Line`, whole and without ends, and a finite straight line AB, given by
  its ends. I.8 names `∠ A B C`, the rectilineal angle, and `MixedAngle`, and says that no
  Lean word is every plane angle. I.13 names `Figures.Outline.Boundary`. I.14 names
  `Figures.Outline` and `Apart`, then `Circle` and a segment by its arc (`Arc`) for
  figures with a curved boundary, and says that no Lean word is every figure. I.18 names
  `Arc.Semicircle`. I.19 names `Figures.Outline`, `Rectilineal` and `Apart`, and
  `Triangle` for the trilateral, and says that quadrilaterals and multilaterals have no
  word of their own: each is a `Figures.Outline`, and `quadArea` measures a four-sided
  figure by its two triangles. I.22's trapezium is given by its area alone, `quadArea`, as
  I.35 uses it. I.17's parallelogram is cut by its diameter into two triangles whose areas
  together are `quadArea A B C D`, and I.17 and I.18 write
  `BookIII.Circumference.semicircle`. `book/I/front.md` is rendered again; S12 now finds
  nothing on it, and a check change of its own, after this one, takes it out of
  `REACH_PENDING`. The docstring of `Line` in `Elements/Foundations/Words.lean` still
  heads it "(Defs. 2–4)"; the foundations are the coordinator's, and the change is asked
  of them.

  The change is to what `render.py` writes, and to nothing it accepts or checks: no check,
  test, expected value or lock changes, and no record, Lean file, mishnah or figure.

  This entry approves the change to `scripts/render.py`: the rows for Definitions I.2,
  I.3, I.8, I.13, I.14, I.17, I.18, I.19 and I.22 in `FRONT_LEAN_I`, and the comment above
  `FRONT_UNUSED`.
