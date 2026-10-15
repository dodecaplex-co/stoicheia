# First mate: the statements of I.25–I.32, and Book Zero for parallels (15 October 2026)

Getting ready for the third voyage, which sends sailors to I.25–I.32, the stretch
where the parallel postulate enters. Claude sailors and OpenAI Codex sailors sail
at once, on one set of [sailing orders](orders-03.md). Three jobs: read the
statements of I.25–I.32 once more against Heath and against every later
proposition that leans on them; give Book Zero the facts about parallels that
every proof from I.27 on will need; and write the orders.

## The statements of I.25–I.32

**No statement changed.** For each proposition: does the Lean say what Euclid's
enunciation and his "I say that" say, in Heath's letters? Is it true, with nothing
false in a degenerate case? And can every later proposition that cites it apply it?
To be sure of the last, I wrote proofs against the statements as they stand, in a
scratch file that is not committed: I.27, I.29 and I.31 in full, the second half of
I.28, I.32 up to its last line of arithmetic, and Euclid's own case of I.30 (with
its side facts left open).

| Prop | Verdict |
|---|---|
| I.25 | OK. I.4, and I.24 with the triangles exchanged, give it at once. Not cited again in Book I. |
| I.26 | OK. Both of Euclid's cases in one statement: the equal side is `BC`, adjoining the equal angles, or `AB`, subtending the angle at `C`. Fits I.34, which applies it to the triangles `ABC`, `DCB` with `BC` common. |
| I.27 | OK. `E` between `A` and `B`, `F` between `C` and `D`, and `A`, `D` on opposite sides of `EF`: the alternate angles. Nothing degenerate slips through: `OppositeSidesOf` makes `E` and `F` different and keeps `A` off `EF`, so `AB` and `CD` are different straight lines. Fits I.28 and I.31 as they stand; I.33, whose straight line falls at the ends `C` and `B`, produces `AC` and `DB` first. |
| I.28 | OK. Heath's figure exactly, with the two conditions joined by "or". Not cited again in Book I. |
| I.29 | OK. Heath's figure exactly: `EF` falls on `AB`, `CD` at `G` and `H`, with `G` between `A` and `B`, `H` between `C` and `D`, `E`, `G`, `H`, `F` in that order, and `B`, `D` on one side of `EF`; the three conclusions are his three. Its later citations (I.30, I.32, I.33, I.34, I.35, I.44, I.45, I.46) have a straight line falling on two parallels at points already named, mostly ends, with no room on either side. Rather than loosen the statement and lose Heath's figure, Book Zero now draws that figure for them, and a citation of I.29 takes two lines. |
| I.30 | OK, and the hardest of the voyage. As general as the enunciation, with `C` off `AB` so that `AB` and `CD` are two straight lines (without it the statement is false). Euclid's figure puts `EF` between the other two; see the note for the sailors below. Fits I.45, its one later citation in Book I, where `HG` does lie between `FK` and `ML`. |
| I.31 | OK. Fits I.32, where one of the two points it gives lies on `A`'s side of `BC`. I.37–I.46 go on to find where the parallel meets some other straight line; that is their business (see "Looking ahead"). |
| I.32 | OK. Both conclusions: the exterior angle `ACD`, and the three angles. Not cited again in Book I. |

**Postulate 5 fits I.29.** `Postulate5` asks for straight lines `L` through `A`,
`B`, `M` through `B`, `C` and `N` through `C`, `D`, with `A`, `D` on one side of `M`
and `∠ A B C + ∠ B C D < ∟ + ∟`, and gives a point of `L` and `N` on `A`'s side. In
I.29, with `B`, `G`, `H`, `D` for its `A`, `B`, `C`, `D`, that is Euclid's step word
for word: the angles `BGH`, `GHD` are less than two right angles, so `AB`, `CD`
meet. When the angle `GHD` is the greater, which Euclid leaves aside, the same
step runs on `A`'s side, with I.13 at `H`. It is also the form I.44 will want,
where Euclid cites the postulate himself.

**The phrases fit.** `AreParallel A B C D` is Definition 23 said of the whole
straight lines through `A`, `B` and through `C`, `D`; `Parallelogram A B C D` is `AB`
parallel to `CD` and `BC` to `DA`. With Book Zero's new symmetries both turn round
easily: I.34's parallelogram `ACDB` gives "AB is parallel to CD" as
`h.2.symm.swap_left`.

## Book Zero

A new file, `Elements/Figure/Parallels.lean`, and a few companions in `Sides.lean`
and `Rays.lean`. None of them uses Postulate 5: they say only what "do not meet"
means, read with System E's rules for sides. `Basics.lean` lists the new file.

| Lemma | File | What Euclid takes for granted |
|---|---|---|
| `Parallel.symm`, `AreParallel.symm`, `.swap_left`, `.swap_right` | Parallels | "AB is parallel to CD" either way round |
| `AreParallel.parallel`, `AreParallel.of_parallel` | Parallels | the same, of any two other points of the same straight lines; the bridge to `Parallel L M` |
| `Parallel.not_onLine`, `Parallel.of_not_meet`, `AreParallel.of_not_meet` | Parallels | parallels do not meet; straight lines which do not meet are parallel (Def. 23, as I.27 cites it) |
| `Parallel.off_transversal` | Parallels | a straight line falling on two parallels meets each in one point |
| `Parallel.sameSide`, `AreParallel.sameSideOf`, `AreParallel.triangle` | Parallels | one parallel lies wholly on one side of the other; an end of one is off the other |
| `AreParallel.oppositeSidesOf` | Parallels | a straight line joining two parallels "in the same directions" (I.33) has their other ends on either side of it; from `crossbar` |
| `AreParallel.figure_alternate`, `AreParallel.figure_interior` | Parallels | the figure of I.29, drawn about any straight line falling on two parallels |
| `SameSideOf.inner` | Sides | the straight line `EF` is the straight line `GH` |
| `SameSideOf.oppositeSidesOf_of_between`, `OppositeSidesOf.sameSideOf_of_between` | Sides | where alternate angles lie |
| `OppositeSides.exists_between` | Sides | a straight line joining points on opposite sides of `L` crosses it between them (it was inside `crossbar`) |
| `OnRay.between` | Rays | a point of the ray from `B` through `E` lies beyond `B` from `C` when `E` does (the same as `Prop14.straight`) |
| `OnRay.of_between_between` | Rays | two points beyond `C` from `B` lie on one ray from `C` |

How to cite I.29 with the figure lemmas, when `hpar : AreParallel P G H Q` and `P`,
`Q` lie on opposite sides of `GH`:

```lean
obtain ⟨B, C, E, F, hPGB, hCHQ, hEGH, hGHF, hpar', hBQ⟩ := hpar.figure_alternate hPQ
have hPGH : ∠ P G H = ∠ G H Q := (Prop29 hpar' hPGB hCHQ hEGH hGHF hBQ).1
```

With `P` and `Q` on one side of `GH` and `hpar : AreParallel G P H Q`,
`figure_interior` gives `∠ P G H + ∠ G H Q = ∟ + ∟` as the third conclusion, and
the exterior angle `EGP` as the second, with `E` beyond `G` from `H`
(`OnRay.of_between_between` moves `E` onto a point already named).

## The sketch of I.30

`Prop30.lean` now imports I.27, for Euclid's last step, "and they are alternate.
Therefore AB is parallel to CD", which cites it without a bracket; its module note
says so. No statement and no `--` line changed.

## For the sailors

- **I.25.** `lt_trichotomy` gives Euclid's three cases. Equal: I.4 makes `BC`
  equal to `EF`. Less: I.24, with `DEF` as its first triangle, makes `BC` less
  than `EF`.
- **I.26.** "Let BG be made equal to DE": `OnRay.exists_len_eq` and
  `OnRay.between_of_len_lt` do it without I.3, which Euclid doesn't bracket. "Let AB
  be greater": the other case is the same argument with the triangles exchanged,
  so write it once for any two triangles (an inner `have`, like I.16's `greater`)
  and use it twice. "The less to the greater" is `angle_lt_of_between`. In the
  second part, I.16 is applied to the triangle `AHC` with `CH` produced to `B`.
- **I.27.** Under "[Def. 23]", `AreParallel.of_not_meet`, and take the meeting
  point `G`. It is off `EF`, on `B`'s side or on `A`'s (`same_side_or`). On `B`'s
  side, `OnRay.of_sameSideOf` puts it on the rays `EB` and `FD`, `OnRay.between`
  puts `E` between `A` and `G`, and I.16 in the triangle `GEF` does the rest. The
  scratch proof took about fifty lines and no helpers.
- **I.28.** `SameSideOf.inner` turns "on one side of EF" into "of GH", and
  `SameSideOf.oppositeSidesOf_of_between` gives the alternate sides I.27 asks for.
  "Let the angle BGH be subtracted from each" is `CommonNotion3`.
- **I.29.** Postulate 5 comes in here and nowhere earlier. "They do not meet" is
  `Parallel.not_onLine`. Euclid takes the angle `AGH` greater; when `GHD` is the
  greater, the same argument runs on the side of `A` and `C` (I.13 at `H`), and a
  remark should say so. Heath's long note on Postulate 5 (vol. 1, pp. 202–220) is
  quoted once, where it matters most, and this is the page; but Proclus' "This
  ought even to be struck out of the Postulates altogether" (p. 202) is already
  quoted on I.17.
- **I.30.** Euclid's figure has `EF` between `AB` and `CD`, and his `GK` falls on all
  three. The statement is general, so `EF` may lie outside the other two, and then
  nothing short of the theorem makes `GK` meet `EF`. A shape that works: prove
  Euclid's case along his words (`G` between `A` and `B`, `K` between `C` and `D`, on
  opposite sides of `EF`; `OppositeSides.exists_between` gives `H`; I.29 twice with
  the figure lemmas, the second time for the exterior angle; then I.27). Write it
  once over any letters, as I.16 does, since the given letters need not sit as
  Heath's do (`A` and `F` on opposite sides of `GK`). For the other arrangement a
  helper is welcome, for instance that two straight lines through one point, both
  parallel to a third, are one straight line (I.29 and `onRay_of_angle_eq`). That is
  "Playfair's" axiom: Heath discusses it under I.29, and reports under I.31 that
  Proclus draws it from I.30. Refer to those notes in a clause, without quoting
  them.
- **I.31.** "Let a point D be taken at random on BC": take it between `B` and `C`
  (`exists_point_between`), so that `B` and `C` lie on opposite sides of `AD`. I.23,
  with its given point at `B`, then builds `E` on the far side of `AD` from `C`, and
  I.27 applies to `E`, `A`, `F` and `B`, `D`, `C` as they stand. The scratch proof
  was a dozen lines.
- **I.32.** I.31 gives the parallel through `C`, with `C` between two of its points;
  take as `E` the one on `A`'s side of `BC`. `AreParallel.oppositeSidesOf` puts `E`
  on the other side of `AC` from `B`. "AC has fallen upon them" is
  `figure_alternate`, and I.29's first conclusion is then `∠ B A C = ∠ A C E`, as
  Euclid says it. "BD has fallen upon them" is `figure_interior` and I.29's exterior
  angle. "The whole angle ACD" is `angle_add_of_within`, with `E` within the angle
  `ACD`.

## Looking ahead

- I.37–I.46 each draw a parallel through a point [I. 31] and then take the point
  where it meets some other straight line: `E`, `F` on `AD` produced in I.37, `E`
  on `BD` in I.39, `G` in I.42, `H` in I.44, `E` in I.46. That a straight line
  meeting one of two parallels meets the other is "Playfair's" axiom, which needs
  Postulate 5. It wants a shared lemma citing I.29 (or I.30) before that voyage.
  It cannot go in Book Zero, which cites no proposition, nor in `Helpers.lean`,
  which earlier propositions import; a file of its own after I.30 would do. If the I.30 sailor
  writes the uniqueness helper, it is the natural seed.
- Small lemmas for `Parallelogram` (its four sides, named from another corner)
  will help I.34 onwards.
- `Prop14.straight` restates `OnRay.between`. It was left in place because the
  mishnah of I.14 names it; I.14 can cite Book Zero when that mishnah is next
  touched.

## Housekeeping

- `lake build`, `lake env lean Certificate/Facts.lean` and
  `python3 scripts/check_fidelity.py` all pass, and `facts.json` comes out
  unchanged. The generated files are left for the captain.
- `scripts/scaffold_book.py` needed no change: no statement changed, and all 48 of
  its statements match the Lean files.
