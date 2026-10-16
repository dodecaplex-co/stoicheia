# First mate: the statements of I.33–I.48, Book Zero for areas, and the shared steps (15 October 2026)

Getting ready for the fourth voyage, which sends sixteen sailors, two crews of
Claude and two of OpenAI Codex, to I.33–I.48 all at once, and finishes Book I.
Three jobs: read the statements once more against Heath and against every later
proposition that leans on them; give Book Zero the facts about areas and
parallelograms that the area section needs, and gather the steps that cite a
proposition into one shared file; and write the [sailing orders](orders-04.md).

Everything below builds: `lake build`, `lake env lean Certificate/Facts.lean` and
`python3 scripts/check_fidelity.py` pass, `facts.json` comes out unchanged, and
nothing before I.29 rests on Postulate 5. The generated files are left for the
captain.

## The statements of I.33–I.48

**Two statements changed (I.38 and I.48); the other fourteen stand.** To be sure
of them I wrote proofs against the statements, in scratch files that are not
committed: I.38, I.42, I.36 and I.48 in full; Euclid's case of I.35 in full; and
the area reckoning of I.43. Each closed with no `sorry` but the cited
propositions' own.

| Prop | Verdict |
|---|---|
| I.33 | OK. `SameSideOf B D A C` is "in the same directions"; `AreParallel.oppositeSidesOf` turns it into the alternate sides I.29 wants. Fits I.36 and I.45. |
| I.34 | OK. Its last conclusion is the bisection; `Prop34.bisect` (new, after `Prop34`) says it of `quadArea`. |
| I.35 | OK, and the hardest of the voyage. General, as Euclid's enunciation is, and I.36 and I.37 need it so: I.37's parallelograms `EBCA`, `DBCF` and I.36's second citation (base `EH`) fall in any arrangement. Euclid proves one case (`D` between `A` and `E`); see the note for the sailors. |
| I.36 | OK. The two parallelograms may be lettered round opposite ways; one case split (`AreParallel.sameSideOf_or`) gives Euclid's case or its mirror. Proved in scratch, 40 lines. |
| I.37 | OK. Needs `A ≠ D`, which I.39 and I.41 can meet (where their `E` is `A` the two triangles are one). |
| **I.38** | **Changed**: below. |
| I.39, I.40 | OK. |
| I.41 | OK. Fits I.42 (`FECG`, with `A` on `FG`) and both citations in I.47. |
| I.42 | OK, unchanged. See "I.42 and I.44" below. |
| I.43 | OK. Every quadrilateral in it is a parallelogram, so the diameter `quadArea` takes does not matter; the complements `EBGK`, `HKFD` are parallelograms by I.30. Its hypotheses are exactly the figure I.44 builds. |
| I.44 | OK, unchanged; Euclid's "let it be placed" is carried out by a new helper, `Prop44.place`. |
| I.45 | OK. "The rectilineal figure ABCD" is the triangles `ABD`, `DBC` on Euclid's diameter `DB`: `△ A B D + △ D B C`, which is its area whichever way the figure turns (`quadArea A B C D` would use `AC`, wrong for a figure re-entrant at `B` or `D`). |
| I.46 | OK. Its corollaries `Prop46.square_eq`, `Prop46.side_eq` are new (below). |
| I.47 | OK. Each square is outward, as Euclid's proof needs (I.14 puts `C`, `A`, `G` on one straight line). |
| **I.48** | **Changed**: below. |

### I.38: two triangles may share their vertex

Before:

```lean
theorem Prop38 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hbase : ‖B C‖ = ‖E F‖)
    (hBF : ∃ L : Line, OnLine B L ∧ OnLine C L ∧ OnLine E L ∧ OnLine F L)
    (hpar : AreParallel A D B F) :
    △ A B C = △ D E F
```

After:

```lean
theorem Prop38 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hbase : ‖B C‖ = ‖E F‖)
    (hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧
      OnLine B M ∧ OnLine C M ∧ OnLine E M ∧ OnLine F M) :
    △ A B C = △ D E F
```

Why: I.42 cites I.38 for the triangles `ABE`, `AEC`, "on equal bases BE, EC and in
the same parallels BC, AG". Both have the vertex `A`, so `AreParallel A A B C`
would be needed, and that is false (`AreParallel` asks for two different points).
"In the same parallels" now says just that: two parallel straight lines, one
through both vertices and one through both bases. It also lets `B` be `F`. Tested:
I.38 along Euclid's route (I.31, I.36, I.34) and I.42 citing it, both in full.

### I.48: the squares are described on the sides

Before: `(hBC : Square B P Q C) (hBA : Square A B R S) (hAC : Square A C T U)`.
After: each square with its far corners on one side of its base,
`(hBC : Square B P Q C) (hPQ : SameSideOf P Q B C) (hBA : Square A B R S)
(hRS : SameSideOf R S A B) (hAC : Square A C T U) (hTU : SameSideOf T U A C)`.

Why: `Square` (Def. 22) asks for four equal sides and four right angles, but our
axioms do not settle the angle at a point lying between two others, so nothing
short of a long detour shows that four points meeting Def. 22 make a figure with
an inside. I.48 compares its given squares with those its proof describes (I.46),
which needs them to be genuine. "Described on BC" on either side is what Euclid
means; I.47 already asks for its squares outward. Tested: I.48 in full along
Euclid's route (I.11, I.46, I.47, I.8), with the two corollaries below.

`scripts/scaffold_book.py` carries both new statements.

## I.42 and I.44: "let it be placed"

I.44 begins: "Let the parallelogram BEFG be constructed equal to the triangle C, in
the angle EBG which is equal to D [I. 42]; let it be placed so that BE is in a
straight line with AB". Euclid moves the parallelogram. Strengthening I.42 to build
at a given point along a given ray, as I.22 and I.23 were, cannot be done along
Euclid's route: his I.42 puts the parallelogram on half of the triangle's own base,
at its middle point, and nowhere else. So I.42 stays, and the move goes where Euclid
makes it. `Prop44.place`, a helper before `Prop44`, proved: given any
parallelogram `PQRS` and a straight line `AB`, it produces `AB` to `E` and builds
`BEFG` with `BE`, `BG` equal to `QR`, `QP`, the angle `EBG` equal to `RQP`, `G` on a
chosen side, and the same area (I.2, I.23, I.31, `Prop30.meet`, I.4, I.34). The
sailor cites `Prop42` and then `Prop44.place` under that sentence.

A consequence for I.45: its "parallelogram FH ... [I. 42]" lies on the triangle
`ABD`'s own base, so in Lean its corner `H` is a corner of `ABD` (`D`, if the
triangle is given to I.42 as `ABD`). The figure follows the proof, and the mishnah
says so.

## I.46: squares on equal straight lines

Euclid assumes in I.48 that "the square on DA is also equal to the square on AB",
and conversely that equal squares have equal sides. Heath reports, under I.46, that
Proclus proves both. They live after `Prop46`, as its corollaries, and both are
proved: `Prop46.square_eq` (I.4 on the halves) and `Prop46.side_eq` (the square on
the less is described inside the square on the greater, and is less: I.3, I.46,
I.34). The second cites `Prop46` itself, so it waits on the I.46 sailor's proof.

## Book Zero

Two new files, gathered by `Basics.lean`; no proposition cited, no axiom added, no
Postulate 5.

| Lemma | File | What Euclid takes for granted |
|---|---|---|
| `Magnitude.instAssociative`, `.instCommutative` | Areas | adding in any order; lets `ac_rfl` close a sum of areas |
| `Magnitude.eq_of_add_self_eq`, `.add_self_lt_add_self` | Areas | the halves of equals are equal; the double of the less is less |
| `area_bca`, `area_cab`, `area_acb`, `area_bac`, `area_cba` | Areas | the triangle `ABC` named from any corner |
| `area_eq_zero_of_collinear`, `Triangle.area_pos` | Areas | three points on a line make no triangle; a triangle is something |
| `area_cut`, `area_lt_of_cut` | Areas | a straight line from a corner cuts a triangle into two which make up the whole (no non-collinearity needed); the part is less |
| `quadArea_reverse`, `quadArea_rotate₂` | Areas | the figure `ABCD` read backwards, or from `C`: same diameter |
| `quadArea_rotate_of_cross` | Areas | diameters that cross: either one measures the figure |
| `Parallelogram.rotate`, `.reverse`, `.triangle`, `.sameSideOf` | Parallelograms | a parallelogram named from any corner; its far side lies on one side of each side |
| `between_of_sameSide` | Parallelograms | a point of `AC` inside both parallels lies between `A` and `C` |
| `Between.of_sameSide`, `Parallel.between` | Parallelograms | parallels keep order: projected along parallels, a point between stays between |
| `AreParallel.cross_or`, `AreParallel.sameSideOf_or` | Parallelograms | a quadrilateral between two parallels has crossing diameters or crossing sides; which way the two parallels run |
| `SameSideOf.of_cross` | Parallelograms | crossing diameters: the far corners lie on one side of each side |
| `Parallelogram.cross`, `Parallelogram.quadArea_rotate` | Parallelograms | a parallelogram's diameters cross; either measures it |
| `quadArea_add_of_parallelograms` | Parallelograms | a parallelogram cut by a parallel is the two parallelograms (I.43, I.45, I.47) |
| `Square.rotate` | Parallelograms | a square named from the next corner |

## Shared steps that cite a proposition

`Helpers.lean` is imported by I.7, I.9, I.18, I.19, I.20 and I.24, so it cannot
import I.28–I.30. Its own docstring foresaw this: a later step needs "a file of its
own". That file is `Elements/BookI/HelpersParallels.lean`.

| Lemma | Cites | Use it for |
|---|---|---|
| `Prop29.alternate` | I.29 | alternate angles, `∠ P G H = ∠ G H Q`, from `AreParallel P G H Q` and `P`, `Q` on opposite sides of `GH` (I.33, I.34, I.45) |
| `Prop29.interior` | I.29 | interior angles on one side make two right angles (I.44, I.45, I.46) |
| `Prop29.exterior` | I.29 | exterior equal to interior and opposite (I.35) |
| `Prop30.meet` | I.30 | a straight line meeting one of two parallels meets the other: every point Euclid takes where a parallel he has drawn meets another straight line (I.37–I.47). Proclus' argument, as Heath reports it under I.31 |
| `Prop30.parallel` | I.30 | I.30 for named straight lines (I.43, I.44, I.45) |
| `Prop28.interior` | I.28 | two right angles on one side make parallels |
| `Prop28.square` | I.28 | a square whose far corners lie on one side of its base is a parallelogram (I.47, I.48, and I.46's corollaries) |

And `Prop34.bisect` (after `Prop34`): "the diameter bisects it", as
`quadArea A B C D = △ A B C + △ A B C`.

## For the sailors

- **I.33.** `hpar.oppositeSidesOf hdir` and `Prop29.alternate`; I.4 on `BAC`, `CDB`;
  for I.27 produce `AC` beyond `C` and `DB` beyond `B` first, then
  `AreParallel.of_parallel`.
- **I.34.** Two `Prop29.alternate`s (the sides of `BC` from the parallelogram:
  `Parallelogram.sameSideOf` and `AreParallel.oppositeSidesOf`), I.26, then
  `angle_add_of_within` for "the whole angle ABD". Keep `Prop34.bisect`.
- **I.35.** Write Euclid's case once (an inner `have`, `D` between `A` and `E`). His
  `G`: `AreParallel.cross_or` on `ED ∥ BC`; the disjunct where `EC` meets `BD` is
  impossible, as `E` and `B` lie on either side of `DC`. Then `E` lies between `D`
  and `F` (they are on either sides of `EB`); `Prop29.exterior` for "FDC ... EAB";
  I.4; `area_cut` four times, `CommonNotion3`, `ac_rfl`. The scratch proof was about
  90 lines. The rest, as Heath reports Proclus doing (vol. 1, p. 328): `E` between
  `A` and `D` (Proclus adds the triangles to the trapezium `EBCD`), `E` at `D`, and
  `E` at `A` (then `D` is `F`: `OnRay.eq_of_len_eq`). The mirror arrangements follow
  by exchanging the two parallelograms: `AreParallel.sameSideOf_or` on `AE ∥ BC`
  says which.
- **I.36.** Scratch proof: an inner `key` for `C`, `H` on one side of `BE` (I.34, I.33,
  I.35 twice, areas turned round with `quadArea_reverse` and
  `Parallelogram.quadArea_rotate`), then `AreParallel.sameSideOf_or` on `EH ∥ BC`,
  the second case with `EFGH` named `HGFE`.
- **I.37, I.38.** Through `B` the parallel to `CA` (I.31), then `Prop30.meet` with the
  straight line `AD` for `E`. `Prop34.bisect hEBCA.rotate` and
  `hEBCA.quadArea_rotate` halve by the diameter `AB`;
  `Magnitude.eq_of_add_self_eq` takes the halves. I.38 in scratch was 50 lines.
- **I.39, I.40.** `Classical.byContradiction`; the meeting point by `Prop30.meet`;
  it lies on the ray from `B` (or `E`) through `D` (`OnRay.of_sameSideOf`); then
  `area_lt_of_cut` for "the greater to the less".
- **I.41.** I.37 (when `E` is `A` there is nothing to prove), `Prop34.bisect`.
- **I.42.** Scratch proof, 60 lines: I.10, I.23 on `A`'s side, I.31 twice,
  `Prop30.meet` twice, `OnRay.of_sameSideOf` to put `F` on the ray of the angle, I.38
  (new form), I.41, `area_cut`.
- **I.43.** I.34 three times (its last conclusion, read with `Parallelogram.rotate`);
  `EBGK` and `HKFD` are parallelograms by `Prop30.parallel`; then `area_cut` and
  `Parallelogram.quadArea_rotate` cut `ABC` into `AEK`, `EBGK`, `KGC`; `CommonNotion3`.
  The scratch reckoning was 25 lines.
- **I.44.** `Prop42`, then `Prop44.place` (`G` on the side away from `P`). `H`, `L`, `M`
  by `Prop30.meet`; `Prop29.interior` and `angle_add_of_within` for "less than two
  right angles"; `Postulate5` for `K`. Then I.43's hypotheses, each by
  `Between.of_sameSide` (parallels keep order): from `B` between `A` and `E`, `G` is
  between `H` and `F`; from that, `B` between `H` and `K`; and so on. `KL` is parallel
  to `AB` by `Prop30.parallel`. I.15 at the end.
- **I.45.** See "I.42 and I.44". `Prop29.interior`, I.14, `Prop29.alternate`, I.14,
  I.34, I.30, I.33 (`F`, `L` lie on one side of `KM`: `Parallel.sameSide`), and
  `quadArea_add_of_parallelograms` for "the whole".
- **I.46.** I.11 at `A` (`Prop11` with its `C` at `A`), `OnRay.exists_len_eq`, I.31
  twice and `Prop30.meet`, I.34, `Prop29.interior` and `CommonNotion3`. Keep the
  corollaries.
- **I.47.** `Prop28.square` makes each square a parallelogram. `L` by `Prop30.meet`;
  the point where `AL` crosses `BC` is unnamed in Heath and needs a name in Lean.
  That it falls between `B` and `C` is Euclid's figure: the angles `ABC`, `ACB` are
  less than right (I.17), so the foot cannot fall outside (I.16). Write the
  "similarly" once over any letters; `quadArea_add_of_parallelograms` for the whole.
- **I.48.** Scratch proof, 50 lines: `D` on the other side of `AC` from `B`, the three
  squares by I.46 outward, I.47, `Prop46.square_eq` twice, `Prop46.side_eq`, I.8.

## Looking ahead

- I.35 and I.44 are the long ones. Each has a scratch-tested route above, but no
  full proof yet.
- `Prop46.side_eq` cites `Prop46`; until the I.46 sailor finishes, I.48 is pending
  through it.
- The figure of I.45 will not look like Heath's (`H` sits on `ABD`), and I.47's foot
  of the parallel has no letter. Both want a sentence in the mishnah.
- `CONTRIBUTING.md` still names only `Helpers.lean`; `docs/STYLE.md` now names both.

## Housekeeping

- `lake build`, `lake env lean Certificate/Facts.lean` and
  `python3 scripts/check_fidelity.py` pass; `facts.json` is unchanged, since no
  proposition's own proof changed. The generated pages are left for the captain.
- All 48 statements in `scripts/scaffold_book.py` match the Lean files.
- The new modules are listed in `Elements.lean`; `Basics.lean` gathers the two Book
  Zero files, so every proposition sees them.
- The sketches import what Euclid cites (and `Prop44.lean`, `Prop46.lean` what
  their new helpers need); a sailor who uses `HelpersParallels` adds the import.
