# First mate: the statements of I.33–I.48, Book Zero for areas, and the shared steps (15 October 2026)

Getting ready for the fourth voyage, which sends sixteen sailors, two crews of
Claude and two of OpenAI Codex, to I.33–I.48 all at once, and finishes Book I.
Three jobs: read the statements once more against Heath and against every later
proposition that leans on them; give Book Zero the facts about areas and
parallelograms that the area section needs, and gather the steps that cite a
proposition into one shared file; and write the [sailing orders](orders-04.md).
A challenger then went over all of it; the twenty challenges, and how each was
answered, are near the end.

Everything below builds: `lake build`, `lake env lean Certificate/Facts.lean` and
`python3 scripts/check_fidelity.py` pass, `facts.json` comes out byte for byte as
committed (so I.1–I.32 keep their citations and axioms), and nothing before I.29
rests on Postulate 5. The generated pages are left for the captain.

## The statements of I.33–I.48

**Three statements changed (I.37, I.38 and I.48); the other thirteen stand.** To be
sure of them, proofs were written against the statements. They were committed, not
built, in `docs/reports/crew/scratch-04/` (the lakefile builds only the `Elements`
root, and `check_fidelity.py` reads only `Elements/`); they served voyage 4 and were
removed once Book I was proved. They are at commit 54a08e6
([`scratch-04/`](https://github.com/jackChallis/stoicheia/tree/54a08e61a69c3b643590f1c7758c7b8058c9c7aa/docs/reports/crew/scratch-04));
there, check one with `lake env lean docs/reports/crew/scratch-04/T35.lean`. Each
compiles against this branch with no `sorry` of its own (`#print axioms` shows
`sorryAx` only through the cited sketches). They follow Euclid's route but are not written under his sentences. The
citations are those the certificate's walk finds.

| File | Proves | Lines | Cites |
|---|---|---|---|
| `T35.lean` | I.35 in every case: Euclid's (`T35euclid`), Proclus' (`T35between`, `T35same`) | 246 | I.4, I.29, I.34 |
| `T36.lean` | I.36 (`T36`); I.43's area reckoning (`T43`), *taking the complements as parallelograms* | 76 | I.33, I.34, I.35; I.34 |
| `ScratchChallenge43.lean` | the complements of I.43 are parallelograms, from I.43's hypotheses alone (the challenger's) | 56 | I.30 |
| `T37.lean` | I.37 as restated (`T37`); I.39 and I.41 citing it (`T39`, `T41`) | 109 | I.30, I.31, I.34, I.35; I.30, I.31, I.37; I.34, I.37 |
| `T38.lean` | I.38 as restated (`T38`); I.42 citing it (`T42`) | 114 | I.30, I.31, I.34, I.36; I.10, I.23, I.30, I.31, I.38, I.41 |
| `T44.lean` | I.44 from its citation of I.42 on | 137 | I.2, I.4, I.15, I.23, I.29, I.30, I.31, I.34, I.42, I.43 |
| `ScratchChallenge45.lean` | I.45 in full (the challenger's) | 83 | I.14, I.29, I.30, I.33, I.34, I.42, I.44 |
| `ScratchChallenge47.lean` | I.47 in full (the challenger's, now citing `Prop47.within`) | 144 | I.4, I.13, I.14, I.17, I.28, I.30, I.31, I.41 |
| `T48.lean` | I.48 in full | 64 | I.3, I.4, I.8, I.11, I.28, I.34, I.46, I.47 |

Not tried in scratch: I.33, I.34, I.40 and I.46. Each is short, and close to a
tested one (I.40 to I.39; I.46 to I.44's parallels and I.29's interior angles).

| Prop | Verdict |
|---|---|
| I.33 | OK. `SameSideOf B D A C` is "in the same directions"; `AreParallel.oppositeSidesOf` turns it into the alternate sides I.29 wants. Fits I.36 and I.45. |
| I.34 | OK. Its last conclusion is the bisection; `Prop34.bisect` (after `Prop34`) says it of `quadArea`. |
| I.35 | OK, and the hardest of the voyage. General, as Euclid's enunciation is, and I.36 and I.37 need it so: I.37's parallelograms `EBCA`, `DBCF` and I.36's second citation (base `EH`) fall in any arrangement. Euclid proves one case (`D` between `A` and `E`); see the note for the sailors. Proved in scratch in every case. |
| I.36 | OK. The two parallelograms may be lettered round opposite ways; one case split (`AreParallel.sameSideOf_or`) gives Euclid's case or its mirror. Proved in scratch. |
| **I.37** | **Changed**: below. |
| **I.38** | **Changed**: below. |
| I.39, I.40 | OK. With I.37 restated, neither needs a case for the meeting point falling on `A`. I.39 proved in scratch. |
| I.41 | OK. Fits I.42 (`FECG`, with `A` on `FG`) and both citations in I.47. Proved in scratch. |
| I.42 | OK, unchanged. See "I.42 and I.44" below. Proved in scratch. |
| I.43 | OK. Every quadrilateral in it is a parallelogram, so the diameter `quadArea` takes does not matter. The complements `EBGK`, `HKFD` are parallelograms by I.30, from I.43's own hypotheses (`ScratchChallenge43.lean`). Its hypotheses are exactly the figure I.44 builds. |
| I.44 | OK, unchanged; Euclid's "let it be placed" is carried out by `Prop44.place`. |
| I.45 | OK. "The rectilineal figure ABCD" is the triangles `ABD`, `DBC` on Euclid's diameter `DB`: `△ A B D + △ D B C`, which is its area whichever way the figure turns (`quadArea A B C D` would use `AC`, wrong for a figure re-entrant at `B` or `D`). Proved in scratch, citing exactly Euclid's brackets. |
| I.46 | OK. Its corollaries `Prop46.square_eq`, `Prop46.side_eq` are below. |
| I.47 | OK. Each square is outward, as Euclid's proof needs (I.14 puts `C`, `A`, `G` on one straight line). Proved in scratch against the statement as it stands. |
| **I.48** | **Changed**: below. |

### I.37: "in the same parallels", as in I.38

Before: `(hpar : AreParallel A D B C)`.
After: `(hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧ OnLine B M ∧ OnLine C M)`.

Why: `AreParallel A D B C` needs `A ≠ D`. Both of I.37's later citers can meet the
case where the two vertices are one point: I.39, when its `E` (where the parallel
through `A` meets `BD`) is `A`, and I.41, when its `E` is `A`. Each sailor would
have split cases before citing it. Read as I.38 now reads it, two parallel
straight lines, one through both vertices and one through the base, the statement
is still true (when `A` is `D` the two triangles are one), and both citers are
simpler. Tested: I.37 along Euclid's route (I.31, I.35, I.34) with no case split,
and I.39 and I.41 citing it, all in full (`T37.lean`).

The phrase "in the same parallels" is now written four ways in I.35–I.41, each for
a reason: I.35 and I.36 give parallelograms, which carry their own parallels, so
only the straight line through the far sides is said (one `∃ L`, or two in I.36);
I.37 and I.38 give triangles, so both parallels are said; I.39 and I.40 conclude
`AreParallel A D …`, Euclid's "AD is parallel"; and I.41's parallelogram carries
its parallels, so `Collinear A D E` puts the triangle's vertex on one of them.

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

So under "let AD be produced in both directions to G, H" there may be no straight
line `AD` to produce. The module notes of I.37 and I.38 now say that "AD" there is
the parallel through the vertices itself, and that the points are taken on it, as
the scratch proofs do.

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

`scripts/scaffold_book.py` carries all three new statements; its 48 statements
match the Lean files.

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

A consequence for I.45, confirmed by the challenger's proof: its "parallelogram FH
... [I. 42]" lies on the triangle `ABD`'s own base. Given to I.42 as `ABD`, the
parallelogram is `FKDG`: `K` lies between `B` and `D` (at its middle point, in
Euclid's construction of I.42), `H` falls on `D`, and `FKDG` lies on `A`'s side of
`BD`. So the finished `KFLM` overlaps the figure `ABCD`, and the figure of I.45
carries two letters, `D` and `H`, at one point. The mishnah says both.

## I.46: squares on equal straight lines

Euclid assumes in I.48 that "the square on DA is also equal to the square on AB",
and conversely that equal squares have equal sides. Heath reports, under I.46, that
Proclus proves both. They live after `Prop46`, as its corollaries, and both are
proved: `Prop46.square_eq` (I.4 on the halves) and `Prop46.side_eq` (the square on
the less is described inside the square on the greater, and is less: I.3, I.46,
I.34). The second cites `Prop46` itself, so it waits on the I.46 sailor's proof.
Its docstring now says why it leaves Proclus' route: he places the two squares side
by side, and a figure cannot be moved here, so one square has to be described
afresh, and described inside the other it is a part of it.

## I.47: where the squares fall

`Prop47.within`, a helper before `Prop47`, proved (from the challenger's
`X47.within`): if the angle `ABC` is less than a right angle, and `BD` stands at
right angles to `BC` on the other side of it from `A`, then `C` lies within the
angle `ABD`. `AD` crosses `BC`; not at `B` (I.13), not beyond `B` (the angle `ABD`
would exceed two right angles, `angle_le_two_right`), so on the ray `BC`. It cites
I.13; the angle is shown acute by I.17 in the proof itself. I.47 uses it three
times: twice for "let the angle ABC be added to each" (`C` within `DBA`, `A` within
`FBC`), and, applied at `B` and at `C`, to put `A` between the parallels `BD`, `CE`,
so that the foot of `AL` falls between `B` and `C` (`Between.of_inside`). I.16 is not
needed.

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
| `Between.of_inside` (was `between_of_sameSide`) | Parallelograms | a point of `AC` inside both parallels lies between `A` and `C` |
| `Between.of_sameSide`, `Parallel.between` | Parallelograms | parallels keep order: projected along parallels, a point between stays between |
| `AreParallel.cross_or`, `AreParallel.sameSideOf_or` | Parallelograms | a quadrilateral between two parallels has crossing diameters or crossing sides; which way the two parallels run |
| `SameSideOf.of_cross` | Parallelograms | crossing diameters: the far corners lie on one side of each side |
| `Parallelogram.cross`, `Parallelogram.quadArea_rotate` | Parallelograms | a parallelogram's diameters cross; either measures it |
| `quadArea_add_of_parallelograms` | Parallelograms | a parallelogram cut by a parallel is the two parallelograms (I.43, I.45, I.47) |
| `Square.rotate` | Parallelograms | a square named from the next corner |

## Shared steps that cite a proposition

`Helpers.lean` is imported by I.7, I.9, I.18, I.19, I.20 and I.24, so it cannot
import I.28–I.30. Its own docstring foresaw this: a later step needs "a file of its
own". That file is `Elements/BookI/HelpersParallels.lean`. The certificate walks
through a step, so a proof that uses one is recorded as citing the propositions
inside it; the last column is what the walk finds.

| Lemma | Where | Use it for | Adds |
|---|---|---|---|
| `Prop29.alternate` | HelpersParallels | alternate angles, `∠ P G H = ∠ G H Q`, from `AreParallel P G H Q` and `P`, `Q` on opposite sides of `GH` (I.33, I.34, I.45) | I.29 |
| `Prop29.interior` | HelpersParallels | interior angles on one side make two right angles (I.44, I.45, I.46) | I.29 |
| `Prop29.exterior` | HelpersParallels | exterior equal to interior and opposite (I.35) | I.29 |
| `Prop30.meet` | HelpersParallels | a straight line meeting one of two parallels meets the other: every point Euclid takes where a parallel he has drawn meets another straight line (I.37–I.47). Proclus' route through I.30, as Heath reports it under I.31; `Prop30.unique`, inside I.30's own proof, is the same from I.29, and each docstring now points to the other | I.30 |
| `Prop30.parallel` | HelpersParallels | I.30 for named straight lines (I.43, I.44, I.45, I.47) | I.30 |
| `Prop28.interior` | HelpersParallels | two right angles on one side make parallels | I.28 |
| `Prop28.square` | HelpersParallels | a square whose far corners lie on one side of its base is a parallelogram (I.47, I.48, and I.46's corollaries) | I.28 |
| `Prop34.bisect` | after `Prop34` | "the diameter bisects it", as `quadArea A B C D = △ A B C + △ A B C` | I.34 |
| `Prop44.place` | before `Prop44` | "let it be placed" | I.2, I.4, I.23, I.30, I.31, I.34 |
| `Prop46.square_eq`, `Prop46.side_eq` | after `Prop46` | squares on equal straight lines are equal, and back (I.48) | I.4, I.28; I.3, I.4, I.28, I.34, I.46 |
| `Prop47.within` | before `Prop47` | where I.47's squares fall | I.13 |

## Citations each sailor should expect beyond Euclid's brackets

From the walk run on the scratch proofs, and, for the four not tried, on the
route in the note. The mishnah explains each (STYLE check 19); when a shared step
brings it in, one sentence naming the step is enough. For I.30 through
`Prop30.meet`, the stock clause is in the orders: Heath reports Proclus drawing it
from I.30 under I.31, referred to in a clause, never quoted.

| Prop | Euclid brackets | Expect beyond them | Brought in by |
|---|---|---|---|
| I.33 | I.29, I.4, I.27 | none | |
| I.34 | I.29, I.26, I.4 | none | |
| I.35 | I.34, I.29, I.4 | none | |
| I.36 | I.33, I.34, I.35 | none | |
| I.37 | I.31, I.35, I.34 | I.30 | `Prop30.meet` |
| I.38 | I.31, I.36, I.34 | I.30 | `Prop30.meet` |
| I.39 | I.31, I.37 | I.30 | `Prop30.meet` |
| I.40 | I.31, I.38 | I.30 | `Prop30.meet` |
| I.41 | I.37, I.34 | none | |
| I.42 | I.23, I.31, I.38, I.41 | I.10, I.30 | "let BC be bisected at E", which has no bracket; `Prop30.meet` |
| I.43 | I.34 | I.30 | `Prop30.parallel`, for the complements |
| I.44 | I.42, I.31, I.29, I.43, I.15 | I.2, I.4, I.23, I.30, I.34 | `Prop44.place` (all five); `Prop30.meet`, `Prop30.parallel` (I.30) |
| I.45 | I.42, I.44, I.29, I.14, I.34, I.30, I.33 | none | |
| I.46 | I.11, I.31, I.34, I.29 | I.30 | `Prop30.meet` |
| I.47 | I.46, I.14, I.4, I.41 | I.13, I.17, I.28, I.30, I.31; and I.46 will not appear | `Prop47.within` (I.13); the acute angles (I.17); `Prop28.square` (I.28); `Prop30.meet`, `Prop30.parallel` (I.30); "through A let AL be drawn parallel", which has no bracket (I.31). The squares are given in the statement, not described in the proof, so I.46 is not cited |
| I.48 | I.47, I.8 | I.3, I.4, I.11, I.28, I.34, I.46 | "let AD be drawn ... at right angles", which has no bracket (I.11); the squares on `DA`, `AC`, `DC`, described to apply I.47 (I.46, also inside `Prop46.side_eq`); `Prop28.square` and `Prop46.square_eq` (I.4, I.28); `Prop46.side_eq` (I.3, I.4, I.28, I.34) |

A sailor who takes another route will see other citations; the report lists them,
each with the step that brings it in.

## For the sailors

- **I.33.** `hpar.oppositeSidesOf hdir` and `Prop29.alternate`; I.4 on `BAC`, `CDB`;
  for I.27 produce `AC` beyond `C` and `DB` beyond `B` first, then
  `AreParallel.of_parallel`. Expect no citation beyond Euclid's.
- **I.34.** Two `Prop29.alternate`s (the sides of `BC` from the parallelogram:
  `Parallelogram.sameSideOf` and `AreParallel.oppositeSidesOf`), I.26, then
  `angle_add_of_within` for "the whole angle ABD". Keep `Prop34.bisect`. Expect no
  citation beyond Euclid's.
- **I.35.** Scratch: `T35.lean`. Write Euclid's case once (an inner `have`, `D`
  between `A` and `E`). His `G`: `AreParallel.cross_or` on `ED ∥ BC`; the disjunct
  where `EC` meets `BD` is impossible, as `E` and `B` lie on either side of `DC`.
  Then `E` lies between `D` and `F` (they are on either sides of `EB`);
  `Prop29.exterior` for "FDC ... EAB"; I.4; `area_cut` four times, `CommonNotion3`,
  `ac_rfl`. In scratch Euclid's case took 90 lines and the whole 240. The rest, as
  Heath reports Proclus doing (vol. 1, p. 328): `E` between `A` and `D` (Proclus
  adds the triangles to the trapezium `EBCD`), `E` at `D`, and `E` at `A` (then `D`
  is `F`: `OnRay.eq_of_len_eq`). The mirror arrangements follow by exchanging the
  two parallelograms: `AreParallel.sameSideOf_or` on `AE ∥ BC` says which. Expect
  no citation beyond Euclid's.
- **I.36.** Scratch: `T36.lean` (`T36`). An inner `key` for `C`, `H` on one side of
  `BE` (I.34, I.33, I.35 twice, areas turned round with `quadArea_reverse` and
  `Parallelogram.quadArea_rotate`), then `AreParallel.sameSideOf_or` on `EH ∥ BC`,
  the second case with `EFGH` named `HGFE`. Expect no citation beyond Euclid's.
- **I.37, I.38.** Scratch: `T37.lean` (`T37`), `T38.lean` (`T38`), about 45 lines
  each. "In the same parallels" gives two parallel straight lines `L`, `M`, and the
  vertices may be one point. Under "let AD be produced in both directions", "AD" is
  `L` itself, and the points are taken on `L`; the mishnah says so in a sentence.
  Through `B` the parallel to `CA` (I.31), then `Prop30.meet` with `L` for `E` (or
  `G`). `Prop34.bisect hEBCA.rotate` and `hEBCA.quadArea_rotate` halve by the
  diameter `AB`; `Magnitude.eq_of_add_self_eq` takes the halves. Expect I.30
  (`Prop30.meet`).
- **I.39, I.40.** Scratch: `T37.lean` (`T39`), 40 lines. `Classical.byContradiction`;
  the meeting point by `Prop30.meet`; it lies on the ray from `B` (or `C`, in I.40)
  through `D` (`OnRay.of_sameSideOf`); then `area_lt_of_cut` for "the greater to
  the less". No case for the meeting point falling on `A`: I.37 and I.38 allow it.
  Expect I.30 (`Prop30.meet`).
- **I.41.** Scratch: `T37.lean` (`T41`), a dozen lines. I.37 with the straight line
  through `A`, `D`, `E` and the straight line `BC`, then `Prop34.bisect`. Expect no
  citation beyond Euclid's.
- **I.42.** Scratch: `T38.lean` (`T42`), 55 lines: I.10, I.23 on `A`'s side, I.31
  twice, `Prop30.meet` twice, `OnRay.of_sameSideOf` to put `F` on the ray of the
  angle, I.38 (new form, with `A` for both vertices), I.41, `area_cut`. Expect I.10
  ("let BC be bisected" has no bracket) and I.30 (`Prop30.meet`).
- **I.43.** Scratch: `T36.lean` (`T43`) and `ScratchChallenge43.lean`. I.34 three
  times (its last conclusion, read with `Parallelogram.rotate`). The complements
  `EBGK` and `HKFD` are parallelograms from I.43's hypotheses alone, by four uses of
  `Prop30.parallel` (`AB ∥ KG`, `BC ∥ KE`, `KH ∥ CD`, `KF ∥ DA`): that is
  `ScratchChallenge43.lean`, 45 lines. `T43` then takes them as given: `area_cut`
  and `Parallelogram.quadArea_rotate` cut `ABC` into `AEK`, `EBGK`, `KGC`;
  `CommonNotion3`; 30 lines. Expect I.30 (`Prop30.parallel`).
- **I.44.** Scratch: `T44.lean`. `Prop42`, then `Prop44.place` (`G` on the side away
  from `P`). `H`, `L`, `M` by `Prop30.meet`; `Prop29.interior` and
  `angle_add_of_within` for "less than two right angles"; `Postulate5` for `K`.
  Then I.43's hypotheses, each by `Between.of_sameSide` (parallels keep order):
  from `B` between `A` and `E`, `G` is between `H` and `F`; from that, `B` between
  `H` and `K`; and so on. `KL` is parallel to `AB` by `Prop30.parallel`. I.15 at the
  end. In scratch, everything after the citation of I.42 took 130 lines. Expect
  I.2, I.4, I.23, I.34 (`Prop44.place`) and I.30 (`Prop44.place`, `Prop30.meet`,
  `Prop30.parallel`); the letters inside `Prop44.place` don't count in STYLE
  check 20.
- **I.45.** Scratch: `ScratchChallenge45.lean`, 70 lines. `Prop42` on the triangle
  `ABD` gives the parallelogram `FKDG`: its `H` is `D`, `K` lies between `B` and `D`
  (at its middle point, in Euclid's construction), and it lies on `A`'s side of
  `BD`. So the finished `KFLM` overlaps `ABCD`, and the figure carries `D` and `H` at
  one point; the mishnah says both. Then `Prop44` on `GD`, `Prop29.interior`, I.14,
  `Prop29.alternate`, I.14, I.34, I.30, I.33 (`F`, `L` lie on one side of `KM`), and
  `quadArea_add_of_parallelograms` for "the whole". Expect no citation beyond
  Euclid's.
- **I.46.** I.11 at `A` (`Prop11` with its `C` at `A`), `OnRay.exists_len_eq`, I.31
  twice and `Prop30.meet`, I.34, `Prop29.interior` and `CommonNotion3`. Keep the
  corollaries. Expect I.30 (`Prop30.meet`).
- **I.47.** Scratch: `ScratchChallenge47.lean`, the challenger's proof in full,
  130 lines beside `Prop47.within`. I.17 makes the angles `ABC`, `ACB` less than right. `Prop47.within`
  (before `Prop47`, proved) puts `C` within the angle `DBA` and `A` within the angle
  `FBC`, for "let the angle ABC be added to each" (`angle_add_of_within`, twice).
  `Prop28.square` makes each square a parallelogram. `AL` through `A` (I.31) is
  parallel to `CE` too (`Prop30.parallel`); `L`, and the point where `AL` crosses
  `BC`, by `Prop30.meet`. That point has no letter in Heath: it gets a name in the
  Lean and none in the figure, and the mishnah says so. It lies between `B` and `C`
  by `Between.of_inside` with the parallels `BD` and `CE`, since `Prop47.within` at
  `B` and at `C` puts `A` between them and `AL` is parallel to both; `L` lies between
  `D` and `E` the same way. Write the half ("the parallelogram BL is also equal to
  the square GB") once over any letters, as the scratch's `X47.half` does, and use
  it for `B` and for `C`; `quadArea_add_of_parallelograms` for the whole. Expect
  I.13 (`Prop47.within`), I.17, I.28 (`Prop28.square`), I.30 (`Prop30.meet`,
  `Prop30.parallel`) and I.31 (unbracketed here); I.46 will not appear, since the
  squares are given in the statement.
- **I.48.** Scratch: `T48.lean`, 50 lines: `D` on the other side of `AC` from `B`,
  the three squares by I.46 outward, I.47, `Prop46.square_eq` twice,
  `Prop46.side_eq`, I.8. Expect I.11 (unbracketed), I.46 (the squares described),
  and I.3, I.4, I.28, I.34 (`Prop28.square`, `Prop46.square_eq`, `Prop46.side_eq`).

## The challenges, and how each was answered

| # | Challenge | Answer |
|---|---|---|
| 1 | I.47's note pointed to a longer route (I.17, I.16) and missed that the same figure fact is needed three times; I.47 was the named top risk | **Fixed.** `Prop47.within` (from the challenger's `X47.within`) is now proved before `Prop47`, citing I.13. The note gives the challenger's tested route: `Prop47.within` twice for C.N. 2, and at `B` and `C` through `Between.of_inside` for the foot; the half written once over any letters. The scratch is committed as `ScratchChallenge47.lean`, adapted to cite `Prop47.within` and `Between.of_inside`. The risk is downgraded. The acute angle stays a hypothesis of the helper, since it is used both ways round. |
| 2 | Extra citations brought in by the helpers in I.44, I.47, I.48 were not foretold | **Fixed.** Measured with the certificate's own walk, on every helper and every scratch proof. The "expect" table above, and each sailor's note, list them with the step that brings each in; I.46's absence from I.47 is said. The orders and STYLE check 19 say one sentence naming the step is enough. |
| 3 | I.37 still took `AreParallel A D B C`, so I.39 and I.41 must split cases | **Fixed by restating I.37** in I.38's form. Tested in full (`T37`), with I.39 and I.41 citing it (`T39`, `T41`), neither splitting cases. `scaffold_book.py` updated. Why the remaining forms differ is said above. |
| 4 | The "I.43 test" took the complements as hypotheses | **Fixed in this report.** The reckoning `T43` took them as given; the challenger proved them from I.43's hypotheses (`ScratchChallenge43.lean`, I.30 four times). Both are committed and named in the I.43 note. No statement change. |
| 5 | I.45: `H` falls on `D`, `K` is the midpoint of `BD`, the figure overlaps | **Fixed in the note.** No statement change. One correction: I.42's statement promises only that `K` lies between `B` and `D`; it is the middle point in Euclid's construction, and the figure puts it there. |
| 6 | `Prop46.square_eq` docstring attributed Heath's remark to Proclus | **Fixed** with the challenger's wording ("and remarks that it ... (vol. 1, p. 348)"); checked against the OCR, p. 348. |
| 7 | I.38: "let AD be produced" when `A` is `D` | **Fixed.** The module notes of I.38 and the restated I.37 say "AD" is the parallel through the vertices, and the points are taken on it; the note tells the sailors to say so in the mishnah. |
| 8 | CONTRIBUTING house rule 2 named only `Helpers.lean` | **Fixed.** It names `HelpersParallels.lean` and the corollary place, and says to import the files cited. |
| 9 | The orders dropped the import rule | **Fixed** in the orders and STYLE §3: `Elements.BookI.HelpersParallels` when a step from it is cited. |
| 10 | The orders dropped "If the statement seems wrong or too weak, stop and say so" | **Fixed**: restored, with "do not work around it". |
| 11 | No stock clause for the certificate effect of shared steps | **Fixed.** The orders' Shared steps say what each adds, and give the clause for `Prop30.meet` (a clause, not a quotation of Heath's I.31 note). |
| 12 | The scratch proofs lived only in a session scratchpad | **Fixed.** Committed, not built, in `docs/reports/crew/scratch-04/`, named in each note and in the orders; the same for both crews. They served voyage 4 and were removed once the propositions were proved. |
| 13 | I.47 untested; the foot and "C within DBA" had no helper and seemed to need I.13, I.17, I.29 | **Answered by 1.** Tested in full. The two steps are one helper (`Prop47.within`) and `Between.of_inside`; the walk shows I.29 is not needed. |
| 14 | The I.40 note named the ray from `E` | **Fixed**: "(or `C`, in I.40)", as Heath's `F` lies on `CD`. |
| 15 | `between_of_sameSide` and `Between.of_sameSide` too alike | **Fixed.** Renamed `Between.of_inside`; each docstring tells them apart; both named, with a gloss, in the orders. |
| 16 | Three docstrings: `Between.of_sameSide`, `Prop30.parallel`, `Prop46.side_eq` | **Fixed.** (a) "If `B`, on the straight line `L`, lies between `A` and `C`". (b) I.44 and I.47 ("parallel to either"), bracketed in I.45, and needed for I.43's complements. (c) "We take another road, because a figure cannot be moved here ...", naming Proclus' I.39, I.27, I.34, I.26. |
| 17 | `Prop30.meet` and `Prop30.unique` both "Playfair's axiom" | **Fixed.** Each docstring points to the other; later proofs cite `Prop30.meet`. The orders name both. |
| 18 | Neither CONTRIBUTING nor STYLE §3 named the corollary place | **Fixed** in both (`Prop34.bisect`). |
| 19 | Orders lacked the `PATH` line, a full path, a Codex commit line, the halves lemma | **Fixed**, all four, and `Prop44.place`, `Prop47.within`, `Between.of_inside` added to Shared steps. |
| 20 | Generated pages stale; helper letters in check 20 | (a) **Not a problem to fix here**: the captain renders after the merge, as in voyage 3; the orders now tell sailors that CI's generated-pages step fails until then. Rendering this branch changes exactly `book/I/30`, `34`, `37`, `38`, `44`, `46`, `47`, `48`; `facts.json`, `CERTIFICATE.md` and `GRAPH.md` do not change. (b) **Fixed**: the orders and STYLE check 20 exempt a helper's own letters. |

## Looking ahead

- I.35 and I.44 are the long ones; both are proved in scratch, so the statements
  hold up, but each sailor still has to write the proof under Euclid's sentences.
- I.47 is no longer a risk of statement: it is proved in scratch, and its figure
  facts are a proved helper. What remains is the length (about 130 lines) and the
  unlettered foot of `AL`, which the figure and mishnah must handle.
- I.33, I.34, I.40 and I.46 were not tried in scratch. Each is short and close to a
  tested proof.
- `Prop46.side_eq` cites `Prop46`; until the I.46 sailor finishes, I.48 is pending
  through it. Every citation of an unfinished sketch is pending in the same way,
  until all sixteen are merged.
- The certificate table assumes the routes in the notes. A sailor on another route
  will see other citations, and must name each in the report and the mishnah; the
  bosun checks `facts.json` after the merge.
- The figure of I.45 puts `D` and `H` at one point, and I.47's foot of the parallel
  has no letter. Both want a sentence in the mishnah.
- `Prop47.within` and the docstrings changed here are read on the pages; the
  enforcer should run STYLE §6 over them with the rest.
- The scratch proofs give I.35–I.39, I.41–I.45, I.47 and I.48 a head start that I.33,
  I.34, I.40 and I.46 lack. Both crews have them, but the comparison should say
  which propositions had one.

## Housekeeping

- `lake build`, `lake env lean Certificate/Facts.lean` and
  `python3 scripts/check_fidelity.py` pass; `facts.json` is unchanged, since no
  proposition's own proof changed. The generated pages are left for the captain.
- All 48 statements in `scripts/scaffold_book.py` match the Lean files.
- The new modules are listed in `Elements.lean`; `Basics.lean` gathers the two Book
  Zero files, so every proposition sees them.
- The sketches import what Euclid cites (and `Prop44.lean`, `Prop46.lean`,
  `Prop47.lean` what their helpers need); the orders tell a sailor who cites a step
  from `HelpersParallels` to add the import.
- Changed outside the statements: `CONTRIBUTING.md` (rule 2), `docs/STYLE.md`
  (§3, checks 19 and 20), `docs/briefs/0002-decisions.md`, and docstrings in
  `Prop30.lean`, `Prop46.lean`, `HelpersParallels.lean` and `Parallelograms.lean`.
