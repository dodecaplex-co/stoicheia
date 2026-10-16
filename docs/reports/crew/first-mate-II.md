# First mate: Book II, its ground and its statements (15 October 2026)

Getting ready for the Book II voyage, which sends fourteen sailors to II.1–II.14 at
once. Four jobs: merge the transcribers' text of Book II; teach the scripts and the
certificate a second book; decide how Lean says "the rectangle contained by AB, BC",
"the square on AB" and "the gnomon", and prove what that needs; and state II.1–II.14,
test every statement, and write the [sailing orders](orders-II.md). The design is in
[docs/briefs/0003-book-II.md](../../briefs/0003-book-II.md); this report is the working
detail for the crew.

Everything below builds, with main's closing pass of Book I (to `7a4449e`) merged in:
`lake build`, `lake env lean Certificate/Facts.lean` and
`python3 scripts/check_fidelity.py` pass with both books. Book I's 48 entries in
`facts.json` and every page under `book/I/` come out byte for byte as on main; the Book I
sections of `CERTIFICATE.md` and `GRAPH.md` are unchanged, and Book II's follow them.
The challenges to this report, and the answers, are at the end.

## The transcribers' text

`heath/II/front.md` and `heath/II/01.md`–`14.md`, from the two transcribers' branches,
merged without conflict. Two of their notes matter to the sailors: II.8's first
construction sentence carries Heath's printed brackets "[the straight line]" and "[with
AB]", which are not citations; and II.10's "[I. Post. 5]", Book I's postulate cited
from Book II, which stays as Heath prints it (challenge 9 below).

## Two books in the scripts

- **`scripts/heath.py`**: `BOOKS = {"I": 48, "II": 14}`, the one list the scripts share;
  `arabic` and `prop_key` sort references by book and number (I.48 before II.1, IX
  before X).
- **`scripts/scaffold_book.py`**: `BOOK_II` holds the fourteen statements; each sketch
  imports Book Zero, `Elements.BookII.Rectangles` (`GROUNDWORK`), and every proposition
  Euclid cites, from either book. `python3 scripts/scaffold_book.py II` made
  `Elements/BookII/Prop01.lean`–`Prop14.lean`.
- **`scripts/render.py`**: `book/II/` (pages, index, front page), a Book II section in
  `CERTIFICATE.md` and `GRAPH.md`, and links across books (a Book II page links to I.47 at `../I/47.md`) on a
  Book II page. The front page's heading and the index's first sentence come from the
  sections of `heath/<book>/front.md` (Book II has Definitions only), and the gap
  catalogue is linked only once it exists. In `GRAPH.md`, the Book I propositions that
  Book II cites are drawn as nodes of their own, in white.
- **`scripts/check_fidelity.py`**: both books. The Postulate 5 boundary is Book I's
  rule: nothing before I.29 may rest on it. Book II comes after all of Book I, so
  `FIRST_EUCLIDEAN = {"I": 29, "II": 1}`, and II.10 may cite the postulate by name. The
  certificate's Book II section says the same in words. It also fails if `facts.json`
  misses a book of `heath.BOOKS` or a proposition cites one that does not come before
  it.
- **`Certificate/Facts.lean`**: `("II", Elements.BookII, 14)` in `books`; `refOf` turns
  `Elements.BookII.Prop4` into `"II.4"`. Tested with II.12's scratch proof put in
  place for a moment: its entry cited I.17, I.47 and II.4 by their own books, with I.4,
  I.28, I.34 and I.46 brought in through `Prop47.sq`.
- **`README.md`**: a Book II row under "Where things stand"; "Join in" now points at
  Book II.

## The design, in one paragraph

`Rectangle A B C D` is Definition II.1's rectangular parallelogram (a parallelogram with
all four angles right); `rect A B C D`, the rectangle contained by `AB`, `CD`, is the
area of a rectangle with those sides, chosen once by `Classical.epsilon`; `sq A B` is
`rect A B A B`. That `rect` follows the lengths, reads either way round, and is nothing
when a side is, needs no proposition. That every rectangle drawn is the rectangle
contained by its sides, so that the choice makes no difference, is
`Rectangle.contained`, from I.4 and I.34. The gnomon has no Lean word: it is the sum of
its three parallelograms, and `Parallelogram.about_diameter` makes it, with the
remaining parallelogram, the whole. Details and reasons are in the brief.

## The ground

All proved, no `sorry`, no axiom.

**Definitions**, `Elements/Foundations/DefinitionsII.lean`: `Rectangle`, `Contain`,
`rect`, `sq`.

**Book Zero**, `Elements/Figure/Rectangles.lean`, gathered by `Basics.lean`; no
proposition, no Postulate 5: `exists_off_line` (a point off the straight line `AB`,
avoiding a list), `rect_congr`, `sq_congr`, `sq_symm`, `Contain.symm`, `rect_comm`,
`rect_self_left`, `rect_self_right`, `sq_self`, `Rectangle.rotate`,
`Rectangle.reverse`, `Square.reverse`, `Square.rectangle`, `Square.len_eq`. And
`Parallel.between` in `Parallelograms.lean`, which main's closing pass removed as unused
and this branch restores for `Parallelogram.figure`.

**Book II's ground**, `Elements/BookII/Rectangles.lean`. "Adds" is what the
certificate's walk finds inside each, measured on this branch.

| Lemma | Use it for | Adds |
|---|---|---|
| `Rectangle.of_right` | a parallelogram with its angle at the first corner right is a rectangle | I.29 |
| `Rectangle.congr` | rectangles with equal sides are equal | I.4, I.34 |
| `Rectangle.contained` | `quadArea P Q R S = rect P Q P S` | I.4, I.34 |
| `Rectangle.eq_rect` | "it is contained by GB, BC, and BG is equal to A": give the two sides at `P` | I.4, I.34 |
| `Square.eq_sq` | a square that is a parallelogram is the square on its first side | I.4, I.34 |
| `Square.described` | from I.46's `Square A D E B` with `D`, `E` on `P`'s side: the parallelogram, and "AE is the square on AB" | I.4, I.28, I.34 |
| `Square.about_diameter` | in a square, a parallelogram about the diameter at a corner is a square | I.5, I.6, I.29, I.34 |
| `Parallelogram.complements` | I.43's complements are parallelograms | I.30 |
| `Parallelogram.about_diameter` | the whole is the two parallelograms about the diameter and the two complements | I.30 |
| `Parallelogram.figure` | "let the figure be drawn": `BD`, `CF` through `C`, `HK` through `G`, with every betweenness and both parallelograms about the diameter, I.43's hypotheses exactly | I.30, I.31 |
| `BookI.Prop47.sq` | I.47 for `sq`: right angle at `A` gives `sq B C = sq B A + sq A C` | I.4, I.28, I.34, I.46, I.47 |

## The statements of II.1–II.14

Hypotheses from the setting-out, conclusions from "I say that". Each was tested against
the scaffold's sketch: five are proved in full in scratch, one has its case split
proved, and the rest have their first construction steps compiled (see "Scratch",
below). Every statement builds, every hypothesis is used by the scratch proofs that
reach it, and none needs a statement of a later proposition.

| Prop | Lean (hypotheses ⊢ conclusion) | Note |
|---|---|---|
| II.1 | `A₁ ≠ A₂`, `Between B D E`, `Between D E C` ⊢ `rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D E + rect A₁ A₂ E C` | The straight line "A" is `A₁ A₂`; BC cut at two points, as the setting-out does. One point of section is not an instance (brief, "Later"). |
| II.2 | `Between A C B` ⊢ `rect A B B C + rect B A A C = sq A B` | Proved in scratch. |
| II.3 | `Between A C B` ⊢ `rect A B B C = rect A C C B + sq B C` | |
| II.4 | `Between A C B` ⊢ `sq A B = sq A C + sq C B + (rect A C C B + rect A C C B)` | Proved in scratch; cited by II.12. |
| II.5 | `Between A C B`, `‖A C‖ = ‖C B‖`, `Between A D B`, `D ≠ C` ⊢ `rect A D D B + sq C D = sq C B` | `D` on either side of `C`, as the enunciation allows ("unequal segments at D" names no side), for later citers such as III.35. Case split proved in scratch. |
| II.6 | `Between A C B`, `‖A C‖ = ‖C B‖`, `Between A B D` ⊢ `rect A D D B + sq C B = sq C D` | Cited by II.11. |
| II.7 | `Between A C B` ⊢ `sq A B + sq B C = rect A B B C + rect A B B C + sq C A` | Cited by II.13. |
| II.8 | `Between A C B` ⊢ `∀ D, Between A B D → ‖B D‖ = ‖C B‖ → rect A B B C + rect A B B C + rect A B B C + rect A B B C + sq A C = sq A D` | "The square described on AB, BC as on one straight line": `D` is introduced by Euclid's own "let BD be produced ... made equal to CB". |
| II.9 | as II.5 ⊢ `sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D)` | `D` on either side of `C`, as II.5. |
| II.10 | as II.6 ⊢ `sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D)` | Cites Postulate 5 by name. |
| II.11 | `A ≠ B` ⊢ `∃ H, Between A H B ∧ rect A B B H = sq A H` | What IV.10 and Book XIII need: `H` within `AB`. |
| II.12 | `Triangle A B C`, `IsObtuse B A C`, `Collinear C A D`, `∀ P, Collinear C A P → P ≠ D → ∠ B D P = ∟` ⊢ `sq B C = sq B A + sq A C + (rect C A A D + rect C A A D)` | The perpendicular as I.12 gives it; that `D` falls on `CA` produced is proved from the obtuse angle (I.17). Proved in scratch. |
| II.13 | `Triangle A B C`, `IsAcute A B C`, `IsAcute A C B`, `Collinear B C D`, `∀ P, Collinear B C P → P ≠ D → ∠ A D P = ∟` ⊢ `sq A C + (rect C B B D + rect C B B D) = sq C B + sq B A` | The same form; `D` falls within `BC` because the angles at `B` and `C` are acute (I.13, I.17). The angle at `A` plays no part, so it is not asked. Proved in scratch. |
| II.14 | `Triangle A₁ A₂ A₄`, `Triangle A₄ A₂ A₃` ⊢ `∃ E H, sq E H = △ A₁ A₂ A₄ + △ A₄ A₂ A₃` | The figure "A" is I.45's figure, two triangles on a diameter; the square is "that which can be described on EH". Proved in scratch. |

### Choices tried and set aside

- **II.12 and II.13 with the foot's place as a hypothesis** (`Between C A D`;
  `Between B D C`). Both proved in scratch, but then the obtuse angle of II.12 and the
  acute angle of II.13 were never used, and Lean warned of the unused hypothesis. In
  I.12's form every hypothesis does work, and a later citer feeds I.12's foot straight
  in.
- **II.5 and II.9 with `D` between `C` and `B`.** Faithful to the figure, and enough
  for II.14: after "Let BE be greater", `E` lies between `G` and `F`, II.5's own figure
  (Heath, vol. 1, p. 410). But the setting-out's "into unequal segments at D" names no
  side, and a later citer such as III.35 meets the point of section on either side of
  the middle point. The general form costs the sailor one case split (15 lines in
  scratch).
- **II.14 for any number of triangles.** It would need I.45 for any number first, and
  II.14 would no longer cite I.45. Left for when a later book needs it.
- **A Lean word for the gnomon.** Euclid only adds the gnomon to things and compares it;
  a sum of three areas says exactly that.

## Scratch

The statements were tested in scratch files, committed, not built, in
[`scratch-II/`](https://github.com/jackChallis/stoicheia/tree/19279eb/docs/reports/crew/scratch-II),
as voyage 4's were; they served Book II and were removed once it was proved, and are at
commit 19279eb. They were re-checked against this branch
after main's closing pass was merged: each compiles with `lake env lean`, T05 and
TFirst with the `sorry`s marked below. T02 now draws `CF` with `Prop31.parallelogram`.
The two walk files (`Walk.lean`, `WalkT.lean`) were tools and stay out.

| File | Proves | Cites (the certificate's walk) |
|---|---|---|
| `T02.lean` | II.2 in full, along Euclid's route, 70 lines; `CF` by `Prop31.parallelogram`, `F`'s place by `Parallel.between` | I.4, I.28, I.29, I.30, I.31, I.34, I.46 |
| `T04.lean` | II.4 in full: `Parallelogram.figure`, then the reckoning; CGKB by `Square.about_diameter` in place of Euclid's own argument | I.4, I.5, I.6, I.28, I.29, I.30, I.31, I.34, I.43, I.46 |
| `T05.lean` | II.5's case split (Euclid's case, or `A` and `B` exchanged), and the figure in II.5's letters; Euclid's case is left | |
| `T12.lean` | II.12 and II.13 in full, the foot placed first | II.12: I.4, I.17, I.28, I.34, I.46, I.47, II.4; II.13: I.4, I.13, I.17, I.28, I.34, I.46, I.47, II.7 |
| `T14.lean` | II.14 in full, 95 lines | I.4, I.10, I.11, I.28, I.29, I.34, I.45, I.46, I.47, II.5 |
| `TFirst.lean` | the first construction steps of II.1, II.3, II.6, II.7, II.8, II.9, II.10, II.11 | |

## Citations each sailor should expect beyond Euclid's brackets

From the walk on the scratch proofs and the ground. The mishnah explains each (STYLE
check 19); when a shared step brings it in, one sentence naming the step is enough.
Nearly every proposition names a drawn rectangle or square, so **I.4 and I.34**
(`Rectangle.contained`) and usually **I.28** (`Square.described`) and **I.29**
(`Rectangle.of_right`) appear throughout; the orders give one stock clause for them.

| Prop | Euclid brackets | Expect beyond them | Brought in by |
|---|---|---|---|
| II.1 | I.11, I.3, I.31, I.34 | I.2, I.4, I.29, I.30 | placing A at B before I.3 cuts it off (I.2); the ground; `Prop31.parallelogram` |
| II.2 | I.46, I.31 | I.4, I.28, I.29, I.30, I.34 | the ground; `Prop31.parallelogram`, `Prop30.parallel` |
| II.3 | I.46, I.31 | I.4, I.28, I.29, I.30, I.34 | the same |
| II.4 | I.46, I.31, I.29, I.5, I.6, I.34 | I.4, I.28, I.30, I.43 | the ground; `Parallelogram.figure`; "since AG is equal to GE" has no bracket (I.43) |
| II.5 | I.46, I.31, I.43, I.36 | I.4, I.5, I.6, I.28, I.29, I.30, I.34 | the ground, `Square.about_diameter`; `Parallelogram.figure` |
| II.6 | I.46, I.31, I.36, I.43 | as II.5 | as II.5 |
| II.7 | I.46, I.43 | I.4, I.5, I.6, I.28, I.29, I.30, I.31, I.34 | "let the figure be drawn" has no bracket (I.31, with `Parallelogram.figure`); the ground |
| II.8 | I.36, I.43 | I.4, I.5, I.6, I.28, I.29, I.30, I.31, I.34, I.46 | "let the square AEFD be described" has no bracket (I.46); the figure drawn double; the ground |
| II.9 | I.32, I.29, I.6, I.34, I.47 | I.4, I.5, I.11, I.28, I.30, I.31, I.46 | "CE drawn at right angles" (I.11), "DF drawn parallel" (I.31) and "the angle EAC equal to AEC" (I.5) have no brackets; `Prop30.meet`; `Prop47.sq` (I.4, I.28, I.34, I.46) |
| II.10 | I.11, I.3, I.31, I.29, I.5, I.32, I.15, I.6, I.34, I.47 | I.4, I.28, I.30, I.46 | `Prop30.meet`; `Prop47.sq` |
| II.11 | I.46, II.6, I.47 | I.4, I.10, I.19 or I.20, I.28, I.29, I.30, I.34 | "AC bisected at E" (I.10); where F and H fall (I.19, I.20); `Prop30.meet` for K; the ground |
| II.12 | II.4, I.47 | I.4, I.17, I.28, I.34, I.46 | where the foot falls (I.17); `Prop47.sq` |
| II.13 | II.7, I.47 | I.4, I.13, I.17, I.28, I.34, I.46 | where the foot falls (I.13, I.17); `Prop47.sq` |
| II.14 | I.45, II.5, I.47 | I.4, I.10, I.11, I.28, I.29, I.34, I.46 | a right angle for I.45 (I.11); "BF bisected at G" (I.10); `Rectangle.of_right`; `Prop47.sq` |

A sailor who takes another route will see other citations; the report lists them, each
with the step that brings it in.

## For the sailors

Book I's shared steps are named below as Book I names them (`Prop30.meet`); in a Book II
file they take `BookI.` (`BookI.Prop30.meet`), and `open BookI` is best avoided, since
there a bare `Prop4` means II.4.

- **II.1.** `exists_off_line`, then `BookI.Prop11` at `B`. "Let BG be made equal to A
  [I. 3]": I.3 cuts off from a greater straight line, so first put A at `B`
  (`BookI.Prop2`), produce `BF` beyond that length (`produce_longer`, from a point
  behind `B`), then `BookI.Prop3`. Through `G` the parallel to `BC` (`BookI.Prop31.line`),
  and through `D`, `E`, `C` the parallels to `BG`, each with the point where it meets
  `GH` and its parallelogram with `GB` (`BookI.Prop31.parallelogram`; one bracket [I. 31]
  for all four), the points' order on `GH` by `Parallel.between`. "BH is equal to BK, DL, EH":
  `quadArea_add_of_parallelograms` twice. Each piece is a rectangle by
  `Rectangle.of_right` (the angle at `B` is right; at `D`, `E` the adjacent angle,
  `adjacent_eq_of_right`), named by `Rectangle.eq_rect`; "DK, that is BG [I. 34]" is
  `BookI.Prop34`.
- **II.2.** Scratch `scratch-II/T02.lean`, the whole proof. `BookI.Prop46` on a side
  from `exists_off_line`; `Square.described`; `BookI.Prop31.parallelogram` draws `CF`
  through `C`, with `F` on `DE` and the parallelogram `ADFC`; `Parallel.between` puts
  `F` between `D` and `E`;
  `quadArea_add_of_parallelograms`; `Rectangle.of_right` and `Rectangle.eq_rect` for AF
  and CE, and `rect_comm` for "AB, BC".
- **II.3.** As II.2, on the square `CDEB` on `CB`. "Let ED be drawn through to F":
  produce `ED`; the parallel through `A`, the point `F` where it meets `ED` produced,
  and the parallelogram `DCAF`, are `BookI.Prop31.parallelogram`.
  "AE is equal to AD, CE": `quadArea_add_of_parallelograms`. "DB is the square on CB":
  `Square.described` and `sq_symm`.
- **II.4.** Scratch `scratch-II/T04.lean`. `BookI.Prop46`, `Square.described`, then
  `Parallelogram.figure` under "let BD be joined ... [I. 31]" (its `F G H K` are
  Euclid's). Then Euclid's proof that CGKB is a square, under his sentences:
  `Prop29.exterior` (CGB, ADB), `Prop5.base` (ADB, ABD), `BookI.Prop6`, `BookI.Prop34`,
  `Prop29.interior`, `BookI.Prop34`; the I.29 corollaries follow I.29 in
  `Elements/BookI/Prop29.lean`. "For the same reason HF is also a square":
  `Square.about_diameter`. "Described on HG, that is AC [I. 34]": `BookI.Prop34` on the
  complement (`Parallelogram.complements`). "AG is equal to GE": `BookI.Prop43` with the
  figure's hypotheses, as in `T04reckon`. The whole: `Parallelogram.about_diameter`; close
  with `ac_rfl`.
- **II.5.** Scratch `scratch-II/T05.lean` for the case split: write Euclid's case once, in an inner
  `have` for `D` between `C` and `B`; the other case exchanges `A` and `B` (`rect_comm`,
  `rect_congr`, `sq_congr`). In Euclid's case: `BookI.Prop46` on `CB`,
  `Parallelogram.figure` with `D` for its `C` (its `F G H K` are Euclid's `G H L M`).
  "Through A let AK be drawn parallel to either CL or BM": `BookI.Prop31.parallelogram`
  gives `K` on `LM` produced and the parallelogram `LCAK`. I.43 for the complements; "CM is equal to AL
  [I. 36]": `BookI.Prop36` with the bases `AC`, `CB`. "DH is equal to DB" and "LG, which
  is equal to the square on CD": `Square.about_diameter` twice, `Square.eq_sq`, I.34. "The
  gnomon NOP and LG are the whole square": `Parallelogram.about_diameter`. The gnomon is
  the sum of its three `quadArea`s; N, O, P label it and are not points.
- **II.6.** As II.5, with `B` between `C` and `D` (`between_inner`) and the square on
  `CD`; no case split.
- **II.7.** `BookI.Prop46`, then "let the figure be drawn" is `Parallelogram.figure`, II.4's
  figure. "AF, CE are the gnomon KLM and the square CF": the square CF is counted twice;
  write each side as a sum of the four pieces (`Parallelogram.about_diameter`) and
  compare with `ac_rfl`. "DG, which is the square on AC": `Square.about_diameter`.
- **II.8.** The longest. `intro D hABD hBD` under "let BD be produced ...". "Let the
  square AEFD be described on AD" (I.46, no bracket) "and let the figure be drawn double":
  `Parallelogram.figure` once with `C`, once with `B`, on the same square; that the two
  sets of parallels meet where Heath's figure puts `G`, `H`, `K`, `L`, `M`, `N`, `O`, `P`,
  `Q`, `R` needs `Prop30.meet` (or `Prop31.parallelogram`) and `Parallel.between`. Name
  the meeting points first, in a helper `Prop8.figure` if it helps, then follow the
  areas. S, T, U label the gnomon and
  are not points.
- **II.9.** Case split as II.5. "CE drawn from C at right angles to AB" (I.11, no
  bracket) "and made equal to AC": `OnRay.exists_len_eq`. "Half a right angle" has no
  Lean word: an angle `x` with `x + x = ∟`; "the whole angle AEB is right" is
  `angle_add_of_within` and `Magnitude.eq_of_add_self_eq`. `BookI.Prop47.sq` three times;
  "the square on AC is also equal to the square on CE" is `sq_congr`.
- **II.10.** As II.9 for the angles, with `D` beyond `B`. "Let it be made equal to either
  AC or CB [I. 3]": produce the perpendicular (`produce_longer`) and cut it with
  `BookI.Prop3`. "Straight lines produced from angles less than two right angles meet
  [I. Post. 5]": `Postulate5` itself, with the two lines `EB`, `FD` and the transversal `EF`.
  `BookI.Prop15` for "DBG is also half a right angle".
- **II.11.** `BookI.Prop46` for the square `ABDC` (I.46 gives it as `Square A C D B`),
  `BookI.Prop10` for `E` (no bracket). "Let CA be drawn through to F, and let EF be made
  equal to BE": `OnRay.exists_len_eq` on `EA` produced; `F` lies beyond `A` because `EB`
  is greater than `EA` (`BookI.Prop19`, the right angle at `A` being the greatest).
  "Let the square FH be described on AF" on `B`'s side; `H` falls on `AB` between `A` and
  `B` because `AF` is less than `AB` (`EB` is less than `EA`, `AB` together:
  `BookI.Prop20`). "GH drawn through to K": `Prop30.meet` with `CD`. II.6 is cited
  as `Prop6 (between_symm hAEC) ... hCAF`. "Let AK be subtracted from each":
  `CommonNotion3` with the cuts from `quadArea_add_of_parallelograms`.
- **II.12.** Scratch `scratch-II/T12.lean`, the whole proof. Under the setting-out sentence, place
  the foot: `D` is not `A` (the angle `BAC` would be right), and not on the ray `AC` (the
  triangle `ABD` would have an obtuse and a right angle, `BookI.Prop17`); so `C`, `A`, `D`
  lie in that order. Then `Prop4` (II.4) on `CD`, `BookI.Prop47.sq` twice, `ac_rfl`.
- **II.13.** Scratch `scratch-II/T12.lean` (`T13`). Place the foot within `BC`: not at `B` or `C`
  (the angle there would be right), and not beyond either (`BookI.Prop13` makes the angle
  beside it obtuse, `BookI.Prop17` forbids it). Then `Prop7` (II.7) on `CB`,
  `BookI.Prop47.sq` twice (the second has no bracket in Heath), `ac_rfl`.
- **II.14.** Scratch `scratch-II/T14.lean`, the whole proof. A right angle from `BookI.Prop11` for
  I.45; `BookI.Prop45` gives a parallelogram, a rectangle by `Rectangle.of_right`. "If BE
  is equal to ED": `Rectangle.contained` and `rect_congr`. "Let BE be greater": write the
  rest once for a rectangle `EBCD` with `ED` less than `EB`, and read the rectangle the
  other way round (`Rectangle.reverse`, `quadArea_reverse`) for the other case. Simson
  remarks that the words are not needed, and Heath answers that they keep II.5's own
  figure, B, G, E, F placed as A, C, D, B are there (p. 410): `G` lies between `B` and
  `E` because `BE` is the greater, so `E` lies between `G` and `F`, and the citation of
  II.5 is Euclid's case. The semicircle: `Postulate3`, `on_circle_of_len_eq`,
  `inside_of_between` for `E`, `line_circle_beyond` for `H`. Then `Prop5` (II.5),
  `Definition15`, `BookI.Prop47.sq` and `CommonNotion3`.

## Looking ahead

- **II.8** is the long one, and the only one whose figure was not built in scratch past
  its first steps: the figure drawn double, ten lettered points where two families of
  parallels meet the square and each other, and eight areas. A helper `Prop8.figure`
  naming every point first will keep the proof under Euclid's sentences readable.
- **II.5 and II.6** reach outside the square: the parallelogram on `AC` through `AK`
  needs its own meeting points and I.36 on equal bases.
- **II.9 and II.10** are angle arithmetic with halves of right angles, and II.10's
  Postulate 5 wants its sides and transversal set out; `Prop30.meet` would also find `G`,
  but Euclid brackets the postulate, so the sailor should cite it.
- **II.11** has three places Euclid takes for granted (F beyond A, H within AB, K on
  CD); each is a few lines with I.19, I.20 and `Prop30.meet`.
- **Certificates.** Through the ground, nearly every Book II proposition will list I.4
  and I.34, and many I.28, I.29 and I.30. The orders give one stock clause; the bosun
  should check each mishnah names the step, not the proposition alone.
- **Figures.** Heath's gnomons carry letters (NOP in II.5 and II.6, KLM in II.7, STU in
  II.8) that label an area, not a point; II.1's "A" is a straight line and II.14's "A" a
  figure. STYLE check 20 has to read these as the orders say. No `figures/II/` exist yet:
  the sailors draw Euclid's figure, and the at-a-glance figures are left for the
  artists.
- **Squares.** Book I's `Square` (Definition 22) says nothing of a side; a square from
  I.46 becomes a parallelogram through `Square.described`, never by assumption.
- **`rect` has no existence or positivity lemma.** Book II always draws its rectangles,
  so it does not need one; Book VI will.
- **Scratch.** The scratch proofs are in `scratch-II/`, inside the repository, so a
  Codex sandbox reaches them as a Claude one does; the orders name the path.

## Housekeeping

- `lake build` (93 jobs) passes; the only warnings are the fourteen sketches' `sorry`.
  `lake env lean Certificate/Facts.lean` writes 62 propositions; Book I's 48 equal
  main's. `python3 scripts/check_fidelity.py` passes for all 62.
- `python3 scripts/render.py` leaves `book/I/` byte for byte as on main, and adds
  `book/II/` and the Book II sections of `CERTIFICATE.md` and `GRAPH.md`.
- The scratch proofs in `scratch-II/` compile against the merged tree.
- All fourteen statements in `scripts/scaffold_book.py` match the Lean files, which the
  scaffold made.
- New modules are listed in `Elements.lean`; `Basics.lean` gathers
  `Elements/Figure/Rectangles.lean`.
- Changed besides: `docs/briefs/0002-decisions.md`, `docs/STYLE.md` (§3 and §6 for a
  second book), `CONTRIBUTING.md` (Book II), `README.md`.

## Challenges and answers

Fourteen challenges to the brief, this report and the orders, before the voyage. Each
is fixed, or shown not to be a problem; the Lean checks were run on the merged tree.

1. **II.14 does not need the general II.5.** Right, and the reason given here was
   wrong. T14 proves `Between B G E` and then calls `Prop5 hBGF hBG hBEF hGE`, with `E`
   between `G` and `F`: Euclid's own case. With a restricted `Prop5r` taking
   `(hCDB : Between C D B)` in place of `Prop5`, T14 compiles with
   `Prop5r hBGF hBG (between_inner hBGE hBEF)`. Heath says as much of "Let BE be
   greater" (vol. 1, p. 410). Fixed: the general statements of II.5 and II.9 stay,
   because the setting-out's "into unequal segments at D" names no side and a later
   citer such as III.35 meets the point of section on either side of the middle point.
   The brief, the table of statements, "Choices tried and set aside" and the II.14 note
   now say so.
2. **II.1 for exactly two points of section.** A judgement; kept as it is. The statement
   is the setting-out's, "cut at random at the points D, E", as I.45's two triangles are
   its figure's. The one-cut form, a(b + c) = ab + ac, is not an instance
   (`Between B D E` makes `D` and `E` different), and getting it from the three-piece
   form needs a cancellation that is not Euclid's. No proposition of Book II cites II.1.
   The limit is recorded in the brief's "Later": a later book that cites II.1 with one
   point of section gets that form then, as a corollary after II.1 from the same figure.
3. **`D ≠ C` in II.5 and II.9.** A judgement; kept. It is Euclid's "unequal segments",
   and the proof needs it to draw the square on `CD`. Both statements do hold at `C`,
   checked in Lean: `rect A C C B + sq C C = sq C B` follows from `‖A C‖ = ‖C B‖` by
   `rw [sq_self, add_zero]; exact rect_congr hAC rfl`, and II.9's by
   `rw [sq_self, add_zero, sq_congr hAC]`. A citer whose point of section may be the
   middle point takes that case first, in a line; the brief says so.
4. **"No axiom" in the brief.** Fixed: Book Zero's `Rectangles.lean` "cites no
   proposition, declares no axiom, never uses Postulate 5", and the brief names what
   `exists_off_line` rests on: Postulates 1 and 3, Definition 15 and System E's rules.
5. **The branch did not merge with main.** Fixed: main (`7a4449e`) is merged in. The
   conflicts are resolved as asked: `check_fidelity.py` keeps main's `COMPLETE` check,
   with `BOOKS = heath.BOOKS` and the branch's `FIRST_EUCLIDEAN` and message;
   `render.py`'s `index()` has main's legend of the marks used and the branch's `start`
   sentence, and `certificate()` main's wording with `P5_NOTE`; `0002-decisions.md`
   keeps main's permalink for `scratch-04` and its closing-pass items, then Book II's;
   `CONTRIBUTING.md` and `README.md` keep "corrections to Book I are welcome" and point
   to Book II. `Parallel.between` is restored, unchanged, in
   `Elements/Figure/Parallelograms.lean`, and recorded in `0002-decisions.md`. Then
   `lake build` (93 jobs), the certificate (62) and `check_fidelity.py` pass;
   `git diff main -- book/I` is empty, and Book I's 48 entries in `facts.json` equal
   main's.
6. **"0 propositions never need it."** Fixed: with nothing proved, Book II's line reads
   "No proposition of Book II is proved yet.", then the note on I.29. Main's wording is
   used once a proposition is proved, with the verb agreeing ("1 uses it"); Book I's
   line is unchanged.
7. **The closing pass's shared steps.** Fixed. The orders list
   `BookI.Prop31.parallelogram` (adds I.30, I.31, by the walk) and `BookI.Prop31.line`
   (adds I.31) under "Shared steps", and ask for parallels to be drawn with them; the
   import rule says the I.29 corollaries come with `Elements.BookI.Prop29` and
   `Prop31.line` with `Elements.BookI.Prop31`. The notes for II.1, II.2, II.3 and II.5
   point at them, and T02 now draws `CF` with `Prop31.parallelogram` and compiles.
   `Parallel.between` stays in the Book Zero list, since it is restored:
   `Prop31.parallelogram` finds a meeting point, not its order among the others.
8. **Scratch proofs out of reach.** Fixed: committed, not built, in
   `docs/reports/crew/scratch-II/` (T02, T04, T05, T12, T14, TFirst), each re-checked
   against the merged tree. The orders name that path, and "if the captain gives you
   one" is gone.
9. **"[I. Post. 5]" rewritten.** Fixed: restored in `heath/II/10.md` and in
   `Prop10.lean`'s `--` line, as the 1908 text prints it (p. 396, leaf n416).
   `heath.justifications` takes an optional book numeral before Post., Def. and C.N.:
   "[I. Post. 5]" is read as Post. 5, and a later book's "[I. Def. 22]" keeps its book.
   II.10's page still shows "Post. 5", and STYLE §5 names the bracket.
10. **STYLE check 8 opens Book I.** Fixed, and checked: with `Elements.BookI` open,
    `#check @Prop4` is I.4; with `Elements.BookII` open it is II.4, and `BookI.Prop4`
    is I.4. Check 8 now says to open `Elements.BookII` for a Book II proposition.
11. **Heath's notes before the propositions.** Fixed: the orders give each one owner.
    II.1 quotes the note on "contained" (p. 370), II.5 the note on the gnomon (p. 371),
    II.4 the account of geometrical algebra (pp. 372–374); every other mishnah refers to
    them in a clause.
12. **"Definitions | 15" on Book II pages.** Fixed: outside Book I, Book I's
    definitions are written with their book, "I.15", on the page and in Book II's rows
    of the certificate. Tried with a Book II entry put into the renderer for a moment;
    Book I's pages are byte for byte as on main.
13. **Silent failures across books.** Taken: `check_facts` fails unless `facts.json`
    covers exactly the books of `heath.BOOKS`, and fails if any proposition cites one
    that does not come before it. Both pass today.
14. **Book II's definitions in the README.** Taken: "What Euclid takes for granted"
    links `DefinitionsII.lean`, the rectangle contained by two straight lines and the
    square on one, "defined, not assumed".
