# First mate: Book II, its ground and its statements (15 October 2026)

Getting ready for the Book II voyage, which sends fourteen sailors to II.1–II.14 at
once. Four jobs: merge the transcribers' text of Book II; teach the scripts and the
certificate a second book; decide how Lean says "the rectangle contained by AB, BC",
"the square on AB" and "the gnomon", and prove what that needs; and state II.1–II.14,
test every statement, and write the [sailing orders](orders-II.md). The design is in
[docs/briefs/0003-book-II.md](../../briefs/0003-book-II.md); this report is the working
detail for the crew.

Everything below builds: `lake build`, `lake env lean Certificate/Facts.lean` and
`python3 scripts/check_fidelity.py` pass with both books. Book I's 48 entries in
`facts.json` and every page under `book/I/` come out byte for byte as before; the Book I
sections of `CERTIFICATE.md` and `GRAPH.md` are unchanged, and Book II's follow them.

## The transcribers' text

`heath/II/front.md` and `heath/II/01.md`–`14.md`, from the two transcribers' branches,
merged without conflict. Two of their notes matter to the sailors: II.8's first
construction sentence carries Heath's printed brackets "[the straight line]" and "[with
AB]", which are not citations; and II.10's "[I. Post. 5]" is written `[Post. 5]`, as in
Book I.

## Two books in the scripts

- **`scripts/heath.py`**: `BOOKS = {"I": 48, "II": 14}`, the one list the scripts share;
  `arabic` and `prop_key` sort references by book and number (I.48 before II.1, IX
  before X).
- **`scripts/scaffold_book.py`**: `BOOK_II` holds the fourteen statements; each sketch
  imports Book Zero, `Elements.BookII.Rectangles` (`GROUNDWORK`), and every proposition
  Euclid cites, from either book. `python3 scripts/scaffold_book.py II` made
  `Elements/BookII/Prop01.lean`–`Prop14.lean`.
- **`scripts/render.py`**: `book/II/` (pages, index, front page), a Book II section in
  `CERTIFICATE.md` and `GRAPH.md`, and links across books, `[I.47](../I/47.md)` on a
  Book II page. The front page's heading and the index's first sentence come from the
  sections of `heath/<book>/front.md` (Book II has Definitions only), and the gap
  catalogue is linked only once it exists. In `GRAPH.md`, the Book I propositions that
  Book II cites are drawn as nodes of their own, in white.
- **`scripts/check_fidelity.py`**: both books. The Postulate 5 boundary is Book I's
  rule: nothing before I.29 may rest on it. Book II comes after all of Book I, so
  `FIRST_EUCLIDEAN = {"I": 29, "II": 1}`, and II.10 may cite the postulate by name. The
  certificate's Book II section says the same in words.
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
`Rectangle.reverse`, `Square.reverse`, `Square.rectangle`, `Square.len_eq`.

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
| II.1 | `A₁ ≠ A₂`, `Between B D E`, `Between D E C` ⊢ `rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D E + rect A₁ A₂ E C` | The straight line "A" is `A₁ A₂`; BC cut at two points, as the setting-out does. |
| II.2 | `Between A C B` ⊢ `rect A B B C + rect B A A C = sq A B` | Proved in scratch. |
| II.3 | `Between A C B` ⊢ `rect A B B C = rect A C C B + sq B C` | |
| II.4 | `Between A C B` ⊢ `sq A B = sq A C + sq C B + (rect A C C B + rect A C C B)` | Proved in scratch; cited by II.12. |
| II.5 | `Between A C B`, `‖A C‖ = ‖C B‖`, `Between A D B`, `D ≠ C` ⊢ `rect A D D B + sq C D = sq C B` | `D` on either side of `C`, as the enunciation allows; II.14 needs it so. Case split proved in scratch. |
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
- **II.5 and II.9 with `D` between `C` and `B`.** Faithful to the figure, but II.14
  cites II.5 with the section on the far side of the middle point whenever the
  rectangle's longer side is `ED`. The general form costs the sailor one case split
  (15 lines in scratch).
- **II.14 for any number of triangles.** It would need I.45 for any number first, and
  II.14 would no longer cite I.45. Left for when a later book needs it.
- **A Lean word for the gnomon.** Euclid only adds the gnomon to things and compares it;
  a sum of three areas says exactly that.

## Scratch

The statements were tested in scratch files outside the repository, against this
branch:
`/private/tmp/claude-501/-Users-johnchallis/68e6b57d-6355-42a6-8303-c463406f082f/scratchpad/II/`.
None is committed. The captain may hand them to the sailors (or commit them as
voyage 4's were).

| File | Proves | Cites (the certificate's walk) |
|---|---|---|
| `T02.lean` | II.2 in full, along Euclid's route, 75 lines | I.4, I.28, I.29, I.30, I.31, I.34, I.46 |
| `T04.lean` | II.4 in full: `Parallelogram.figure`, then the reckoning; CGKB by `Square.about_diameter` in place of Euclid's own argument | I.4, I.5, I.6, I.28, I.29, I.30, I.31, I.34, I.43, I.46 |
| `T05.lean` | II.5's case split (Euclid's case, or `A` and `B` exchanged), and the figure in II.5's letters; Euclid's case is left | |
| `T12.lean` | II.12 and II.13 in full, the foot placed first | II.12: I.4, I.17, I.28, I.34, I.46, I.47, II.4; II.13: I.4, I.13, I.17, I.28, I.34, I.46, I.47, II.7 |
| `T14.lean` | II.14 in full, 95 lines | I.4, I.10, I.11, I.28, I.29, I.34, I.45, I.46, I.47, II.5 |
| `TFirst.lean` | the first construction steps of II.1, II.3, II.6, II.7, II.8, II.9, II.10, II.11 | |
| `Walk.lean`, `WalkT.lean` | the certificate's walk over the ground and the scratch proofs | |

## Citations each sailor should expect beyond Euclid's brackets

From the walk on the scratch proofs and the ground. The mishnah explains each (STYLE
check 19); when a shared step brings it in, one sentence naming the step is enough.
Nearly every proposition names a drawn rectangle or square, so **I.4 and I.34**
(`Rectangle.contained`) and usually **I.28** (`Square.described`) and **I.29**
(`Rectangle.of_right`) appear throughout; the orders give one stock clause for them.

| Prop | Euclid brackets | Expect beyond them | Brought in by |
|---|---|---|---|
| II.1 | I.11, I.3, I.31, I.34 | I.2, I.4, I.29, I.30 | placing A at B before I.3 cuts it off (I.2); the ground; `Prop30.meet` |
| II.2 | I.46, I.31 | I.4, I.28, I.29, I.30, I.34 | the ground; `Prop30.meet`, `Prop30.parallel` |
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
  behind `B`), then `BookI.Prop3`. Through `G` the parallel to `BC` and through `D`, `E`,
  `C` the parallels to `BG` (`BookI.Prop31`, one bracket for all four; each meeting point
  by `Prop30.meet`, and its place by `Parallel.between`). "BH is equal to BK, DL, EH":
  `quadArea_add_of_parallelograms` twice. Each piece is a rectangle by
  `Rectangle.of_right` (the angle at `B` is right; at `D`, `E` the adjacent angle,
  `adjacent_eq_of_right`), named by `Rectangle.eq_rect`; "DK, that is BG [I. 34]" is
  `BookI.Prop34`.
- **II.2.** Scratch `T02.lean`, the whole proof. `BookI.Prop46` on a side from
  `exists_off_line`; `Square.described`; `BookI.Prop31` through `C`, `F` by
  `Prop30.meet`; `Parallel.between` puts `F` between `D` and `E`;
  `quadArea_add_of_parallelograms`; `Rectangle.of_right` and `Rectangle.eq_rect` for AF
  and CE, and `rect_comm` for "AB, BC".
- **II.3.** As II.2, on the square `CDEB` on `CB`. "Let ED be drawn through to F":
  produce `ED`, and `F` is where the parallel through `A` meets it (`Prop30.meet`).
  "AE is equal to AD, CE": `quadArea_add_of_parallelograms`. "DB is the square on CB":
  `Square.described` and `sq_symm`.
- **II.4.** Scratch `T04.lean`. `BookI.Prop46`, `Square.described`, then
  `Parallelogram.figure` under "let BD be joined ... [I. 31]" (its `F G H K` are
  Euclid's). Then Euclid's proof that CGKB is a square, under his sentences:
  `Prop29.exterior` (CGB, ADB), `Prop5.base` (ADB, ABD), `BookI.Prop6`, `BookI.Prop34`,
  `Prop29.interior`, `BookI.Prop34`. "For the same reason HF is also a square":
  `Square.about_diameter`. "Described on HG, that is AC [I. 34]": `BookI.Prop34` on the
  complement (`Parallelogram.complements`). "AG is equal to GE": `BookI.Prop43` with the
  figure's hypotheses, as in `T04reckon`. The whole: `Parallelogram.about_diameter`; close
  with `ac_rfl`.
- **II.5.** Scratch `T05.lean` for the case split: write Euclid's case once, in an inner
  `have` for `D` between `C` and `B`; the other case exchanges `A` and `B` (`rect_comm`,
  `rect_congr`, `sq_congr`). In Euclid's case: `BookI.Prop46` on `CB`,
  `Parallelogram.figure` with `D` for its `C` (its `F G H K` are Euclid's `G H L M`).
  "Through A let AK be drawn parallel to either CL or BM": `BookI.Prop31`, and `K` where
  it meets `LM` produced (`Prop30.meet`). I.43 for the complements; "CM is equal to AL
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
  `Q`, `R` needs `Prop30.meet` and `Parallel.between`. Name the meeting points first, in a
  helper `Prop8.figure` if it helps, then follow the areas. S, T, U label the gnomon and
  are not points.
- **II.9.** Case split as II.5. "CE drawn from C at right angles to AB" (I.11, no
  bracket) "and made equal to AC": `OnRay.exists_len_eq`. "Half a right angle" has no
  Lean word: an angle `x` with `x + x = ∟`; "the whole angle AEB is right" is
  `angle_add_of_within` and `Magnitude.eq_of_add_self_eq`. `BookI.Prop47.sq` three times;
  "the square on AC is also equal to the square on CE" is `sq_congr`.
- **II.10.** As II.9 for the angles, with `D` beyond `B`. "Let it be made equal to either
  AC or CB [I. 3]": produce the perpendicular (`produce_longer`) and cut it with
  `BookI.Prop3`. "Straight lines produced from angles less than two right angles meet
  [Post. 5]": `Postulate5` itself, with the two lines `EB`, `FD` and the transversal `EF`.
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
- **II.12.** Scratch `T12.lean`, the whole proof. Under the setting-out sentence, place
  the foot: `D` is not `A` (the angle `BAC` would be right), and not on the ray `AC` (the
  triangle `ABD` would have an obtuse and a right angle, `BookI.Prop17`); so `C`, `A`, `D`
  lie in that order. Then `Prop4` (II.4) on `CD`, `BookI.Prop47.sq` twice, `ac_rfl`.
- **II.13.** Scratch `T12.lean` (`T13`). Place the foot within `BC`: not at `B` or `C`
  (the angle there would be right), and not beyond either (`BookI.Prop13` makes the angle
  beside it obtuse, `BookI.Prop17` forbids it). Then `Prop7` (II.7) on `CB`,
  `BookI.Prop47.sq` twice (the second has no bracket in Heath), `ac_rfl`.
- **II.14.** Scratch `T14.lean`, the whole proof. A right angle from `BookI.Prop11` for
  I.45; `BookI.Prop45` gives a parallelogram, a rectangle by `Rectangle.of_right`. "If BE
  is equal to ED": `Rectangle.contained` and `rect_congr`. "Let BE be greater": write the
  rest once for a rectangle `EBCD` with `ED` less than `EB`, and read the rectangle the
  other way round (`Rectangle.reverse`, `quadArea_reverse`) for the other case; Simson's
  remark that the words are not needed is Heath's, p. 410. `G` lies between `B` and `E`
  because `BE` is the greater. The semicircle: `Postulate3`, `on_circle_of_len_eq`,
  `inside_of_between` for `E`, `line_circle_beyond` for `H`. Then `Prop5` (II.5),
  `Definition15`, `BookI.Prop47.sq` and `CommonNotion3`.

## Looking ahead

- **II.8** is the long one, and the only one whose figure was not built in scratch past
  its first steps: the figure drawn double, ten lettered points where two families of
  parallels meet the square and each other, and eight areas. A helper `Prop8.figure` naming every point first will keep the
  proof under Euclid's sentences readable.
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
- **Scratch.** The scratch proofs live outside the repository, and a Codex sandbox may
  not reach them. If they should travel with the orders, they can be committed as
  `scratch-04/` was.

## Housekeeping

- `lake build` (93 jobs) passes; the only warnings are the fourteen sketches' `sorry`.
  `lake env lean Certificate/Facts.lean` writes 62 propositions; Book I's 48 are as
  before. `python3 scripts/check_fidelity.py` passes for all 62.
- `python3 scripts/render.py` leaves `book/I/` byte for byte as it was, and adds
  `book/II/` and the Book II sections of `CERTIFICATE.md` and `GRAPH.md`.
- All fourteen statements in `scripts/scaffold_book.py` match the Lean files, which the
  scaffold made.
- New modules are listed in `Elements.lean`; `Basics.lean` gathers
  `Elements/Figure/Rectangles.lean`.
- Changed besides: `docs/briefs/0002-decisions.md`, `docs/STYLE.md` (§3 and §6 for a
  second book), `CONTRIBUTING.md` (Book II), `README.md`.
