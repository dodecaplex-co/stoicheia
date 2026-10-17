# Book II: the brief

*The current decisions for Book II in one place: its words, how its statements say Euclid's
phrases, its representations and their bridges, its shared steps, the choices its
statements make, and its exceptions. The design and its reasons are in
[0003-book-II.md](0003-book-II.md), kept as written, and the first mate's note on every
statement is in [first-mate-II.md](../reports/crew/first-mate-II.md); this page keeps the
outcomes, and agrees with the code. Book I's words and rules hold throughout
([Book I's brief](book-I.md)).*

## The words

In `Elements/Foundations/DefinitionsII.lean`; none is an assumption.

| Euclid | Lean | What it is |
|---|---|---|
| "a rectangular parallelogram" ABCD (Definition II.1) | `Rectangle A B C D` | a parallelogram with all four angles right, its corners in order |
| "the rectangle contained by AB, CD" | `rect A B C D` | the area of a rectangle whose sides about a right angle are equal to AB and CD |
| "the square on AB" | `sq A B` | `rect A B A B` |
| "the gnomon" (Definition II.2) | no word: the sum of its three parallelograms, written where it is used | |

## How the statements say Euclid's phrases

| Euclid | Lean |
|---|---|
| "the rectangle contained by AB, BC" | `rect A B B C` |
| "the square on AB" | `sq A B` |
| "twice the rectangle" | `r + r` |
| "greater than … by", "less than … by" | an equation: the less with the excess is the greater |
| "the straight line A" (II.1) | two points, `A₁ A₂` |
| "the square described on AB, BC as on one straight line" (II.8) | `sq A D` for every D with B between A and D and BD equal to CB |
| "the rectilineal figure A" (II.14) | two triangles, `△ A₁ A₂ A₄ + △ A₄ A₂ A₃`, the figure I.45 takes |
| "let BD be drawn perpendicular" (II.12, II.13) | I.12's form: D on the straight line, and every angle there right |

## Representations and their bridges

- **`rect` is chosen, and the choice makes no difference.** `rect A B C D` is one area of a
  rectangle with sides AB and CD, chosen by `Classical.epsilon`. `Rectangle.contained`
  proves that every rectangle PQRS has the area `rect` names for PQ, PS (from I.4 and
  I.34), so a rectangle drawn in Euclid's figure is the rectangle his words name; this is
  Definition II.1 made a theorem, and it is why I.4 and I.34 appear on Book II's
  certificates.
- **What follows at once,** in Book Zero's `Elements/Figure/Rectangles.lean`: `rect` depends
  only on the lengths (`rect_congr`, `sq_congr`), reads either way round (`rect_comm`), and
  is nothing when a side is (`rect_self_left`, `rect_self_right`, `sq_self`).
- **Squares.** The square I.46 describes is a parallelogram, and the square on its side
  (`Square.described`); Book I's statements about drawn squares stay as they are, and
  `BookI.Prop47.sq` says I.47 of `sq`.
- **No numbers.** Every statement is a sum of areas, as Euclid's are.

How the areas correspond to the pieces drawn (which expression is which piece, and why the
pieces make up the whole) is told once in Book II's introduction and linked where it
matters; the stage-5 review checks it page by page.

## Shared steps

**Book Zero**, besides `Rectangles.lean`: `exists_off_line`, a point off a straight line for
a square or perpendicular to stand on (it rests on Postulates 1 and 3, Definition 15 and
System E's rules, as I.1 does); `Parallel.between` and `quadArea_add_of_parallelograms`, in
`Parallelograms.lean`.

**Book II's ground**, `Elements/BookII/Rectangles.lean`, which may cite Book I:

| Lemma | What Euclid takes for granted | Adds |
|---|---|---|
| `Rectangle.of_right` | a parallelogram with one right angle has all four right | I.29 |
| `Rectangle.congr` | rectangles contained by equal straight lines are equal | I.4, I.34 |
| `Rectangle.contained`, `Rectangle.eq_rect` | a rectangle drawn is the rectangle contained by its sides | I.4, I.34 |
| `Square.eq_sq` | a square is the square on its side | I.4, I.34 |
| `Square.described` | the square I.46 describes is a parallelogram, and the square on its side | I.4, I.28, I.34 |
| `Square.about_diameter` | in square areas the parallelograms about the diameter are squares (the porism to II.4 that Heath calls interpolated) | I.5, I.6, I.29, I.34 |
| `Parallelogram.complements`, `Parallelogram.about_diameter` | the complements of I.43 are parallelograms; the parallelograms about the diameter and the complements make up the whole | I.30 |
| `Parallelogram.figure` | "let the figure be drawn": the diameter and the two parallels, with every point where Euclid's figure puts it | I.30, I.31 |
| `BookI.Prop47.sq` | I.47 said of `sq` | I.4, I.28, I.34, I.46, I.47 |

## The statements' choices

- **II.1** cuts BC at the two points of its setting-out, D and E (see the exceptions).
- **II.5 and II.9** take D anywhere between A and B except at the middle point C, as the
  enunciation does; Euclid's figure has D between C and B, and the other side is the same
  with A and B exchanged.
- **II.12 and II.13** take the perpendicular as I.12 gives it, and prove where its foot
  falls ("CA produced", "cut off within") from the obtuse or acute angles; II.13 asks only
  the angles at B and C to be acute, the angle at A playing no part.
- **II.14** squares the figures I.45 can turn into a parallelogram, two triangles, and
  returns the side of the square, a straight line EH with `sq E H` equal to the figure.

## Policies

- **Postulate 5.** Every proposition of Book II comes after I.29 and may rest on it; II.10
  cites it by name ("[I. Post. 5]", read as Post. 5).
- **Superposition** stays with I.4 and I.8.
- **Citing Book I.** A proof cites `BookI.Prop46` under "[I. 46]", and imports Book Zero,
  `Elements.BookII.Rectangles` and every proposition cited, from either book.
- **Definitions across books.** A Book II page writes Book I's Definition 15 as "Def. I.15",
  beside Book II's own.

## Exceptions

The review records in `review/II/` are the authority. These are the exceptions the outside
review named, with the work that answers each:

| Proposition | Scope | What is restricted | Tags | Planned |
|---|---|---|---|---|
| II.1 | restricted | the straight line is cut into exactly three pieces, where Euclid's words allow any number | `three-pieces` | stage 2: `Prop1.two` and `Prop1.general`, for any number of pieces in order |
| II.14 | restricted | the figure is two triangles; the construction returns the side of the square | `two-triangles`, `side-not-square` | stage 2: `Prop14.general` for a supplied dissection, and `Prop14.square`, returning a drawn square |

Each keeps Euclid's worked configuration, with the general theorem beside it as a
companion. `rect` has as yet no lemma that a rectangle contained by any two straight lines
can be drawn; Book II never needs one, since it always draws its rectangles, and Book VI
will.
