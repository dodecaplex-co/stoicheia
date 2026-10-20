"""Create the Lean file for each proposition of a book: the statement in Heath's
letters, Heath's enunciation as its docstring, and every sentence of Euclid's
proof as a `--` comment, ending in `sorry`. That is the "sketch"; proofs are then
written between the comments.

Only creates files that don't exist yet, so it never overwrites a proof.

    python3 scripts/scaffold_book.py III
"""

import re
import sys
import textwrap

import heath

# The statements of Book I, in Heath's letters. Hypotheses come from Euclid's
# setting-out ("Let ABC be a triangle …"), conclusions from "I say that …".
BOOK_I = {
    1: "(A B : Point) (hAB : A ≠ B) (P : Point) :\n"
       "    ∃ C : Point, Equilateral A B C ∧ (¬ Collinear A B P → SameSideOf C P A B)",
    2: "(A B C : Point) (hBC : B ≠ C) :\n    ∃ L : Point, ‖A L‖ = ‖B C‖",
    3: "{A B C₁ C₂ : Point} (hC : C₁ ≠ C₂) (h : ‖C₁ C₂‖ < ‖A B‖) :\n"
       "    ∃ E : Point, Between A E B ∧ ‖A E‖ = ‖C₁ C₂‖",
    4: "{A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)\n"
       "    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (hA : ∠ B A C = ∠ E D F) :\n"
       "    ‖B C‖ = ‖E F‖ ∧ △ A B C = △ D E F ∧ ∠ A B C = ∠ D E F ∧ ∠ A C B = ∠ D F E",
    5: "{A B C D E : Point} (hABC : Triangle A B C) (hAB : ‖A B‖ = ‖A C‖)\n"
       "    (hD : Between A B D) (hE : Between A C E) :\n"
       "    ∠ A B C = ∠ A C B ∧ ∠ C B D = ∠ B C E",
    6: "{A B C : Point} (hABC : Triangle A B C) (h : ∠ A B C = ∠ A C B) :\n    ‖A B‖ = ‖A C‖",
    7: "{A B C D : Point} (hCD : SameSideOf C D A B) (hCA : ‖C A‖ = ‖D A‖)\n"
       "    (hCB : ‖C B‖ = ‖D B‖) :\n    C = D",
    8: "{A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)\n"
       "    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (hBC : ‖B C‖ = ‖E F‖) :\n"
       "    ∠ B A C = ∠ E D F",
    9: "{A B C : Point} (hBAC : Triangle B A C) :\n"
       "    ∃ F : Point, SameSideOf F C A B ∧ SameSideOf F B A C ∧\n"
       "      ∠ B A F = ∠ F A C ∧ ∠ B A F + ∠ F A C = ∠ B A C",
    10: "{A B : Point} (hAB : A ≠ B) :\n    ∃ D : Point, Between A D B ∧ ‖A D‖ = ‖D B‖",
    11: "{A B C Q : Point} (hAB : A ≠ B) (hC : Collinear A B C) (hQ : ¬ Collinear A B Q) :\n"
        "    ∃ F : Point, SameSideOf F Q A B ∧ ∀ P : Point, Collinear A B P → P ≠ C → ∠ P C F = ∟",
    12: "{A B C : Point} (hAB : A ≠ B) (hC : ¬ Collinear A B C) :\n"
        "    ∃ H : Point, Collinear A B H ∧ ∀ P : Point, Collinear A B P → P ≠ H → ∠ C H P = ∟",
    13: "{A B C D : Point} (hCBD : Between C B D) (hA : ¬ Collinear C D A) :\n"
        "    ∠ C B A + ∠ A B D = ∟ + ∟",
    14: "{A B C D : Point} (hCD : OppositeSidesOf C D A B) (h : ∠ A B C + ∠ A B D = ∟ + ∟) :\n"
        "    Between C B D",
    15: "{A B C D E : Point} (hAEB : Between A E B) (hCED : Between C E D)\n"
        "    (hC : ¬ Collinear A B C) :\n    ∠ A E C = ∠ D E B ∧ ∠ C E B = ∠ A E D",
    16: "{A B C D : Point} (hABC : Triangle A B C) (hBCD : Between B C D) :\n"
        "    ∠ C B A < ∠ A C D ∧ ∠ B A C < ∠ A C D",
    17: "{A B C : Point} (hABC : Triangle A B C) :\n"
        "    ∠ A B C + ∠ B C A < ∟ + ∟ ∧ ∠ B A C + ∠ A C B < ∟ + ∟ ∧ ∠ C A B + ∠ A B C < ∟ + ∟",
    18: "{A B C : Point} (hABC : Triangle A B C) (h : ‖A B‖ < ‖A C‖) :\n    ∠ B C A < ∠ A B C",
    19: "{A B C : Point} (hABC : Triangle A B C) (h : ∠ B C A < ∠ A B C) :\n    ‖A B‖ < ‖A C‖",
    20: "{A B C : Point} (hABC : Triangle A B C) :\n"
        "    ‖B C‖ < ‖B A‖ + ‖A C‖ ∧ ‖A C‖ < ‖A B‖ + ‖B C‖ ∧ ‖A B‖ < ‖B C‖ + ‖C A‖",
    21: "{A B C D : Point} (hABC : Triangle A B C) (hD : InsideTriangle D A B C) :\n"
        "    ‖B D‖ + ‖D C‖ < ‖B A‖ + ‖A C‖ ∧ ∠ B A C < ∠ B D C",
    22: "{A₁ A₂ B₁ B₂ C₁ C₂ E F P : Point}\n"
        "    (hAB : ‖C₁ C₂‖ < ‖A₁ A₂‖ + ‖B₁ B₂‖) (hAC : ‖B₁ B₂‖ < ‖A₁ A₂‖ + ‖C₁ C₂‖)\n"
        "    (hBC : ‖A₁ A₂‖ < ‖B₁ B₂‖ + ‖C₁ C₂‖) (hFE : F ≠ E) (hP : ¬ Collinear F E P) :\n"
        "    ∃ G K : Point, OnRay G F E ∧ SameSideOf K P F E ∧\n"
        "      ‖K F‖ = ‖A₁ A₂‖ ∧ ‖F G‖ = ‖B₁ B₂‖ ∧ ‖G K‖ = ‖C₁ C₂‖",
    23: "{A B C D E P : Point} (hAB : A ≠ B) (hDCE : Triangle D C E) (hP : ¬ Collinear A B P) :\n"
        "    ∃ F G : Point, OnRay G A B ∧ SameSideOf F P A B ∧ ∠ F A G = ∠ D C E",
    24: "{A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)\n"
        "    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (h : ∠ E D F < ∠ B A C) :\n"
        "    ‖E F‖ < ‖B C‖",
    25: "{A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)\n"
        "    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (h : ‖E F‖ < ‖B C‖) :\n"
        "    ∠ E D F < ∠ B A C",
    26: "{A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)\n"
        "    (hB : ∠ A B C = ∠ D E F) (hC : ∠ B C A = ∠ E F D)\n"
        "    (hside : ‖B C‖ = ‖E F‖ ∨ ‖A B‖ = ‖D E‖) :\n"
        "    ‖A B‖ = ‖D E‖ ∧ ‖A C‖ = ‖D F‖ ∧ ‖B C‖ = ‖E F‖ ∧ ∠ B A C = ∠ E D F",
    27: "{A B C D E F : Point} (hAEB : Between A E B) (hCFD : Between C F D)\n"
        "    (hAD : OppositeSidesOf A D E F) (h : ∠ A E F = ∠ E F D) :\n    AreParallel A B C D",
    28: "{A B C D E F G H : Point} (hAGB : Between A G B) (hCHD : Between C H D)\n"
        "    (hEGH : Between E G H) (hGHF : Between G H F) (hBD : SameSideOf B D E F)\n"
        "    (h : ∠ E G B = ∠ G H D ∨ ∠ B G H + ∠ G H D = ∟ + ∟) :\n    AreParallel A B C D",
    29: "{A B C D E F G H : Point} (hpar : AreParallel A B C D) (hAGB : Between A G B)\n"
        "    (hCHD : Between C H D) (hEGH : Between E G H) (hGHF : Between G H F)\n"
        "    (hBD : SameSideOf B D E F) :\n"
        "    ∠ A G H = ∠ G H D ∧ ∠ E G B = ∠ G H D ∧ ∠ B G H + ∠ G H D = ∟ + ∟",
    30: "{A B C D E F : Point} (h₁ : AreParallel A B E F) (h₂ : AreParallel C D E F)\n"
        "    (hC : ¬ Collinear A B C) :\n    AreParallel A B C D",
    31: "{A B C : Point} (hBC : B ≠ C) (hA : ¬ Collinear B C A) :\n"
        "    ∃ E F : Point, Between E A F ∧ AreParallel E F B C",
    32: "{A B C D : Point} (hABC : Triangle A B C) (hBCD : Between B C D) :\n"
        "    ∠ A C D = ∠ C A B + ∠ A B C ∧ ∠ A B C + ∠ B C A + ∠ C A B = ∟ + ∟",
    33: "{A B C D : Point} (hpar : AreParallel A B C D) (heq : ‖A B‖ = ‖C D‖)\n"
        "    (hdir : SameSideOf B D A C) :\n    ‖A C‖ = ‖B D‖ ∧ AreParallel A C B D",
    34: "{A B C D : Point} (h : Parallelogram A C D B) :\n"
        "    ‖A B‖ = ‖C D‖ ∧ ‖A C‖ = ‖B D‖ ∧ ∠ B A C = ∠ C D B ∧ ∠ A B D = ∠ A C D ∧\n"
        "      △ A B C = △ D C B",
    35: "{A B C D E F : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E B C F)\n"
        "    (hAF : ∃ L : Line, OnLine A L ∧ OnLine D L ∧ OnLine E L ∧ OnLine F L) :\n"
        "    quadArea A B C D = quadArea E B C F",
    36: "{A B C D E F G H : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E F G H)\n"
        "    (hbase : ‖B C‖ = ‖F G‖)\n"
        "    (hAH : ∃ L : Line, OnLine A L ∧ OnLine D L ∧ OnLine E L ∧ OnLine H L)\n"
        "    (hBG : ∃ L : Line, OnLine B L ∧ OnLine C L ∧ OnLine F L ∧ OnLine G L) :\n"
        "    quadArea A B C D = quadArea E F G H",
    37: "{A B C D : Point} (hABC : Triangle A B C) (hDBC : Triangle D B C)\n"
        "    (hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧ OnLine B M ∧ OnLine C M) :\n"
        "    △ A B C = △ D B C",
    38: "{A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)\n"
        "    (hbase : ‖B C‖ = ‖E F‖)\n"
        "    (hpar : ∃ L M : Line, Parallel L M ∧ OnLine A L ∧ OnLine D L ∧\n"
        "      OnLine B M ∧ OnLine C M ∧ OnLine E M ∧ OnLine F M) :\n    △ A B C = △ D E F",
    39: "{A B C D : Point} (hABC : Triangle A B C) (hDBC : Triangle D B C)\n"
        "    (heq : △ A B C = △ D B C) (hside : SameSideOf A D B C) (hAD : A ≠ D) :\n"
        "    AreParallel A D B C",
    40: "{A B C D E : Point} (hABC : Triangle A B C) (hCDE : Triangle C D E)\n"
        "    (hBCE : Between B C E) (hbase : ‖B C‖ = ‖C E‖) (heq : △ A B C = △ C D E)\n"
        "    (hside : SameSideOf A D B E) (hAD : A ≠ D) :\n    AreParallel A D B E",
    41: "{A B C D E : Point} (hABCD : Parallelogram A B C D) (hE : Collinear A D E) :\n"
        "    quadArea A B C D = △ B E C + △ B E C",
    42: "{A B C D₁ D D₂ : Point} (hABC : Triangle A B C) (hD : Triangle D₁ D D₂) :\n"
        "    ∃ E F G : Point, Between B E C ∧ SameSideOf F A B C ∧ Parallelogram F E C G ∧\n"
        "      ∠ C E F = ∠ D₁ D D₂ ∧ quadArea F E C G = △ A B C",
    43: "{A B C D E F G H K : Point} (hABCD : Parallelogram A B C D) (hK : Between A K C)\n"
        "    (hE : Between A E B) (hG : Between B G C) (hF : Between C F D) (hH : Between D H A)\n"
        "    (hEH : Parallelogram A E K H) (hFG : Parallelogram K G C F) :\n"
        "    quadArea E B G K = quadArea H K F D",
    44: "{A B C₁ C₂ C₃ D₁ D D₂ P : Point} (hAB : A ≠ B) (hC : Triangle C₁ C₂ C₃)\n"
        "    (hD : Triangle D₁ D D₂) (hP : ¬ Collinear A B P) :\n"
        "    ∃ L M : Point, SameSideOf M P A B ∧ Parallelogram A B M L ∧\n"
        "      ∠ A B M = ∠ D₁ D D₂ ∧ quadArea A B M L = △ C₁ C₂ C₃",
    45: "{A B C D E₁ E E₂ : Point} (hABD : Triangle A B D) (hDBC : Triangle D B C)\n"
        "    (hE : Triangle E₁ E E₂) :\n"
        "    ∃ K F L M : Point, Parallelogram K F L M ∧ ∠ F K M = ∠ E₁ E E₂ ∧\n"
        "      quadArea K F L M = △ A B D + △ D B C",
    46: "{A B P : Point} (hAB : A ≠ B) (hP : ¬ Collinear A B P) :\n"
        "    ∃ D E : Point, Square A D E B ∧ SameSideOf D P A B ∧ SameSideOf E P A B",
    47: "{A B C D E F G H K : Point} (hABC : Triangle A B C) (hright : ∠ B A C = ∟)\n"
        "    (hBDEC : Square B D E C) (hD : OppositeSidesOf D A B C) (hE : OppositeSidesOf E A B C)\n"
        "    (hABFG : Square A B F G) (hF : OppositeSidesOf F C A B) (hG : OppositeSidesOf G C A B)\n"
        "    (hACKH : Square A C K H) (hK : OppositeSidesOf K B A C) (hH : OppositeSidesOf H B A C) :\n"
        "    quadArea B D E C = quadArea A B F G + quadArea A C K H",
    48: "{A B C P Q R S T U : Point} (hABC : Triangle A B C)\n"
        "    (hBC : Square B P Q C) (hPQ : SameSideOf P Q B C)\n"
        "    (hBA : Square A B R S) (hRS : SameSideOf R S A B)\n"
        "    (hAC : Square A C T U) (hTU : SameSideOf T U A C)\n"
        "    (h : quadArea B P Q C = quadArea A B R S + quadArea A C T U) :\n"
        "    ∠ B A C = ∟",
}

# The statements of Book II. "The rectangle contained by AB, CD" is `rect A B C D`, and
# "the square on AB" is `sq A B` (Elements/Foundations/DefinitionsII.lean); "twice" a
# magnitude is that magnitude added to itself. A straight line Heath names by one
# letter is two points (`A₁ A₂` for "A" in II.1), and so on for the rectilineal figure
# "A" of II.14, cut by a diameter into two triangles as I.45 takes it.
BOOK_II = {
    1: "{A₁ A₂ B C D E : Point} (hA : A₁ ≠ A₂) (hBDE : Between B D E) (hDEC : Between D E C) :\n"
       "    rect A₁ A₂ B C = rect A₁ A₂ B D + rect A₁ A₂ D E + rect A₁ A₂ E C",
    2: "{A B C : Point} (hACB : Between A C B) :\n    rect A B B C + rect B A A C = sq A B",
    3: "{A B C : Point} (hACB : Between A C B) :\n    rect A B B C = rect A C C B + sq B C",
    4: "{A B C : Point} (hACB : Between A C B) :\n"
       "    sq A B = sq A C + sq C B + (rect A C C B + rect A C C B)",
    5: "{A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖) (hADB : Between A D B)\n"
       "    (hDC : D ≠ C) :\n    rect A D D B + sq C D = sq C B",
    6: "{A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖)\n"
       "    (hABD : Between A B D) :\n    rect A D D B + sq C B = sq C D",
    7: "{A B C : Point} (hACB : Between A C B) :\n"
       "    sq A B + sq B C = rect A B B C + rect A B B C + sq C A",
    8: "{A B C : Point} (hACB : Between A C B) :\n"
       "    ∀ D : Point, Between A B D → ‖B D‖ = ‖C B‖ →\n"
       "      rect A B B C + rect A B B C + rect A B B C + rect A B B C + sq A C = sq A D",
    9: "{A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖) (hADB : Between A D B)\n"
       "    (hDC : D ≠ C) :\n    sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D)",
    10: "{A B C D : Point} (hACB : Between A C B) (hAC : ‖A C‖ = ‖C B‖)\n"
        "    (hABD : Between A B D) :\n    sq A D + sq D B = sq A C + sq C D + (sq A C + sq C D)",
    11: "{A B : Point} (hAB : A ≠ B) :\n    ∃ H : Point, Between A H B ∧ rect A B B H = sq A H",
    12: "{A B C D : Point} (hABC : Triangle A B C) (hBAC : IsObtuse B A C)\n"
        "    (hD : Collinear C A D) (hBD : ∀ P : Point, Collinear C A P → P ≠ D → ∠ B D P = ∟) :\n"
        "    sq B C = sq B A + sq A C + (rect C A A D + rect C A A D)",
    13: "{A B C D : Point} (hABC : Triangle A B C) (hB : IsAcute A B C) (hC : IsAcute A C B)\n"
        "    (hD : Collinear B C D) (hAD : ∀ P : Point, Collinear B C P → P ≠ D → ∠ A D P = ∟) :\n"
        "    sq A C + (rect C B B D + rect C B B D) = sq C B + sq B A",
    14: "{A₁ A₂ A₃ A₄ : Point} (h₁ : Triangle A₁ A₂ A₄) (h₂ : Triangle A₄ A₂ A₃) :\n"
        "    ∃ E H : Point, sq E H = △ A₁ A₂ A₄ + △ A₄ A₂ A₃",
}


# The statements of Book III. A circle takes Heath's letters (`ABC` for the circle ABC).
# A centre is named where the statement uses it. Where a proof needs an unnamed centre,
# it takes one by III.1 where Heath cites it, and from `exists_centre` otherwise
# (docs/briefs/0008-centre.md, step 6). "Equal circles" is `EqualCircles`; a straight
# line touching a circle is `Touches`; circles touching one another are
# `TouchesInternally`, `TouchesExternally` or `CirclesTouch`.
# Contact within includes a point of the inner circle within the outer and none outside;
# contact without has no point within both. `CirclesCut` means meeting at two points with
# a point of each circle within the other. The circumference BKC is
# `circumference α B K C`, and the circumference on which the angle BAC stands is
# `standing α B A C` (Elements/Foundations/DefinitionsIII.lean). Perpendiculars take
# I.12's form, as in II.12. The design is in docs/briefs/0004-book-III.md; III.5's
# statement, and the readings of cutting and of contact within and without, are as
# docs/briefs/0008-centre.md, section 7, restates them.
BOOK_III = {
    1: "{A B : Point} {ABC : Circle} (hA : OnCircle A ABC)\n"
       "    (hB : OnCircle B ABC) (hAB : A ≠ B) :\n"
       "    ∃ F C D E : Point, Centre F ABC ∧ Between A D B ∧ ‖A D‖ = ‖D B‖ ∧ OnCircle C ABC ∧\n"
       "      OnCircle E ABC ∧ Between C D E ∧ ∠ A D C = ∟ ∧ Between C F E ∧ ‖C F‖ = ‖F E‖",
    2: "{A B : Point} {ABC : Circle} (hA : OnCircle A ABC)\n"
       "    (hB : OnCircle B ABC) :\n"
       "    ∀ E : Point, Between A E B → InsideCircle E ABC",
    3: "{A B E F : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)\n"
       "    (hB : OnCircle B ABC) (hAFB : Between A F B) (hE_AB : ¬ Collinear A B E) :\n"
       "    (‖A F‖ = ‖F B‖ → ∠ A F E = ∟ ∧ ∠ B F E = ∟) ∧ (∠ A F E = ∟ → ‖A F‖ = ‖F B‖)",
    4: "{A B C D E : Point} {ABCD : Circle}\n"
       "    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)\n"
       "    (hD : OnCircle D ABCD) (hAEC : Between A E C) (hBED : Between B E D)\n"
       "    (hB_AC : ¬ Collinear A C B) (hAC : ∀ F : Point, Centre F ABCD → ¬ Collinear A C F)\n"
       "    (hBD : ∀ F : Point, Centre F ABCD → ¬ Collinear B D F) :\n"
       "    ¬ (‖A E‖ = ‖E C‖ ∧ ‖B E‖ = ‖E D‖)",
    5: "{E : Point} {ABC CDG : Circle} (hcut : CirclesCut ABC CDG) :\n"
       "    ¬ (Centre E ABC ∧ Centre E CDG)",
    6: "{C F : Point} {ABC CDE : Circle} (htouch : CirclesTouch ABC CDE C) :\n"
       "    ¬ (Centre F ABC ∧ Centre F CDE)",
    7: "{A D E F : Point} {ABCD : Circle} (hE : Centre E ABCD) (hA : OnCircle A ABCD)\n"
       "    (hD : OnCircle D ABCD) (hAED : Between A E D) (hEFD : Between E F D) :\n"
       "    (∀ B : Point, OnCircle B ABCD → B ≠ A → ‖F B‖ < ‖F A‖) ∧\n"
       "    (∀ G : Point, OnCircle G ABCD → G ≠ D → ‖F D‖ < ‖F G‖) ∧\n"
       "    (∀ B C : Point, OnCircle B ABCD → OnCircle C ABCD → SameSideOf B C A D →\n"
       "      ∠ A F B < ∠ A F C → ‖F C‖ < ‖F B‖) ∧\n"
       "    (∀ G : Point, OnCircle G ABCD → ¬ Collinear A D G → ∃ H : Point, OnCircle H ABCD ∧\n"
       "      OppositeSidesOf H G A D ∧ ‖F H‖ = ‖F G‖ ∧\n"
       "      ∀ K : Point, OnCircle K ABCD → ‖F K‖ = ‖F G‖ → K = G ∨ K = H)",
    8: "{A D G : Point} {ABC : Circle}\n"
       "    (hD : OutsideCircle D ABC) (hA : OnCircle A ABC) (hG : OnCircle G ABC)\n"
       "    (hDGA : Between D G A) (hGA : ∀ M : Point, Centre M ABC → Between G M A) :\n"
       "    (∀ E : Point, OnCircle E ABC → E ≠ A → ‖D E‖ < ‖D A‖) ∧\n"
       "    (∀ E F : Point, OnCircle E ABC → OnCircle F ABC →\n"
       "      (∃ H : Point, OnCircle H ABC ∧ Between D H E) →\n"
       "      (∃ L : Point, OnCircle L ABC ∧ Between D L F) →\n"
       "      SameSideOf E F D A → ∠ A D E < ∠ A D F → ‖D F‖ < ‖D E‖) ∧\n"
       "    (∀ K : Point, OnCircle K ABC → K ≠ G → ‖D G‖ < ‖D K‖) ∧\n"
       "    (∀ K L : Point, OnCircle K ABC → OnCircle L ABC →\n"
       "      (∃ C : Point, OnCircle C ABC ∧ Between D K C) →\n"
       "      (∃ F : Point, OnCircle F ABC ∧ Between D L F) →\n"
       "      SameSideOf K L D A → ∠ A D K < ∠ A D L → ‖D K‖ < ‖D L‖) ∧\n"
       "    (∀ K : Point, OnCircle K ABC → ¬ Collinear D A K → ∃ B : Point, OnCircle B ABC ∧\n"
       "      OppositeSidesOf B K D A ∧ ‖D B‖ = ‖D K‖ ∧\n"
       "      ∀ N : Point, OnCircle N ABC → ‖D N‖ = ‖D K‖ → N = K ∨ N = B)",
    9: "{A B C D : Point} {ABC : Circle}\n"
       "    (hA : OnCircle A ABC) (hB : OnCircle B ABC)\n"
       "    (hC : OnCircle C ABC) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)\n"
       "    (hDA : ‖D A‖ = ‖D B‖) (hDB : ‖D B‖ = ‖D C‖) :\n"
       "    Centre D ABC",
    10: "{B G H : Point} {ABC DEF : Circle}\n"
        "    (hB₁ : OnCircle B ABC) (hB₂ : OnCircle B DEF)\n"
        "    (hG₁ : OnCircle G ABC) (hG₂ : OnCircle G DEF) (hH₁ : OnCircle H ABC)\n"
        "    (hH₂ : OnCircle H DEF) (hBG : B ≠ G) (hBH : B ≠ H) (hGH : G ≠ H) :\n"
        "    ABC = DEF",
    11: "{A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)\n"
        "    (htouch : TouchesInternally ABC ADE A) :\n"
        "    Between F G A",
    12: "{A F G : Point} {ABC ADE : Circle} (hF : Centre F ABC) (hG : Centre G ADE)\n"
        "    (htouch : TouchesExternally ABC ADE A) :\n"
        "    Between F A G",
    13: "{A B C D : Point} {ABDC EBFD ACK : Circle} :\n"
        "    ((TouchesInternally ABDC EBFD D ∨ TouchesInternally EBFD ABDC D) →\n"
        "      OnCircle B ABDC → OnCircle B EBFD → B = D) ∧\n"
        "    (TouchesExternally ACK ABDC A → OnCircle C ACK → OnCircle C ABDC → C = A)",
    14: "{A B C D E F G : Point} {ABDC : Circle} (hE : Centre E ABDC) (hA : OnCircle A ABDC)\n"
        "    (hB : OnCircle B ABDC) (hC : OnCircle C ABDC) (hD : OnCircle D ABDC)\n"
        "    (hE_AB : ¬ Collinear A B E) (hE_CD : ¬ Collinear C D E) (hF : Collinear A B F)\n"
        "    (hEF : ∀ P : Point, Collinear A B P → P ≠ F → ∠ E F P = ∟) (hG : Collinear C D G)\n"
        "    (hEG : ∀ P : Point, Collinear C D P → P ≠ G → ∠ E G P = ∟) :\n"
        "    ‖A B‖ = ‖C D‖ ↔ ‖E F‖ = ‖E G‖",
    15: "{A B C D E F G H K : Point} {ABCD : Circle} (hE : Centre E ABCD)\n"
        "    (hA : OnCircle A ABCD) (hD : OnCircle D ABCD) (hAED : Between A E D)\n"
        "    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hF : OnCircle F ABCD)\n"
        "    (hG : OnCircle G ABCD) (hE_BC : ¬ Collinear B C E) (hE_FG : ¬ Collinear F G E)\n"
        "    (hH : Collinear B C H) (hEH : ∀ P : Point, Collinear B C P → P ≠ H → ∠ E H P = ∟)\n"
        "    (hK : Collinear F G K) (hEK : ∀ P : Point, Collinear F G P → P ≠ K → ∠ E K P = ∟)\n"
        "    (hnearer : ‖E H‖ < ‖E K‖) :\n"
        "    ‖B C‖ < ‖A D‖ ∧ ‖F G‖ < ‖B C‖",
    16: "{A B D E : Point} {ABC : Circle} (hD : Centre D ABC) (hA : OnCircle A ABC)\n"
        "    (hADB : Between A D B) (hE : ¬ Collinear A B E) (hBAE : ∠ B A E = ∟) :\n"
        "    (∀ P : Point, Collinear A E P → P ≠ A → OutsideCircle P ABC) ∧\n"
        "    (∀ F : Point, ¬ Collinear A E F → ∃ G : Point, Collinear A F G ∧ InsideCircle G ABC)",
    17: "{A : Point} {BCD : Circle} (hA : OutsideCircle A BCD) :\n"
        "    ∃ B : Point, OnCircle B BCD ∧ Touches A B BCD",
    18: "{C D E F : Point} {ABC : Circle} (hF : Centre F ABC) (hC : OnCircle C ABC)\n"
        "    (hDE : Touches D E ABC) (hCDE : Collinear D E C) :\n"
        "    ∀ P : Point, Collinear D E P → P ≠ C → ∠ F C P = ∟",
    19: "{A C D E : Point} {ABC : Circle} (hC : OnCircle C ABC) (hDE : Touches D E ABC)\n"
        "    (hCDE : Collinear D E C) (hA : ¬ Collinear D E A)\n"
        "    (hCA : ∀ P : Point, Collinear D E P → P ≠ C → ∠ A C P = ∟) :\n"
        "    ∀ F : Point, Centre F ABC → Collinear A C F",
    20: "{A B C E : Point} {ABC : Circle} (hE : Centre E ABC) (hA : OnCircle A ABC)\n"
        "    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hEA : SameSideOf E A B C) :\n"
        "    ∠ B E C = ∠ B A C + ∠ B A C",
    21: "{A B D E : Point} {ABCD : Circle}\n"
        "    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hD : OnCircle D ABCD)\n"
        "    (hE : OnCircle E ABCD) (hAE : SameSideOf A E B D) :\n"
        "    ∠ B A D = ∠ B E D",
    22: "{A B C D : Point} {ABCD : Circle}\n"
        "    (hA : OnCircle A ABCD) (hB : OnCircle B ABCD) (hC : OnCircle C ABCD)\n"
        "    (hD : OnCircle D ABCD) (hAC : OppositeSidesOf A C B D) :\n"
        "    ∠ A B C + ∠ A D C = ∟ + ∟ ∧ ∠ B A D + ∠ D C B = ∟ + ∟",
    23: "{A B C D : Point} {ACB ADB : Circle} (hA₁ : OnCircle A ACB)\n"
        "    (hB₁ : OnCircle B ACB) (hC : OnCircle C ACB) (hA₂ : OnCircle A ADB)\n"
        "    (hB₂ : OnCircle B ADB) (hD : OnCircle D ADB) (hCD : SameSideOf C D A B)\n"
        "    (hsim : ∠ A C B = ∠ A D B) :\n"
        "    ACB = ADB",
    24: "{A B C D E F : Point} {AEB CFD : Circle} (hA : OnCircle A AEB)\n"
        "    (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD) (hD : OnCircle D CFD)\n"
        "    (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E) (hF_CD : ¬ Collinear C D F)\n"
        "    (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :\n"
        "    Arc.Congruent ⟨AEB, A, B, E⟩ ⟨CFD, C, D, F⟩",
    25: "{A C P : Point} {S : Point → Prop} (hP : ¬ Collinear A C P)\n"
        "    (hmeet : ∀ X Y : Point, Between A X C → SameSideOf Y P A C →\n"
        "      ∃ B : Point, S B ∧ OnRay B X Y) :\n"
        "    ∃ (B D E : Point) (γ : Circle), S B ∧ SameSideOf B P A C ∧ Between A D C ∧\n"
        "      ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E γ ∧ OnCircle A γ ∧ OnCircle B γ ∧\n"
        "      OnCircle C γ ∧ Collinear D B E ∧\n"
        "      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧\n"
        "      (∠ A B D < ∠ B A D → SameSideOf E B A C)",
    26: "{A B C D E F G H K L : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)\n"
        "    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)\n"
        "    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)\n"
        "    (hF : OnCircle F DEF) (hAK : OppositeSidesOf A K B C) (hDL : OppositeSidesOf D L E F) :\n"
        "    (OppositeSidesOf G K B C → OppositeSidesOf H L E F → ∠ B G C = ∠ E H F →\n"
        "      circumference ABC B K C = circumference DEF E L F ∧\n"
        "        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩) ∧\n"
        "    (∠ B A C = ∠ E D F →\n"
        "      circumference ABC B K C = circumference DEF E L F ∧\n"
        "        Arc.Congruent ⟨ABC, B, C, K⟩ ⟨DEF, E, F, L⟩)",
    27: "{A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)\n"
        "    (hG : Centre G ABC) (hH : Centre H DEF) (hA : OnCircle A ABC) (hB : OnCircle B ABC)\n"
        "    (hC : OnCircle C ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)\n"
        "    (hF : OnCircle F DEF) (hBAC : Triangle B A C) (hEDF : Triangle E D F)\n"
        "    (heq : standing ABC B A C = standing DEF E D F) :\n"
        "    ∠ B A C = ∠ E D F ∧\n"
        "      (SameSideOf G A B C → SameSideOf H D E F → ∠ B G C = ∠ E H F)",
    28: "{A B C D E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)\n"
        "    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hD : OnCircle D DEF) (hE : OnCircle E DEF)\n"
        "    (hCG : OppositeSidesOf C G A B) (hFH : OppositeSidesOf F H D E) (hAB : ‖A B‖ = ‖D E‖)\n"
        "    (hABC : circumference ABC A G B ≤ circumference ABC A C B)\n"
        "    (hDEF : circumference DEF D H E ≤ circumference DEF D F E) :\n"
        "    (circumference ABC A C B = circumference DEF D F E ∧\n"
        "        Arc.Congruent ⟨ABC, A, B, C⟩ ⟨DEF, D, E, F⟩) ∧\n"
        "      (circumference ABC A G B = circumference DEF D H E ∧\n"
        "        Arc.Congruent ⟨ABC, A, B, G⟩ ⟨DEF, D, E, H⟩)",
    29: "{B C E F G H : Point} {ABC DEF : Circle} (hcircles : EqualCircles ABC DEF)\n"
        "    (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hE : OnCircle E DEF) (hF : OnCircle F DEF)\n"
        "    (hG : ¬ Collinear B C G) (hH : ¬ Collinear E F H)\n"
        "    (heq : circumference ABC B G C = circumference DEF E H F) :\n"
        "    ‖B C‖ = ‖E F‖",
    30: "{A B : Point} {ADB : Circle} (hA : OnCircle A ADB) (hB : OnCircle B ADB) :\n"
        "    ∀ P : Point, ¬ Collinear A B P → ∃ D : Point, OnCircle D ADB ∧ SameSideOf D P A B ∧\n"
        "      standing ADB A B D = standing ADB D A B",
    31: "{A B C E : Point} {ABCD : Circle} (hE : Centre E ABCD) (hA : OnCircle A ABCD)\n"
        "    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hBEC : Between B E C) (hAB : A ≠ B)\n"
        "    (hAC : A ≠ C) :\n"
        "    ∠ B A C = ∟ ∧\n"
        "      (∀ X : Point, OnCircle X ABCD → SameSideOf X B A C → ∠ A X C < ∟) ∧\n"
        "      ∀ D : Point, OnCircle D ABCD → OppositeSidesOf B D A C → ∟ < ∠ A D C",
    32: "{B D E F : Point} {ABCD : Circle} (hB : OnCircle B ABCD)\n"
        "    (hD : OnCircle D ABCD) (hBD : B ≠ D) (hEF : Touches E F ABCD) (hEBF : Between E B F) :\n"
        "    (∀ A : Point, OnCircle A ABCD → OppositeSidesOf A F B D → ∠ F B D = ∠ B A D) ∧\n"
        "    (∀ C : Point, OnCircle C ABCD → SameSideOf C F B D → ∠ E B D = ∠ D C B)",
    33: "{A B C₁ C C₂ : Point} (hAB : A ≠ B) (hC : Triangle C₁ C C₂) :\n"
        "    ∃ (AEB : Circle) (E : Point), OnCircle A AEB ∧ OnCircle B AEB ∧ OnCircle E AEB ∧\n"
        "      ¬ Collinear A B E ∧ ∠ A E B = ∠ C₁ C C₂",
    34: "{D₁ D D₂ : Point} (ABC : Circle) (hD : Triangle D₁ D D₂) :\n"
        "    ∃ A B C : Point, OnCircle A ABC ∧ OnCircle B ABC ∧ OnCircle C ABC ∧ Triangle B A C ∧\n"
        "      ∠ B A C = ∠ D₁ D D₂",
    35: "{A B C D E : Point} {ABCD : Circle} (hA : OnCircle A ABCD)\n"
        "    (hB : OnCircle B ABCD) (hC : OnCircle C ABCD) (hD : OnCircle D ABCD)\n"
        "    (hAEC : Between A E C) (hBED : Between B E D) :\n"
        "    rect A E E C = rect D E E B",
    36: "{A B C D : Point} {ABC : Circle} (hD : OutsideCircle D ABC)\n"
        "    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hDCA : Between D C A)\n"
        "    (hDB : Touches D B ABC) :\n"
        "    rect A D D C = sq D B",
    37: "{A B C D : Point} {ABC : Circle} (hD : OutsideCircle D ABC)\n"
        "    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hDCA : Between D C A)\n"
        "    (h : rect A D D C = sq D B) :\n"
        "    Touches D B ABC",
}

# Declarations that follow their proposition in the same file: each has a docstring and a
# statement ending in `sorry`.
FOLLOWUPS = {
    ("III", 1): [(
        "porism",
        "The Porism to III.1: \"if in a circle a straight line cut a straight line into two\n"
        "equal parts and at right angles, the centre of the circle is on the cutting straight\n"
        "line.\" The straight line `DC` cuts `AB`, a straight line in the circle, at its\n"
        "middle point `D` and at right angles; the centre `G` is on `DC`. III.9 and III.10\n"
        "cite it.",
        "{A B C D G : Point} {ABC : Circle} (hG : Centre G ABC) (hA : OnCircle A ABC)\n"
        "    (hB : OnCircle B ABC) (hADB : Between A D B) (hAD : ‖A D‖ = ‖D B‖)\n"
        "    (hC : ¬ Collinear A B C) (hADC : ∠ A D C = ∟) :\n"
        "    Collinear D C G",
    )],
    ("III", 16): [(
        "porism",
        "The Porism to III.16: \"the straight line drawn at right angles to the diameter of a\n"
        "circle from its extremity touches the circle.\" The diameter through `A` is the\n"
        "straight line `AD`, `D` the centre, and `AE` is drawn at right angles to it. III.17,\n"
        "III.33 and III.37 cite it, and Book IV after them.",
        "{A D E : Point} {ABC : Circle} (hD : Centre D ABC) (hA : OnCircle A ABC)\n"
        "    (hE : ¬ Collinear D A E) (hDAE : ∠ D A E = ∟) :\n"
        "    Touches A E ABC",
    )],
    ("III", 24): [(
        "equalCircles",
        "**III.24, the circles and the measures** (companion of III.24, \"III.24 equalCircles\").\n"
        "Similar segments on equal straight lines lie in equal circles, and their circumferences are\n"
        "equal in measure.",
        "{A B C D E F : Point} {AEB CFD : Circle} (hA : OnCircle A AEB)\n"
        "    (hB : OnCircle B AEB) (hE : OnCircle E AEB) (hC : OnCircle C CFD) (hD : OnCircle D CFD)\n"
        "    (hF : OnCircle F CFD) (hE_AB : ¬ Collinear A B E) (hF_CD : ¬ Collinear C D F)\n"
        "    (hAB : ‖A B‖ = ‖C D‖) (hsim : ∠ A E B = ∠ C F D) :\n"
        "    EqualCircles AEB CFD ∧ circumference AEB A E B = circumference CFD C F D",
    ), (
        "equalMeasure",
        "**Congruent segments have equal circumferences** (companion of III.24, \"III.24\n"
        "equalMeasure\"). If two drawn segments are congruent, their circumferences are equal in\n"
        "measure.",
        "{a b : Arc} (ha : a.Drawn) (hb : b.Drawn)\n"
        "    (h : Arc.Congruent a b) : a.measure = b.measure",
    )],
    ("III", 25): [(
        "complete",
        "**III.25's circle is the segment's circle** (companion of III.25, \"III.25 complete\").\n"
        "Let A, C be points of a circle α, and B a point of its arc on P's side of AC. Any circle γ\n"
        "through A, B and C is α, and every point of the arc AC on P's side is on γ.",
        "{A C P B : Point} {α γ : Circle} (hA : OnCircle A α)\n"
        "    (hC : OnCircle C α) (hB : OnArc B ⟨α, A, C, P⟩) (hBP : SameSideOf B P A C)\n"
        "    (hAγ : OnCircle A γ) (hBγ : OnCircle B γ) (hCγ : OnCircle C γ) :\n"
        "    γ = α ∧ ∀ X : Point, OnArc X ⟨α, A, C, P⟩ → OnCircle X γ",
    ), (
        "of_circle",
        "**Today's III.25, from the restated core** (companion of III.25, \"III.25 of_circle\").\n"
        "Handed the circle ABC, the core finds a circle that is ABC itself, so its centre E is the\n"
        "centre of ABC.",
        "{A C : Point} {ABC : Circle} (hA : OnCircle A ABC)\n"
        "    (hC : OnCircle C ABC) :\n"
        "    ∀ P : Point, ¬ Collinear A C P → ∃ B D E : Point, OnCircle B ABC ∧ SameSideOf B P A C ∧\n"
        "      Between A D C ∧ ‖A D‖ = ‖D C‖ ∧ ∠ A D B = ∟ ∧ Centre E ABC ∧ Collinear D B E ∧\n"
        "      (∠ B A D < ∠ A B D → OppositeSidesOf E B A C) ∧ (∠ A B D = ∠ B A D → E = D) ∧\n"
        "      (∠ A B D < ∠ B A D → SameSideOf E B A C)",
    )],
}

BOOKS = {"I": BOOK_I, "II": BOOK_II, "III": BOOK_III}

# What every proposition of a book imports besides Book Zero: the ground its proofs
# share, which cites propositions of earlier books.
GROUNDWORK = {"II": ["Elements.BookII.Rectangles"], "III": ["Elements.BookIII.Squares"]}

# Ground that cites propositions of the book itself, imported from a given proposition
# on: Book III's facts about circumferences rest on III.20-III.22.
LATER_GROUNDWORK = {"III": {23: ["Elements.BookIII.Circumferences"]}}

WIDTH = 100


NBSP = "\u00a0"


def comment_lines(paragraph: str) -> list[str]:
    # Keep each bracketed citation ("[Post. 3]") glued to the word before it.
    glued = re.sub(r" (\[[^\]]*\])", lambda m: NBSP + m.group(1).replace(" ", NBSP), paragraph)
    lines = textwrap.wrap(glued, width=WIDTH - 5, break_long_words=False,
                          break_on_hyphens=False, initial_indent="  -- ",
                          subsequent_indent="  -- ")
    return [line.replace(NBSP, " ") for line in lines]


def docstring_text(text: str) -> str:
    """A docstring kept as written, line breaks and all."""
    return "/-- " + text + " -/"


def docstring(enunciation: str) -> str:
    lines = textwrap.wrap(enunciation, width=WIDTH - 4, break_long_words=False,
                          break_on_hyphens=False)
    return "/-- " + "\n".join(lines) + " -/"


def render(book: str, n: int, signature: str) -> str:
    _, enunciation, proof = heath.read(book, n)
    # Every proposition Euclid cites comes before this one: in an earlier book, or
    # earlier in this one.
    cites = sorted((c for c in heath.citations(proof)
                    if heath.prop_key(c) < (heath.arabic(book), n)), key=heath.prop_key)
    imports = ["import Elements.Figure.Basics"]
    imports += [f"import {m}" for m in GROUNDWORK.get(book, [])]
    imports += [f"import {m}" for first, ms in LATER_GROUNDWORK.get(book, {}).items()
                if n >= first for m in ms]
    imports += [f"import Elements.Book{c.split('.')[0]}.Prop{int(c.split('.')[1]):02d}"
                for c in cites]
    body = []
    for p in proof:
        body.extend(comment_lines(p))
    followups = "".join(
        f"\n{docstring_text(doc)}\ntheorem Prop{n}.{name} {sig} := by\n  sorry\n"
        for name, doc, sig in FOLLOWUPS.get((book, n), []))
    return f"""{chr(10).join(imports)}

/-!
# Book {book}, Proposition {n}

Euclid's text, in Heath's translation: [`heath/{book}/{n:02d}.md`](../../heath/{book}/{n:02d}.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.Book{book}

open Tacit

{docstring(enunciation)}
theorem Prop{n} {signature} := by
{chr(10).join(body)}
  sorry
{followups}
end Elements.Book{book}
"""


def main() -> None:
    book = sys.argv[1] if len(sys.argv) > 1 else "I"
    out_dir = heath.ROOT / "Elements" / f"Book{book}"
    out_dir.mkdir(parents=True, exist_ok=True)
    made = 0
    for n, signature in BOOKS[book].items():
        path = out_dir / f"Prop{n:02d}.lean"
        if path.exists():
            continue
        path.write_text(render(book, n, signature))
        made += 1
    print(f"Book {book}: created {made} proposition files")


if __name__ == "__main__":
    main()
