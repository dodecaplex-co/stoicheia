"""Create the Lean file for each proposition of a book: the statement in Heath's
letters, Heath's enunciation as its docstring, and every sentence of Euclid's
proof as a `--` comment, ending in `sorry`. That is the "sketch"; proofs are then
written between the comments.

Only creates files that don't exist yet, so it never overwrites a proof.

    python3 scripts/scaffold_book.py I
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
        "    ∃ F G : Point, OnRay F A B ∧ SameSideOf G P A B ∧ ∠ F A G = ∠ D C E",
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
        "    (hpar : AreParallel A D B C) :\n    △ A B C = △ D B C",
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

BOOKS = {"I": BOOK_I}

WIDTH = 100


NBSP = "\u00a0"


def comment_lines(paragraph: str) -> list[str]:
    # Keep each bracketed citation ("[Post. 3]") glued to the word before it.
    glued = re.sub(r" (\[[^\]]*\])", lambda m: NBSP + m.group(1).replace(" ", NBSP), paragraph)
    lines = textwrap.wrap(glued, width=WIDTH - 5, break_long_words=False,
                          break_on_hyphens=False, initial_indent="  -- ",
                          subsequent_indent="  -- ")
    return [line.replace(NBSP, " ") for line in lines]


def docstring(enunciation: str) -> str:
    lines = textwrap.wrap(enunciation, width=WIDTH - 4, break_long_words=False,
                          break_on_hyphens=False)
    return "/-- " + "\n".join(lines) + " -/"


def render(book: str, n: int, signature: str) -> str:
    _, enunciation, proof = heath.read(book, n)
    cites = sorted((c for c in heath.citations(proof) if c.startswith(f"{book}.")),
                   key=lambda c: int(c.split(".")[1]))
    imports = ["import Elements.Figure.Basics"]
    imports += [f"import Elements.Book{book}.Prop{int(c.split('.')[1]):02d}" for c in cites
                if int(c.split(".")[1]) < n]
    body = []
    for p in proof:
        body.extend(comment_lines(p))
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
