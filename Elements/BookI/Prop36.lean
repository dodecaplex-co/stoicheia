import Elements.Figure.Basics
import Elements.BookI.Prop33
import Elements.BookI.Prop34
import Elements.BookI.Prop35

/-!
# Book I, Proposition 36

Euclid's text, in Heath's translation: [`heath/I/36.md`](../../heath/I/36.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookI

open Tacit

/-- Parallelograms which are on equal bases and in the same parallels are equal to one another. -/
theorem Prop36 {A B C D E F G H : Point} (h₁ : Parallelogram A B C D) (h₂ : Parallelogram E F G H)
    (hbase : ‖B C‖ = ‖F G‖)
    (hAH : ∃ L : Line, OnLine A L ∧ OnLine D L ∧ OnLine E L ∧ OnLine H L)
    (hBG : ∃ L : Line, OnLine B L ∧ OnLine C L ∧ OnLine F L ∧ OnLine G L) :
    quadArea A B C D = quadArea E F G H := by
  -- Let ABCD, EFGH be parallelograms which are on equal bases BC, FG and in the same parallels
  -- AH, BG;
  obtain ⟨AH, hA, hD, hE, hH⟩ := hAH
  obtain ⟨BG, hB, hC, hF, hG⟩ := hBG
  have hpar : Parallel AH BG := (h₁.2.parallel hB hC hD hA).symm
  -- I say that the parallelogram ABCD is equal to EFGH.
  /- Euclid's case: EH runs the same way as BC, so C and H lie on one side of BE.
     We give his argument first, then turn the lettering round for the other case. -/
  have key : ∀ {E F G H : Point}, Parallelogram E F G H → ‖B C‖ = ‖F G‖ →
      OnLine E AH → OnLine H AH → OnLine F BG → OnLine G BG → SameSideOf C H B E →
      quadArea A B C D = quadArea E F G H := by
    intro E F G H h₂ hbase hE hH hF hG
    -- For let BE, CH be joined.
    /- The joining straight lines are named by their ends in I.33 below. -/
    -- Then, since BC is equal to FG,
    have hBC_FG : ‖B C‖ = ‖F G‖ := hbase
    -- while FG is equal to EH,
    have hEH : ‖E H‖ = ‖F G‖ := (Prop34 (A := E) (B := H) (C := F) (D := G) h₂).1
    -- BC is also equal to EH. [C.N. 1]
    have hBC_EH : ‖B C‖ = ‖E H‖ := CommonNotion1 hBC_FG hEH
    -- But they are also parallel.
    have hBCEH : AreParallel B C E H :=
      AreParallel.of_parallel h₁.2.1 h₂.2.2.1.symm hB hC hE hH hpar.symm
    -- And EB, HC join them;
    intro hdir
    -- but straight lines joining equal and parallel straight lines (at the extremities which
    -- are) in the same directions (respectively) are equal and parallel. [I. 33]
    have h33 := Prop33 hBCEH hBC_EH hdir
    -- Therefore EBCH is a parallelogram. [I. 34]
    /- Both pairs of opposite sides are parallel, which is the definition of a
       parallelogram. I.34 supplies FG = EH earlier in the argument. -/
    have hEBCH : Parallelogram E B C H :=
      ⟨h33.2.swap_left,
        AreParallel.of_parallel h₁.2.1 h₂.2.2.1 hB hC hH hE hpar.symm⟩
    -- And it is equal to ABCD;
    have e₁ : quadArea A B C D = quadArea E B C H := by
      -- for it has the same base BC with it, and is in the same parallels BC, AH with it. [I. 35]
      exact Prop35 h₁ hEBCH ⟨AH, hA, hD, hE, hH⟩
    -- For the same reason also EFGH is equal to the same EBCH; [I. 35]
    have harea : quadArea F E H G = quadArea B E H C :=
      Prop35 h₂.reverse.rotate.rotate.rotate hEBCH.reverse.rotate.rotate.rotate
        ⟨BG, hF, hG, hB, hC⟩
    /- This time the common base is EH. Book Zero turns both areas back to their
       given names, whichever diameter measures them. -/
    have e₂ : quadArea E F G H = quadArea E B C H := calc
      quadArea E F G H = quadArea F G H E := h₂.quadArea_rotate.symm
      _ = quadArea F E H G := (quadArea_reverse F G H E).symm
      _ = quadArea B E H C := harea
      _ = quadArea B C H E := quadArea_reverse B C H E
      _ = quadArea E B C H := hEBCH.quadArea_rotate
    -- so that the parallelogram ABCD is also equal to EFGH. [C.N. 1]
    exact CommonNotion1 e₁ e₂
  /- Book Zero settles which way EH runs. In the second case EFGH is read as
     HGFE, and the same argument applies without changing its area. -/
  have hEHBC : AreParallel E H B C :=
    AreParallel.of_parallel h₂.2.2.1.symm h₁.2.1 hE hH hB hC hpar
  have hequal : quadArea A B C D = quadArea E F G H := by
    rcases hEHBC.sameSideOf_or with hs | hs
    · exact key h₂ hbase hE hH hF hG hs.swap
    · rw [key h₂.reverse.rotate (hbase.trans (len_symm F G)) hH hE hG hF hs.swap,
        quadArea_reverse, quadArea_rotate₂, h₂.quadArea_rotate]
  -- Therefore etc.
  exact hequal
  -- Q. E. D.

end Elements.BookI
