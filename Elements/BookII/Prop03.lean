import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop04
import Elements.BookI.Prop28
import Elements.BookI.Prop29
import Elements.BookI.Prop30
import Elements.BookI.Prop31
import Elements.BookI.Prop34
import Elements.BookI.Prop46
import Elements.BookI.HelpersParallels

/-!
# Book II, Proposition 3

Euclid's text, in Heath's translation: [`heath/II/03.md`](../../heath/II/03.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- If a straight line be cut at random, the rectangle contained by the whole and one of the
segments is equal to the rectangle contained by the segments and the square on the aforesaid
segment. -/
theorem Prop3 {A B C : Point} (hACB : Between A C B) :
    rect A B B C = rect A C C B + sq B C := by
  -- For let the straight line AB be cut at random at C;
  have hAB : A ≠ B := ne_of_between_ends hACB
  have hAC : A ≠ C := ne_of_between hACB
  have hCB : C ≠ B := (ne_of_between (between_symm hACB)).symm
  obtain ⟨AB, hA_AB, hB_AB⟩ := Postulate1 A B hAB
  have hC_AB : OnLine C AB := on_line_of_between_ends hACB hA_AB hB_AB
  -- I say that the rectangle contained by AB, BC is equal to the rectangle contained by AC, CB
  -- together with the square on BC.
  -- For let the square CDEB be described on CB; [I. 46]
  /- I.46 describes the square on the side of a point off CB (`exists_off_line`), and
     `Square.described` says it is the square on CB. -/
  obtain ⟨P, hP, -⟩ := exists_off_line hCB []
  obtain ⟨D, E, hsq, hD, hE⟩ := BookI.Prop46 hCB hP
  obtain ⟨hp, hDB⟩ := Square.described hsq hD hE
  -- let ED be drawn through to F,
  /- DE names the whole straight line. The parallel through A will find F on it. -/
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hp.2.1
  have hDE_AB : Parallel DE AB := hp.2.parallel hD_DE hE_DE hB_AB hC_AB
  -- and through A let AF be drawn parallel to either CD or BE. [I. 31]
  /- I.31 draws AF parallel to CD; I.30 finds its meeting with DE and makes it
     parallel to BE as well. -/
  obtain ⟨CD, hC_CD, hD_CD⟩ := Postulate1 C D hp.1.1
  obtain ⟨BE, hB_BE, hE_BE⟩ := Postulate1 B E hp.1.2.1.symm
  have hCD_BE : Parallel CD BE := hp.1.parallel hC_CD hD_CD hE_BE hB_BE
  obtain ⟨F, hF_DE, hDCAF⟩ :=
    BookI.Prop31.parallelogram hDE_AB hD_DE hC_AB hA_AB hAC.symm
  have hAF : A ≠ F := hDCAF.1.2.1
  obtain ⟨AF, hA_AF, hF_AF⟩ := Postulate1 A F hAF
  have hAF_CD : Parallel AF CD := (hDCAF.1.parallel hD_CD hC_CD hA_AF hF_AF).symm
  have hA_BE : ¬ OnLine A BE := fun h =>
    hCD_BE.not_onLine hC_CD ((line_unique hAB hA_AB hB_AB h hB_BE) ▸ hC_AB)
  have hAF_BE : Parallel AF BE :=
    BookI.Prop30.parallel hAF_CD hCD_BE.symm fun e => hA_BE (e ▸ hA_AF)
  -- Then AE is equal to AD, CE.
  /- Parallels keep order: D lies between F and E, as C lies between A and B.
     Thus CD cuts the whole AFEB into AFDC and CDEB. -/
  have hFDE : Between F D E :=
    Parallel.between hAF_CD hCD_BE.symm hA_AF hC_CD hB_BE hACB hF_AF hD_CD hE_BE
      ⟨DE, hF_DE, hD_DE, hE_DE⟩
  have hAFDC : Parallelogram A F D C := hDCAF.rotate.rotate
  have hwhole : quadArea A F E B = quadArea A F D C + quadArea C D E B :=
    quadArea_add_of_parallelograms hAFDC hp hACB hFDE
  -- Now AE is the rectangle contained by AB, BC, for it is contained by AB, BE, and BE is
  -- equal to BC;
  /- AE is the parallelogram BAFE, and its angle at B is the square's right angle, so it
     is a rectangle (`Rectangle.of_right`), contained by AB and BE (`Rectangle.eq_rect`). -/
  have hFE : F ≠ E := ne_of_between_ends hFDE
  have hBAFE : Parallelogram B A F E :=
    ⟨AreParallel.of_parallel hAB.symm hFE hB_AB hA_AB hF_DE hE_DE hDE_AB.symm,
      AreParallel.of_parallel hAF hp.1.2.1 hA_AF hF_AF hE_BE hB_BE hAF_BE⟩
  have hAE : quadArea A F E B = rect A B B C := by
    rw [hBAFE.quadArea_rotate]
    refine (Rectangle.of_right hBAFE ?_).eq_rect (len_symm B A) ?_
    · rw [angle_onRay_right (OnRay.of_beyond (between_symm hACB)) hp.1.2.1]
      exact hsq.2.2.2.2.2.2
    · rw [len_symm B E]; exact hsq.2.2.1
  -- AD is the rectangle AC, CB, for DC is equal to CB;
  have hAD : quadArea A F D C = rect A C C B := by
    have hCAFD : Parallelogram C A F D := hDCAF.rotate
    rw [hCAFD.quadArea_rotate]
    have hD_AB : ¬ OnLine D AB := hDE_AB.not_onLine hD_DE
    /- The angle DCA adjacent to the square's right angle BCD is right
       (System E, Diagram-angle 3). -/
    have hright : ∠ D C A = ∟ := by
      have h := hsq.2.2.2.1
      rw [adjacent_eq_of_right hB_AB hA_AB (between_symm hACB) hD_AB h] at h
      exact h
    exact (Rectangle.of_right hCAFD hright).eq_rect (len_symm C A) hsq.len_eq.symm
  -- and DB is the square on CB.
  have hDB' : quadArea C D E B = sq B C := hDB.trans (sq_symm C B)
  -- Therefore the rectangle contained by AB, BC is equal to the rectangle contained by AC, CB
  -- together with the square on BC.
  rw [← hAE, hwhole, hAD, hDB']
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookII
