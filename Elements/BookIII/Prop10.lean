import Elements.Figure.Basics
import Elements.BookIII.Squares
import Elements.BookI.Prop10
import Elements.BookI.Prop11
import Elements.BookI.Prop13
import Elements.BookI.Prop17
import Elements.BookIII.Prop01
import Elements.BookIII.Prop02

/-!
# Book III, Proposition 10

Euclid's text, in Heath's translation: [`heath/III/10.md`](../../heath/III/10.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If the angle BKC is right, so is the angle BKX for any other point X of the straight
line KC, on either side of K. -/
theorem Prop10.right_on_line {B K C X : Point} {N : Line} (hK : OnLine K N) (hC : OnLine C N)
    (hX : OnLine X N) (hKC : K ≠ C) (hXK : X ≠ K) (hB : ¬ OnLine B N) (hBKC : ∠ B K C = ∟) :
    ∠ B K X = ∟ := by
  have hBK : B ≠ K := fun e => hB (e ▸ hK)
  by_cases hb : Between X K C
  · have h := adjacent_eq_of_right hC hX (between_symm hb) hB
      (by rw [angle_symm hKC.symm hBK]; exact hBKC)
    rw [← h, angle_symm hKC.symm hBK]; exact hBKC
  · rw [angle_onRay_right ⟨hKC, hXK, ⟨N, hK, hC, hX⟩, hb⟩ hBK]; exact hBKC

/-- The straight lines at right angles to BH at K and to BG at L have at most one
common point. Euclid takes for granted that they are two straight lines; as in III.9
(`Prop9.apart`), were they one, the triangle BKL would have two right angles. -/
theorem Prop10.meet_once {B G H K L C O P Q : Point} (hBHG : Triangle B H G)
    (hBKH : Between B K H) (hBLG : Between B L G)
    (hC : ¬ Collinear B H C) (hBKC : ∠ B K C = ∟) (hO : ¬ Collinear B G O)
    (hBLO : ∠ B L O = ∟)
    (hKCP : Collinear K C P) (hKCQ : Collinear K C Q) (hLOP : Collinear L O P)
    (hLOQ : Collinear L O Q) : P = Q := by
  refine Classical.byContradiction fun hPQ => ?_
  obtain ⟨M₁, hK₁, hC₁, hP₁⟩ := hKCP
  obtain ⟨M₂, hK₂, hC₂, hQ₂⟩ := hKCQ
  obtain ⟨M₃, hL₃, hO₃, hP₃⟩ := hLOP
  obtain ⟨M₄, hL₄, hO₄, hQ₄⟩ := hLOQ
  obtain ⟨BH, hB_BH, hH_BH⟩ := Postulate1 B H (ne_of_between_ends hBKH)
  have hK_BH := on_line_of_between_ends hBKH hB_BH hH_BH
  obtain ⟨BG, hB_BG, hG_BG⟩ := Postulate1 B G (ne_of_between_ends hBLG)
  have hL_BG := on_line_of_between_ends hBLG hB_BG hG_BG
  have hKC : K ≠ C := fun e => hC ⟨BH, hB_BH, hH_BH, e ▸ hK_BH⟩
  have hLO : L ≠ O := fun e => hO ⟨BG, hB_BG, hG_BG, e ▸ hL_BG⟩
  obtain rfl := line_unique hKC hK₁ hC₁ hK₂ hC₂
  obtain rfl := line_unique hLO hL₃ hO₃ hL₄ hO₄
  obtain rfl := line_unique hPQ hP₁ hQ₂ hP₃ hQ₄
  /- Now one straight line, M₁, passes through K, C, L and O. -/
  have hKL : K ≠ L := by
    rintro rfl
    have hBK : B ≠ K := ne_of_between hBKH
    exact hBHG ⟨BH, hB_BH, hH_BH, (line_unique hBK hB_BG hL_BG hB_BH hK_BH) ▸ hG_BG⟩
  have hB : ¬ OnLine B M₁ := fun hB =>
    hC ⟨BH, hB_BH, hH_BH,
      (line_unique (ne_of_between hBKH) hB hK₁ hB_BH hK_BH) ▸ hC₁⟩
  have h₁ : ∠ B K L = ∟ := Prop10.right_on_line hK₁ hC₁ hL₃ hKC hKL.symm hB hBKC
  have h₂ : ∠ B L K = ∟ := Prop10.right_on_line hL₃ hO₃ hK₁ hLO hKL hB hBLO
  have h17 := (BookI.Prop17 (Triangle.of_line hK₁ hL₃ hKL hB).cab).1
  rw [h₁, angle_symm hKL (fun e => hB (by rw [e]; exact hL₃)), h₂] at h17
  exact lt_irrefl _ h17

/-- A circle does not cut a circle at more points than two. -/
theorem Prop10 {B G H : Point} {ABC DEF : Circle}
    (hB₁ : OnCircle B ABC) (hB₂ : OnCircle B DEF)
    (hG₁ : OnCircle G ABC) (hG₂ : OnCircle G DEF) (hH₁ : OnCircle H ABC)
    (hH₂ : OnCircle H DEF) (hBG : B ≠ G) (hBH : B ≠ H) (hGH : G ≠ H) :
    ABC = DEF := by
  -- For, if possible, let the circle ABC cut the circle DEF at more points than two, namely B,
  -- G, F, H;
  refine Classical.byContradiction fun hne => ?_
  /- Three common points suffice; Euclid never uses the fourth, F. -/
  have hBHG : Triangle B H G := Prop2.triangle hB₁ hH₁ hG₁ hBH hGH.symm hBG
  -- let BH, BG be joined and bisected at the points K, L,
  obtain ⟨BH, hB_BH, hH_BH⟩ := Postulate1 B H hBH
  obtain ⟨BG, hB_BG, hG_BG⟩ := Postulate1 B G hBG
  obtain ⟨K, hBKH, hBK⟩ := BookI.Prop10 hBH
  obtain ⟨L, hBLG, hBL⟩ := BookI.Prop10 hBG
  have hK_BH := on_line_of_between_ends hBKH hB_BH hH_BH
  have hL_BG := on_line_of_between_ends hBLG hB_BG hG_BG
  -- and from K, L let KC, LM be drawn at right angles to BH, BG and carried through to the
  -- points A, E.
  obtain ⟨X, hXG, hKX⟩ := BookI.Prop11 hBH ⟨BH, hB_BH, hH_BH, hK_BH⟩ hBHG
  obtain ⟨Y, hYH, hLY⟩ := BookI.Prop11 hBG ⟨BG, hB_BG, hG_BG, hL_BG⟩ hBHG.acb
  have hX_BH : ¬ OnLine X BH := hXG.triangle.off_line hB_BH hH_BH
  have hY_BG : ¬ OnLine Y BG := hYH.triangle.off_line hB_BG hG_BG
  have hKX_ne : K ≠ X := fun e => hX_BH (e ▸ hK_BH)
  have hLY_ne : L ≠ Y := fun e => hY_BG (e ▸ hL_BG)
  /- The argument needs only a point of each perpendicular besides K and L, never where
     the perpendicular meets the circle; so KX is produced to C and YL to O [Post. 2], and
     A and E are not named. O is on the other side of BG from H, as in the figure. -/
  obtain ⟨AC, hK_AC, hX_AC⟩ := Postulate1 K X hKX_ne
  obtain ⟨C, hKXC⟩ := produce hKX_ne
  have hC_AC := on_line_of_between hKXC hK_AC hX_AC
  obtain ⟨NO, hL_NO, hY_NO⟩ := Postulate1 L Y hLY_ne
  obtain ⟨O, hYLO⟩ := produce hLY_ne.symm
  have hO_NO := on_line_of_between hYLO hY_NO hL_NO
  have hBK_ne : B ≠ K := ne_of_between hBKH
  have hBL_ne : B ≠ L := ne_of_between hBLG
  have hBKC : ∠ B K C = ∟ := by
    rw [angle_onRay_right (OnRay.of_beyond hKXC) hBK_ne]
    exact hKX B ⟨BH, hB_BH, hH_BH, hB_BH⟩ hBK_ne
  have hB_NO : ¬ OnLine B NO := fun h =>
    hY_BG ((line_unique hBL_ne h hL_NO hB_BG hL_BG) ▸ hY_NO)
  have hYLB : ∠ Y L B = ∟ := by
    rw [angle_symm hLY_ne.symm hBL_ne]
    exact hLY B ⟨BG, hB_BG, hG_BG, hB_BG⟩ hBL_ne
  have hBLO : ∠ B L O = ∟ :=
    (adjacent_eq_of_right hY_NO hO_NO hYLO hB_NO hYLB).symm.trans hYLB
  have hKC : K ≠ C := ne_of_between_ends hKXC
  have hLO : L ≠ O := (ne_of_between (between_symm hYLO)).symm
  have hC_off : ¬ Collinear B H C := fun ⟨M, h1, h2, h3⟩ => hX_BH (by
    have e₁ := line_unique hBH h1 h2 hB_BH hH_BH
    have hK_M : OnLine K M := e₁ ▸ hK_BH
    have e₂ := line_unique hKC hK_M h3 hK_AC hC_AC
    exact e₁ ▸ e₂ ▸ hX_AC)
  have hO_off : ¬ Collinear B G O := fun ⟨M, h1, h2, h3⟩ => hY_BG (by
    have e₁ := line_unique hBG h1 h2 hB_BG hG_BG
    have hL_M : OnLine L M := e₁ ▸ hL_BG
    have e₂ := line_unique hLO hL_M h3 hL_NO hO_NO
    exact e₁ ▸ e₂ ▸ hY_NO)
  -- Then, since in the circle ABC a straight line AC cuts a straight line BH into two equal
  -- parts and at right angles,
  -- the centre of the circle ABC is on AC. [III. 1, Por.]
  obtain ⟨P, hP⟩ := exists_centre ABC
  have hP_AC : Collinear K C P := Prop1.porism hP hB₁ hH₁ hBKH hBK hC_off hBKC
  -- Again, since in the same circle ABC a straight line NO cuts a straight line BG into two
  -- equal parts and at right angles,
  -- the centre of the circle ABC is on NO.
  have hP_NO : Collinear L O P := Prop1.porism hP hB₁ hG₁ hBLG hBL hO_off hBLO
  -- But it was also proved to be on AC, and the straight lines AC, NO meet at no point except
  -- at P;
  /- AC and NO are two straight lines (`Prop10.meet_once`), so any point on both is P,
     even if P is K or L. -/
  have hmeet : ∀ Q : Point, Collinear K C Q → Collinear L O Q → Q = P :=
    fun Q hQ_AC hQ_NO =>
      Prop10.meet_once hBHG hBKH hBLG hC_off hBKC hO_off hBLO hQ_AC hP_AC hQ_NO hP_NO
  -- therefore the point P is the centre of the circle ABC.
  /- The centre the rule gives the circle ABC has already been named P. -/
  -- Similarly we can prove that P is also the centre of the circle DEF;
  obtain ⟨P', hP'⟩ := exists_centre DEF
  have hP'_AC : Collinear K C P' := Prop1.porism hP' hB₂ hH₂ hBKH hBK hC_off hBKC
  have hP'_NO : Collinear L O P' := Prop1.porism hP' hB₂ hG₂ hBLG hBL hO_off hBLO
  obtain rfl : P' = P := hmeet P' hP'_AC hP'_NO
  -- therefore the two circles ABC, DEF which cut one another have the same centre P: which is
  -- impossible. [III. 5]
  /- Heath's bracket gives III.5. `Prop5` asks that the circles cut one another, each
     passing within the other, and this statement gives only three common points, so it
     cannot serve. Heath states under III.5 what does: circles with one centre and one
     common point coincide altogether, here P and B (`circle_eq`). -/
  exact hne (circle_eq hP hP' hB₁ hB₂ rfl)
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookIII
