import Elements.Figure.Basics
import Elements.Figure.Circles
import Elements.BookIII.Squares
import Elements.BookIII.Feet
import Elements.BookIII.Circumferences
import Elements.BookI.Prop12
import Elements.BookI.Prop47
import Elements.BookII.Prop06
import Elements.BookIII.Prop03
import Elements.BookIII.Prop18

/-!
# Book III, Proposition 36

Euclid's text, in Heath's translation: [`heath/III/36.md`](../../heath/III/36.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookIII

open Tacit

/-- If a point be taken outside a circle and from it there fall on the circle two straight lines,
and if one of them cut the circle and the other touch it, the rectangle contained by the whole
of the straight line which cuts the circle and the straight line intercepted on it outside
between the point and the convex circumference will be equal to the square on the tangent. -/
theorem Prop36 {A B C D : Point} {ABC : Circle} (hD : OutsideCircle D ABC)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC) (hC : OnCircle C ABC) (hDCA : Between D C A)
    (hDB : Touches D B ABC) :
    rect A D D C = sq D B := by
  -- For let a point D be taken outside the circle ABC,
  have hDB' : D ≠ B := fun e => hD.2 (e ▸ hB)
  -- and from D let the two straight lines DCA, DB fall on the circle ABC; let DCA cut the
  -- circle ABC and let BD touch it;
  have hACD : Between A C D := between_symm hDCA
  have hAC : A ≠ C := ne_of_between hACD
  obtain ⟨DB, hD_DB, hB_DB⟩ := Postulate1 D B hDB.1
  have hDB_B : Collinear D B B := ⟨DB, hD_DB, hB_DB, hB_DB⟩
  have hDB_D : Collinear D B D := ⟨DB, hD_DB, hB_DB, hD_DB⟩
  -- I say that the rectangle contained by AD, DC is equal to the square on DB.
  have hresult : rect A D D C = sq D B := by
    -- Then DCA is either through the centre or not through the centre.
    by_cases hthrough : ∀ P : Point, Centre P ABC → Collinear A C P
    -- First let it be through the centre, and let F be the centre of the circle ABC;
    · obtain ⟨F, hF⟩ := exists_centre ABC
      -- let FB be joined;
      -- therefore the angle FBD is right. [III. 18]
      have hFBD : ∠ F B D = ∟ := Prop18 hF hB hDB hDB_B D hDB_D hDB'
      -- And, since AC has been bisected at F, and CD is added to it,
      obtain ⟨AC, hA_AC, hC_AC, hF_AC⟩ := hthrough F hF
      have hAFC : Between A F C :=
        between_of_inside_chord hF_AC hA_AC hC_AC (centre_inside hF) hA hC hAC
      have hAF : ‖A F‖ = ‖F C‖ := by
        rw [len_symm A F]
        exact Definition15 hF hA hC
      -- the rectangle AD, DC together with the square on FC is equal to the square on FD. [II. 6]
      have h6 : rect A D D C + sq F C = sq F D := BookII.Prop6 hAFC hAF hACD
      -- But FC is equal to FB;
      have hFC_FB : ‖F C‖ = ‖F B‖ := Definition15 hF hC hB
      -- therefore the rectangle AD, DC together with the square on FB is equal to the square on
      -- FD.
      have h6' : rect A D D C + sq F B = sq F D := by
        rw [← sq_congr hFC_FB]
        exact h6
      -- And the squares on FB, BD are equal to the square on FD; [I. 47]
      have hF_DB : ¬ Collinear D B F := fun h => hDB.not_inside h (centre_inside hF)
      have t : Triangle B F D :=
        (Triangle.of_line hB_DB hD_DB hDB'.symm (Triangle.off_line hF_DB hD_DB hB_DB)).acb
      have h47 : sq F D = sq F B + sq B D := BookI.Prop47.sq t hFBD
      -- therefore the rectangle AD, DC together with the square on FB is equal to the squares on
      -- FB, BD.
      have hsum : rect A D D C + sq F B = sq B D + sq F B := by
        rw [h6', h47]
        ac_rfl
      -- Let the square on FB be subtracted from each;
      have hrect : rect A D D C = sq B D := CommonNotion3 hsum rfl
      -- therefore the rectangle AD, DC which remains is equal to the square on the tangent DB.
      exact hrect.trans (sq_symm B D)
    -- Again, let DCA not be through the centre of the circle ABC;
    -- let the centre E be taken, and from E let EF be drawn perpendicular to AC;
    · obtain ⟨E, hE⟩ := exists_centre ABC
      have hE_AC : ¬ Collinear A C E := fun h => hthrough fun P hP => by
        obtain rfl : P = E := centre_unique hP hE
        exact h
      obtain ⟨F, hF, hEF⟩ := BookI.Prop12 hAC hE_AC
      -- let EB, EC, ED be joined.
      -- Then the angle EBD is right. [III. 18]
      have hEBD : ∠ E B D = ∟ := Prop18 hE hB hDB hDB_B D hDB_D hDB'
      -- And, since a straight line EF through the centre cuts a straight line AC not through the
      -- centre at right angles,
      /- The foot lies within AC, as III.3 asks. -/
      have hAFC : Between A F C := foot_between hE hA hC hE_AC hF hEF
      obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hAC
      have hF_AC : OnLine F AC := on_line_of_between_ends hAFC hA_AC hC_AC
      have hD_AC : OnLine D AC := on_line_of_between hACD hA_AC hC_AC
      have hE_off : ¬ OnLine E AC := Triangle.off_line hE_AC hA_AC hC_AC
      have hEF' : E ≠ F := fun e => hE_off (e ▸ hF_AC)
      have hAFE : ∠ A F E = ∟ := by
        rw [angle_symm (ne_of_between hAFC) hEF']
        exact hEF A ⟨AC, hA_AC, hC_AC, hA_AC⟩ (ne_of_between hAFC)
      -- it also bisects it; [III. 3]
      have hbisect := (Prop3 hE hA hC hAFC hE_AC).2 hAFE
      -- therefore AF is equal to FC.
      have hAF : ‖A F‖ = ‖F C‖ := hbisect
      -- Now, since the straight line AC has been bisected at the point F, and CD is added to it,
      -- the rectangle contained by AD, DC together with the square on FC is equal to the square on
      -- FD. [II. 6]
      have h6 : rect A D D C + sq F C = sq F D := BookII.Prop6 hAFC hAF hACD
      -- Let the square on FE be added to each;
      have hadd := CommonNotion2 h6 (rfl : sq F E = sq F E)
      -- therefore the rectangle AD, DC together with the squares on CF, FE is equal to the squares
      -- on FD, FE.
      have hsum : rect A D D C + (sq C F + sq F E) = sq F D + sq F E := by
        rw [sq_symm C F, ← add_assoc]
        exact hadd
      -- But the square on EC is equal to the squares on CF, FE, for the angle EFC is
      -- right; [I. 47]
      have hCF : C ≠ F := ne_of_between (between_symm hAFC)
      have tC : Triangle F E C := (Triangle.of_line hF_AC hC_AC hCF.symm hE_off).acb
      have hEC : sq E C = sq C F + sq F E := by
        rw [BookI.Prop47.sq tC (hEF C ⟨AC, hA_AC, hC_AC, hC_AC⟩ hCF),
          sq_symm C F, sq_symm E F]
        ac_rfl
      -- and the square on ED is equal to the squares on DF, FE;
      have hDF : D ≠ F :=
        ne_of_between (between_symm (between_of_between_left hACD hAFC))
      have tD : Triangle F E D := (Triangle.of_line hF_AC hD_AC hDF.symm hE_off).acb
      have hED : sq E D = sq F D + sq F E := by
        rw [BookI.Prop47.sq tD (hEF D ⟨AC, hA_AC, hC_AC, hD_AC⟩ hDF), sq_symm E F]
        ac_rfl
      -- therefore the rectangle AD, DC together with the square on EC is equal to the square on
      -- ED.
      have h1 : rect A D D C + sq E C = sq E D := by
        rw [hEC, hED]
        exact hsum
      -- And EC is equal to EB;
      have hEC_EB : ‖E C‖ = ‖E B‖ := Definition15 hE hC hB
      -- therefore the rectangle AD, DC together with the square on EB is equal to the square on
      -- ED.
      have h2 : rect A D D C + sq E B = sq E D := by
        rw [← sq_congr hEC_EB]
        exact h1
      -- But the squares on EB, BD are equal to the square on ED, for the angle EBD is
      -- right; [I. 47]
      have hE_DB : ¬ Collinear D B E := fun h => hDB.not_inside h (centre_inside hE)
      have t : Triangle B E D :=
        (Triangle.of_line hB_DB hD_DB hDB'.symm (Triangle.off_line hE_DB hD_DB hB_DB)).acb
      have h47 : sq E D = sq E B + sq B D := BookI.Prop47.sq t hEBD
      -- therefore the rectangle AD, DC together with the square on EB is equal to the squares on
      -- EB, BD.
      have hsum' : rect A D D C + sq E B = sq B D + sq E B := by
        rw [h2, h47]
        ac_rfl
      -- Let the square on EB be subtracted from each;
      have hrect : rect A D D C = sq B D := CommonNotion3 hsum' rfl
      -- therefore the rectangle AD, DC which remains is equal to the square on DB.
      exact hrect.trans (sq_symm B D)
  -- Therefore etc.
  -- Q. E. D.
  exact hresult

/-- The diameter case of III.36, stated on its own for III.37, which takes this case
first. It is proved from III.36. -/
theorem Prop36.through_centre {A B C D F : Point} {ABC : Circle}
    (hF : Centre F ABC)
    (hA : OnCircle A ABC) (hB : OnCircle B ABC)
    (hC : OnCircle C ABC)
    (hDCA : Between D C A) (hACF : Collinear A C F)
    (hDB : Touches D B ABC) :
    rect A D D C = sq D B := by
  obtain ⟨AC, hA_AC, hC_AC, hF_AC⟩ := hACF
  have hAFC : Between A F C := between_of_inside_chord hF_AC hA_AC hC_AC
    (centre_inside hF) hA hC (ne_of_between (between_symm hDCA))
  have hFCD : Between F C D := between_inner hAFC (between_symm hDCA)
  have hD : OutsideCircle D ABC := outside_of_len_gt hF hC (len_lt_of_between hFCD)
  exact Prop36 hD hA hB hC hDCA hDB

end Elements.BookIII
