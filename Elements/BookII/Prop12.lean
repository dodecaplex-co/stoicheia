import Elements.Figure.Basics
import Elements.BookII.Rectangles
import Elements.BookI.Prop17
import Elements.BookI.Prop47
import Elements.BookII.Prop04

/-!
# Book II, Proposition 12

Euclid's text, in Heath's translation: [`heath/II/12.md`](../../heath/II/12.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.
-/

namespace Elements.BookII

open Tacit

/-- In obtuse-angled triangles the square on the side subtending the obtuse angle is greater than
the squares on the sides containing the obtuse angle by twice the rectangle contained by one of
the sides about the obtuse angle, namely that on which the perpendicular falls, and the straight
line cut off outside by the perpendicular towards the obtuse angle. -/
theorem Prop12 {A B C D : Point} (hABC : Triangle A B C) (hBAC : IsObtuse B A C)
    (hD : Collinear C A D) (hBD : ∀ P : Point, Collinear C A P → P ≠ D → ∠ B D P = ∟) :
    sq B C = sq B A + sq A C + (rect C A A D + rect C A A D) := by
  -- Let ABC be an obtuse-angled triangle having the angle BAC obtuse, and let BD be drawn from
  -- the point B perpendicular to CA produced;
  obtain ⟨CA, hC_CA, hA_CA⟩ := Postulate1 C A hABC.ne₁₃.symm
  have hD_CA : OnLine D CA := by
    obtain ⟨M, hC_M, hA_M, hD_M⟩ := hD
    exact (line_unique hABC.ne₁₃.symm hC_M hA_M hC_CA hA_CA) ▸ hD_M
  have hB_CA : ¬ OnLine B CA := fun h => hABC ⟨CA, hA_CA, h, hC_CA⟩
  have colCA : ∀ {P : Point}, OnLine P CA → Collinear C A P :=
    fun h => ⟨CA, hC_CA, hA_CA, h⟩
  /- Euclid reads "produced" off his figure; we prove it from the obtuse angle,
     which keeps D off A and off the ray from A through C [I. 17]. -/
  have hDA : D ≠ A := by
    intro e
    have h : ∟ < ∠ B A C := hBAC
    rw [← e, hBD C (colCA hC_CA) (e ▸ hABC.ne₁₃.symm)] at h
    exact lt_irrefl _ h
  have hDB : D ≠ B := fun e => hB_CA (e ▸ hD_CA)
  have hD_not_ray : ¬ OnRay D A C := by
    intro hray
    have hABD : Triangle A B D := Triangle.of_line hA_CA hD_CA hDA.symm hB_CA |>.acb
    have h17 := (BookI.Prop17 hABD).2.1
    rw [angle_onRay_right hray hABC.ne₁₂.symm, angle_symm hDA.symm hDB.symm,
      hBD A (colCA hA_CA) hDA.symm] at h17
    exact lt_irrefl _ (lt_trans (add_lt_add_right ∟ hBAC) h17)
  have hCAD : Between C A D := by
    by_cases hDC : D = C
    · rw [hDC] at hD_not_ray
      exact absurd (OnRay.self hABC.ne₁₃) hD_not_ray
    rcases between_cases hABC.ne₁₃.symm hDA.symm (Ne.symm hDC) hC_CA hA_CA hD_CA with
      h | h | h
    · exact h
    · exact absurd (OnRay.of_beyond h) hD_not_ray
    · exact absurd (OnRay.of_between (between_symm h)) hD_not_ray
  -- I say that the square on BC is greater than the squares on BA, AC by twice the rectangle
  -- contained by CA, AD.
  -- For, since the straight line CD has been cut at random at the point A,
  have hDC : D ≠ C := (ne_of_between_ends hCAD).symm
  -- the square on DC is equal to the squares on CA, AD and twice the rectangle contained by
  -- CA, AD. [II. 4]
  have h4 : sq D C = sq C A + sq A D + (rect C A A D + rect C A A D) := by
    rw [sq_symm D C]
    exact Prop4 hCAD
  -- Let the square on DB be added to each;
  have hadded := CommonNotion2 h4 (rfl : sq D B = sq D B)
  -- therefore the squares on CD, DB are equal to the squares on CA, AD, DB and twice the
  -- rectangle CA, AD.
  have hadd : sq C D + sq D B =
      sq C A + (sq A D + sq D B) + (rect C A A D + rect C A A D) := by
    rw [sq_symm C D, hadded]
    ac_rfl
  -- But the square on CB is equal to the squares on CD, DB, for the angle at D is
  -- right; [I. 47]
  have hCDB : ∠ C D B = ∟ := by
    rw [angle_symm hDC.symm hDB.symm]
    exact hBD C (colCA hC_CA) hDC.symm
  have h47a : sq C B = sq C D + sq D B :=
    BookI.Prop47.sq (Triangle.of_line hD_CA hC_CA hDC hB_CA) hCDB
  -- and the square on AB is equal to the squares on AD, DB; [I. 47]
  have hADB : ∠ A D B = ∟ := by
    rw [angle_symm hDA.symm hDB.symm]
    exact hBD A (colCA hA_CA) hDA.symm
  have h47b : sq A B = sq A D + sq D B :=
    BookI.Prop47.sq (Triangle.of_line hD_CA hA_CA hDA hB_CA) hADB
  -- therefore the square on CB is equal to the squares on CA, AB and twice the rectangle
  -- contained by CA, AD;
  have h : sq C B = sq C A + sq A B + (rect C A A D + rect C A A D) := by
    rw [h47a, hadd, ← h47b]
  -- so that the square on CB is greater than the squares on CA, AB by twice the rectangle
  -- contained by CA, AD.
  rw [sq_symm B C, h, sq_symm C A, sq_symm A B]
  ac_rfl
  -- Therefore etc.
  -- Q. E. D.

end Elements.BookII
