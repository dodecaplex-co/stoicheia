import Elements.Figure.Basics
import Elements.BookI.Prop16
import Elements.BookI.Prop20

/-!
# Book I, Proposition 21

Euclid's text, in Heath's translation: [`heath/I/21.md`](../../heath/I/21.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

"Within the triangle" is `InsideTriangle D A B C`: D is on A's side of BC, on
B's side of CA, and on C's side of AB. Euclid's one construction, "let BD be
drawn through to E", needs the crossbar of Book Zero to make BD reach AC at all,
and a word more to make D lie between B and E (`Prop21.through`). After that
the proof is two applications of I.20 and two of I.16, each with a little adding.
-/

namespace Elements.BookI

open Tacit

/-! ## What Euclid reads off the figure -/

/-- "Let BD be drawn through to E." In Euclid's figure BD, produced beyond D,
meets the side AC at a point E between A and C.

It meets it because D lies within the angle ABC (on C's side of BA and on
A's side of BC), so the ray from B through D crosses AC (`crossbar`). And
D falls short of E, rather than beyond it: E is on AC, while B and D are
on one side of AC, so E cannot lie between them (System E, Pasch 3); and B is
not between D and E, since E is on the ray from B through D. Of three points
on a straight line one is between the other two (Between 6), so it is D. -/
theorem Prop21.through {A B C D : Point} (hD : InsideTriangle D A B C) :
    ∃ E : Point, Between B D E ∧ Between A E C := by
  obtain ⟨hDA, hDB, hDC⟩ := hD
  /- D lies within the angle ABC: the ray from B through D crosses AC. -/
  obtain ⟨E, hAEC, hE_ray⟩ := crossbar hDC.swap hDA
  obtain ⟨hBD, hEB, ⟨L, hB_L, hD_L, hE_L⟩, hEBD⟩ := hE_ray
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C (ne_of_between_ends hAEC)
  have hE_AC : OnLine E AC := on_line_of_between_ends hAEC hA_AC hC_AC
  have hDB_AC : SameSide D B AC := hDB.sameSide hC_AC hA_AC
  have hDE : D ≠ E := fun e => not_on_line_of_same_side hDB_AC (e ▸ hE_AC)
  refine ⟨E, ?_, hAEC⟩
  rcases between_cases hBD hDE hEB.symm hB_L hD_L hE_L with h | h | h
  · exact h
  · /- B is not between D and E, for E is on the ray from B through D. -/
    exact absurd (between_symm h) hEBD
  · /- Nor is E between B and D, for AC does not separate B from D. -/
    exact absurd (same_side_symm hDB_AC) (pasch3 h hE_AC)

/-- If on one of the sides of a triangle, from its extremities, there be constructed two straight
lines meeting within the triangle, the straight lines so constructed will be less than the
remaining two sides of the triangle, but will contain a greater angle. -/
theorem Prop21 {A B C D : Point} (hABC : Triangle A B C) (hD : InsideTriangle D A B C) :
    ‖B D‖ + ‖D C‖ < ‖B A‖ + ‖A C‖ ∧ ∠ B A C < ∠ B D C := by
  -- On BC, one of the sides of the triangle ABC, from its extremities B, C, let the two
  -- straight lines BD, DC be constructed meeting within the triangle;
  /- The statement hands us D within the triangle. -/
  -- I say that BD, DC are less than the remaining two sides of the triangle BA, AC, but
  -- contain an angle BDC greater than the angle BAC.
  -- For let BD be drawn through to E.
  /- BD produced crosses AC at E, beyond D: see `Prop21.through`. -/
  obtain ⟨E, hBDE, hAEC⟩ := Prop21.through hD
  /- B is off AC, since ABC is a triangle. And C is off BE: else BE would be BC,
     and D, which is on A's side of BC, would lie on it. -/
  obtain ⟨AC, hA_AC, hC_AC⟩ := Postulate1 A C hABC.ne₁₃
  have hE_AC : OnLine E AC := on_line_of_between_ends hAEC hA_AC hC_AC
  have hB_AC : ¬ OnLine B AC := hABC.acb.off_line hA_AC hC_AC
  have hA_E : A ≠ E := ne_of_between hAEC
  have hB_E : B ≠ E := ne_of_between_ends hBDE
  have hD_E : D ≠ E := (ne_of_between (between_symm hBDE)).symm
  obtain ⟨BE, hB_BE, hE_BE⟩ := Postulate1 B E hB_E
  have hD_BE : OnLine D BE := on_line_of_between_ends hBDE hB_BE hE_BE
  have hC_BE : ¬ OnLine C BE := by
    intro hC
    obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
    have hD_BC : ¬ OnLine D BC := not_on_line_of_same_side (hD.1.sameSide hB_BC hC_BC)
    exact hD_BC (line_unique hABC.ne₂₃ hB_BE hC hB_BC hC_BC ▸ hD_BE)
  /- So ABE and CED are triangles. -/
  have hAEB : Triangle A E B := Triangle.of_line hA_AC hE_AC hA_E hB_AC
  have hEDC : Triangle E D C := Triangle.of_line hE_BE hD_BE hD_E.symm hC_BE
  -- Then, since in any triangle two sides are greater than the remaining one, [I. 20]
  -- therefore, in the triangle ABE, the two sides AB, AE are greater than BE.
  have hBE_lt : ‖B E‖ < ‖B A‖ + ‖A E‖ := (Prop20 hAEB.acb).1
  -- Let EC be added to each;
  have hBEC : ‖B E‖ + ‖E C‖ < ‖B A‖ + ‖A E‖ + ‖E C‖ := add_lt_add_right ‖E C‖ hBE_lt
  -- therefore BA, AC are greater than BE, EC.
  /- AE and EC together make up AC, since E lies between A and C. -/
  have hBA_AC : ‖B E‖ + ‖E C‖ < ‖B A‖ + ‖A C‖ := by
    rw [← len_add_of_between hAEC, ← add_assoc]
    exact hBEC
  -- Again, since, in the triangle CED,
  have hCED : Triangle C E D := hEDC.cab
  -- the two sides CE, ED are greater than CD,
  have hCD_lt : ‖C D‖ < ‖C E‖ + ‖E D‖ := (Prop20 hCED).2.1
  -- let DB be added to each;
  have hCDB : ‖C D‖ + ‖D B‖ < ‖C E‖ + ‖E D‖ + ‖D B‖ := add_lt_add_right ‖D B‖ hCD_lt
  -- therefore CE, EB are greater than CD, DB.
  /- ED and DB together make up EB, since D lies between E and B. -/
  have hCE_EB : ‖C D‖ + ‖D B‖ < ‖C E‖ + ‖E B‖ := by
    rw [← len_add_of_between (between_symm hBDE), ← add_assoc]
    exact hCDB
  -- But BA, AC were proved greater than BE, EC;
  -- therefore BA, AC are much greater than BD, DC.
  /- BD, DC are CD, DB taken the other way round, and BE, EC are CE, EB. -/
  have hsides : ‖B D‖ + ‖D C‖ < ‖B A‖ + ‖A C‖ := by
    have h₁ : ‖B D‖ + ‖D C‖ = ‖C D‖ + ‖D B‖ := by
      rw [add_comm, len_symm D C, len_symm B D]
    have h₂ : ‖C E‖ + ‖E B‖ = ‖B E‖ + ‖E C‖ := by
      rw [add_comm, len_symm C E, len_symm E B]
    rw [h₁]
    exact lt_trans (h₂ ▸ hCE_EB) hBA_AC
  -- Again, since in any triangle the exterior angle is greater than the interior and opposite
  -- angle, [I. 16]
  -- therefore, in the triangle CDE,
  /- In the triangle CDE the side ED is produced to B. -/
  have hEDB : Between E D B := between_symm hBDE
  -- the exterior angle BDC is greater than the angle CED.
  /- I.16 reads both angles the other way round, as DEC and CDB. -/
  have hCED_BDC : ∠ C E D < ∠ B D C := by
    rw [angle_symm (ne_of_between (between_symm hAEC)) hD_E,
      angle_symm (ne_of_between hBDE) hEDC.ne₂₃.symm]
    exact (Prop16 hCED hEDB).1
  -- For the same reason, moreover, in the triangle ABE also,
  /- In the triangle ABE the side AE is produced to C. -/
  have hBAE : Triangle B A E := hAEB.cab
  -- the exterior angle CEB is greater than the angle BAC.
  /- I.16 gives the angle EAB less than BEC. The angle EAB, read the other way
     round, is BAE, and that is the angle BAC, since E lies on the ray from A
     through C. -/
  have hBAC_CEB : ∠ B A C < ∠ C E B := by
    rw [← angle_onRay_right (OnRay.of_between hAEC) hABC.ne₁₂.symm,
      angle_symm hABC.ne₁₂.symm hA_E.symm,
      angle_symm (ne_of_between (between_symm hAEC)) hB_E]
    exact (Prop16 hBAE hAEC).1
  -- But the angle BDC was proved greater than the angle CEB;
  /- The angle CED is the angle CEB, since D lies on the ray from E through
     B. -/
  have hCEB_BDC : ∠ C E B < ∠ B D C := by
    rw [← angle_onRay_right (OnRay.of_between hEDB) (ne_of_between (between_symm hAEC))]
    exact hCED_BDC
  -- therefore the angle BDC is much greater than the angle BAC.
  have hangle : ∠ B A C < ∠ B D C := lt_trans hBAC_CEB hCEB_BDC
  -- Therefore etc.
  exact ⟨hsides, hangle⟩
  -- Q. E. D.

end Elements.BookI
