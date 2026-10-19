import Elements.Figure.Lengths
import Elements.Figure.RuleBase

/-!
# Book Zero: order, sides and circle intersections

The remaining order and intersection rules proved here follow from the retained
foundations and the elementary rules in `Elements.Figure.RuleBase`. The length
arguments precede the general lemmas about straight lines, so those lemmas can use
these rules without a circular dependency. None of these proofs uses Circle 2 or
Circle 3.
-/

namespace Elements

open Tacit

variable {A B C D E F : Point} {L M N : Line} {α β : Circle}

namespace RuleProofs.Order

/-- An interior centre differs from every point on its circumference. -/
theorem ne_of_centre_of_on (hA : Centre A α) (hC : OnCircle C α) : C ≠ A := by
  intro h
  subst h
  exact inside_not_on (centre_inside hA) hC

end RuleProofs.Order

/-- A point nearer the centre than the circumference is inside. (Diagram-segment 4) A point
outside would lie beyond a circumference crossing, whose radius is shorter than its
distance. -/
theorem Tacit.inside_of_len_lt (hA : Centre A α) (hB : OnCircle B α) (h : ‖A C‖ < ‖A B‖) :
    InsideCircle C α := by
  by_cases hAC : A = C
  · subst C
    exact centre_inside hA
  obtain ⟨L, hAL, hCL⟩ := Postulate1 A C hAC
  apply Classical.byContradiction
  intro hn
  have hout : OutsideCircle C α := ⟨hn, fun hon =>
    Magnitude.ne_of_lt h (Definition15 hA hon hB)⟩
  obtain ⟨P, hP, _, hAPC⟩ := line_circle_between (centre_inside hA) hAL hout hCL
  have hlt := len_lt_of_between hAPC
  rw [Definition15 hA hP hB] at hlt
  exact lt_irrefl _ (lt_trans h hlt)

/-- A point inside is nearer the centre than the circumference. (Diagram-segment 4) Produce the
line from the centre through the interior point to the circumference; its distance is a part
of the radius. -/
theorem Tacit.len_lt_of_inside (hA : Centre A α) (hB : OnCircle B α) (h : InsideCircle C α) :
    ‖A C‖ < ‖A B‖ := by
  by_cases hAC : A = C
  · subst C
    rw [len_self]
    exact len_pos (RuleProofs.Order.ne_of_centre_of_on hA hB).symm
  obtain ⟨L, hAL, hCL⟩ := Postulate1 A C hAC
  obtain ⟨P, hP, _, hPCA⟩ := line_circle_beyond h hCL hAL hAC
  have hlt := len_lt_of_between (between_symm hPCA)
  rw [Definition15 hA hP hB] at hlt
  exact hlt

/-- The ends of a finite straight line differ. (Between 1) Coincident endpoints would make a sum
containing a positive length equal to zero. -/
theorem Tacit.ne_of_between_ends (h : Between A B C) : A ≠ C := by
  intro e
  subst C
  have hs := len_add_of_between h
  rw [len_self] at hs
  have hp := len_pos (Elements.Tacit.ne_of_between h)
  have hlt := CommonNotion5 (a := ‖B A‖) hp
  rw [add_comm ‖B A‖ ‖A B‖, hs] at hlt
  exact not_lt_zero _ hlt

/-- A straight line through A and B, with B between A and C, passes through C. (Between 2) Join
the endpoints and use incidence of the middle point and uniqueness of their line. -/
theorem Tacit.on_line_of_between (h : Between A B C) (hA : OnLine A L) (hB : OnLine B L) :
    OnLine C L := by
  obtain ⟨M, hAM, hCM⟩ := Postulate1 A C (ne_of_between_ends h)
  have hBM := on_line_of_between_ends h hAM hCM
  have e : M = L := line_unique (ne_of_between h) hAM hBM hA hB
  exact e ▸ hCM

/-- Take B on L, C on M and D on N, three straight lines through A, with B other than A and D
off M. If C and D are on the same side of L, and B and D are not on the same side of M, then
B and C are on the same side of N: C lies within the angle BAD. (Triple incidence 2) Extend
BA through A. The two-side rule locates the extension, and Triple incidence 1 excludes the
contrary arrangement. -/
theorem Tacit.triple_incidence2 (hAL : OnLine A L) (hAM : OnLine A M) (hAN : OnLine A N)
    (hB : OnLine B L) (hC : OnLine C M) (hD : OnLine D N) (hCD : SameSide C D L)
    (hBD : ¬ SameSide B D M) (hDM : ¬ OnLine D M) (hBA : B ≠ A) : SameSide B C N := by
  have hCL := not_on_line_of_same_side hCD
  have hDL := not_on_line_of_same_side (same_side_symm hCD)
  have hBM : ¬ OnLine B M := fun hBM =>
    hCL (line_unique hBA hBM hAM hB hAL ▸ hC)
  have hBN : ¬ OnLine B N := fun hBN =>
    hDL (line_unique hBA hBN hAN hB hAL ▸ hD)
  have hCA : C ≠ A := fun e => hCL (e ▸ hAL)
  have hCN : ¬ OnLine C N := fun hCN =>
    hDM (line_unique hCA hCN hAN hC hAM ▸ hD)
  apply Classical.byContradiction
  intro hBC
  obtain ⟨P, hPL, hBAP, _⟩ := Postulate2 hB hAL hBA []
  have hPM : ¬ OnLine P M := fun hPM =>
    hBM (on_line_of_between (between_symm hBAP) hPM hAM)
  have hPN : ¬ OnLine P N := fun hPN =>
    hBN (on_line_of_between (between_symm hBAP) hPN hAN)
  have hDP : SameSide D P M :=
    (same_side_or hBM hDM hPM hBD).resolve_left (pasch3 hBAP hAM)
  have hCP : SameSide C P N :=
    (same_side_or hBN hCN hPN hBC).resolve_left (pasch3 hBAP hAN)
  exact triple_incidence1 hAL hAM hAN hPL hC hD hCD
    (same_side_symm hCP) (same_side_symm hDP)

namespace RuleProofs.Order

/-- Distinct endpoints have positive length. -/
theorem positive_length {A B : Point} (h : A ≠ B) : 0 < ‖A B‖ := by
  rcases lt_trichotomy 0 ‖A B‖ with hp | hz | hn
  · exact hp
  · exact False.elim (h (eq_of_len_eq_zero hz.symm))
  · exact False.elim (not_lt_zero _ hn)


/-- The first part of a segment is less than the whole. -/
theorem len_lt_left {A B C : Point} (h : Between A B C) : ‖A B‖ < ‖A C‖ := by
  rw [← len_add_of_between h]
  exact CommonNotion5 (positive_length (ne_of_between (between_symm h)).symm)


/-- The last part of a segment is less than the whole. -/
theorem len_lt_right {A B C : Point} (h : Between A B C) : ‖B C‖ < ‖A C‖ := by
  rw [← len_add_of_between h, add_comm]
  exact CommonNotion5 (positive_length (ne_of_between h))


/-- Reversing this order would give two contradictory strict length inequalities. -/
theorem not_between_lengths {A B C : Point} (h : Between A B C) :
    ¬ Between B A C := by
  intro h'
  exact lt_irrefl _ (lt_trans (len_lt_right h) (len_lt_right h'))


/-- The three collinear orders exclude a length greater than the sum of the other two. -/
theorem collinear_triangle {A B C : Point} {L : Line}
    (hA : OnLine A L) (hB : OnLine B L) (hC : OnLine C L)
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) :
    ¬ ‖A B‖ + ‖B C‖ < ‖A C‖ := by
  intro hlt
  rcases between_cases hAB hBC hAC hA hB hC with h | h | h
  · rw [len_add_of_between h] at hlt
    exact lt_irrefl _ hlt
  · have hsum : ‖B C‖ < ‖A B‖ + ‖B C‖ := by
      rw [add_comm]
      exact CommonNotion5 (positive_length hAB)
    exact lt_irrefl _ (lt_trans hlt (lt_trans (len_lt_right h) hsum))
  · have hsum : ‖A B‖ < ‖A B‖ + ‖B C‖ := CommonNotion5 (positive_length hBC)
    exact lt_irrefl _ (lt_trans hlt (lt_trans (len_lt_left h) hsum))

end RuleProofs.Order

open RuleProofs.Order

/-- If B is between A and C, and D is between A and B, then D is between A and C. (Between 4)
Length addition and strict comparison exclude the other two orders of A, D and C. -/
theorem Tacit.between_of_between_left (h₁ : Between A B C) (h₂ : Between A D B) : Between A D C := by
  obtain ⟨L, hAL, hCL⟩ := Postulate1 A C (ne_of_between_ends h₁)
  have hBL := on_line_of_between_ends h₁ hAL hCL
  have hDL := on_line_of_between_ends h₂ hAL hBL
  have hDC : D ≠ C := by
    intro e
    subst D
    exact not_between_lengths (between_symm h₁) (between_symm h₂)
  rcases between_cases (ne_of_between h₂) hDC (ne_of_between_ends h₁)
      hAL hDL hCL with h | h | h
  · exact h
  · have hsum : ‖D B‖ + ‖B C‖ < ‖A C‖ := by
      rw [← len_add_of_between h₁, ← len_add_of_between h₂, add_assoc,
        add_comm ‖A D‖]
      exact CommonNotion5 (positive_length (ne_of_between h₂))
    exact False.elim (collinear_triangle hDL hBL hCL
      (ne_of_between (between_symm h₂)).symm
      (ne_of_between (between_symm h₁)).symm hDC
      (lt_trans hsum (len_lt_right h)))
  · exact False.elim (lt_irrefl _
      (lt_trans (len_lt_left h₂) (lt_trans (len_lt_left h₁) (len_lt_left h))))

namespace RuleProofs.Order

/-- Adding two strict comparisons contradicts the two decompositions of the same length. -/
theorem spoke_order_impossible {A B C D : Point}
    (hABC : Between A B C) (hABD : Between A B D)
    (hCBD : Between C B D) (hACD : Between A C D) : False := by
  have h₁ := add_lt_add_right ‖B D‖ (len_lt_left hABC)
  have h₂ := add_lt_add_right ‖A C‖ (len_lt_right hCBD)
  rw [add_comm ‖B D‖ ‖A C‖, add_comm ‖C D‖ ‖A C‖] at h₂
  have h₃ := lt_trans h₁ h₂
  rw [len_add_of_between hABD, len_add_of_between hACD] at h₃
  exact lt_irrefl _ h₃


/-- The three collinear orders contradict three proposed crossings at one point. -/
theorem not_between_three_lengths {A B C D : Point}
    (hABC : Between A B C) (hABD : Between A B D) : ¬ Between C B D := by
  intro hCBD
  obtain ⟨L, hA, hB⟩ := Postulate1 A B (ne_of_between hABC)
  have hC := on_line_of_between hABC hA hB
  have hD := on_line_of_between hABD hA hB
  rcases between_cases (ne_of_between_ends hABC) (ne_of_between_ends hCBD)
      (ne_of_between_ends hABD) hA hC hD with hACD | hCAD | hADC
  · exact spoke_order_impossible hABC hABD hCBD hACD
  · exact spoke_order_impossible (between_symm hABC) hCBD hABD hCAD
  · exact spoke_order_impossible hABD hABC (between_symm hCBD) hADC


/-- Two nested segments place the shared endpoint between the inner and outer endpoints. -/
theorem between_inner_lengths {A B C D : Point}
    (h₁ : Between A B C) (h₂ : Between A C D) : Between B C D := by
  obtain ⟨L, hA, hC⟩ := Postulate1 A C (ne_of_between_ends h₁)
  have hB := on_line_of_between_ends h₁ hA hC
  have hD := on_line_of_between h₂ hA hC
  have hBC : B ≠ C := (ne_of_between (between_symm h₁)).symm
  have hCD : C ≠ D := (ne_of_between (between_symm h₂)).symm
  have hBD : B ≠ D := by
    rintro rfl
    exact not_between_lengths (between_symm h₂) (between_symm h₁)
  rcases between_cases hBC hCD hBD hB hC hD with h | h | h
  · exact h
  · exact absurd (Elements.Tacit.between_of_between_left (between_symm h₂) (between_symm h))
      (not_between_three_lengths h (between_symm h₁))
  · exact absurd (Elements.Tacit.between_of_between_left (between_symm h₁) (between_symm h))
      (not_between_lengths (between_symm h₂))

end RuleProofs.Order

/-- If B is between A and C, and C is between B and D, then B is between A and D. (Between 5)
Collinear orders, length comparison and one extension exclude both contrary arrangements. -/
theorem Tacit.between_of_between_right (h₁ : Between A B C) (h₂ : Between B C D) : Between A B D := by
  obtain ⟨L, hAL, hCL⟩ := Postulate1 A C (ne_of_between_ends h₁)
  have hBL := on_line_of_between_ends h₁ hAL hCL
  have hDL := on_line_of_between h₂ hBL hCL
  have hAD : A ≠ D := by
    rintro rfl
    exact not_between_lengths (between_symm h₁) h₂
  rcases between_cases (ne_of_between h₁) (ne_of_between_ends h₂) hAD
      hAL hBL hDL with hABD | hBAD | hADB
  · exact hABD
  · have hADC : Between A D C := by
      rcases between_cases (ne_of_between_ends h₁)
          (ne_of_between (between_symm h₂)).symm hAD hAL hCL hDL
          with hACD | hCAD | hADC
      · exact False.elim (not_between_lengths hBAD
          (Elements.Tacit.between_of_between_left hACD h₁))
      · exact False.elim (not_between_lengths h₂
          (Elements.Tacit.between_of_between_left hCAD (between_symm h₁)))
      · exact hADC
    obtain ⟨E, -, hBDE, -⟩ := Postulate2 hBL hDL (ne_of_between_ends h₂) []
    have hADE := between_inner_lengths hBAD hBDE
    have hCDE := between_inner_lengths h₂ hBDE
    exact False.elim (not_between_three_lengths (between_symm hADC) hCDE hADE)
  · exact False.elim (not_between_lengths (between_symm h₁)
      (Elements.Tacit.between_of_between_left (between_symm hADB) h₂))

namespace RuleProofs.Intersections

/-- A point between an interior point and a circumference point is interior, by Circle 1 and a
crossing from inside. -/
theorem inside_between_inside_on {A B C : Point} {L : Line} {α : Circle}
    (hAL : OnLine A L) (hBL : OnLine B L) (hCL : OnLine C L)
    (hA : InsideCircle A α) (hB : OnCircle B α) (hACB : Between A C B) :
    InsideCircle C α := by
  apply Classical.byContradiction
  intro hn
  have hCnoton : ¬ OnCircle C α := by
    intro hC
    exact not_between_of_between hACB
      (between_of_inside_chord hAL hCL hBL hA hC hB
        (ne_of_between (between_symm hACB)).symm)
  obtain ⟨X, hX, hXL, hAXC⟩ := line_circle_between hA hAL ⟨hn, hCnoton⟩ hCL
  have hAXB := between_of_between_left hACB hAXC
  exact not_between_of_between hAXB
    (between_of_inside_chord hAL hXL hBL hA hX hB
      (ne_of_between (between_symm hAXB)).symm)

end RuleProofs.Intersections

/-- Two circles cut one another if the first passes through a point A inside the second, and a
point B outside the second is inside or on the first. (Intersection 4, in LeanEuclid's
corrected form) A crossing of the second circle lies inside the first, giving the two
witnesses for Intersection 5. -/
theorem Tacit.circles_meet_of_on_inside_outside (hAα : OnCircle A α)
    (hBα : InsideCircle B α ∨ OnCircle B α) (hAβ : InsideCircle A β) (hBβ : OutsideCircle B β) :
    CirclesMeet α β := by
  have meet_of_inside_outside : ∀ O : Point, InsideCircle O α → OutsideCircle O β →
      CirclesMeet α β := by
    intro O hOα hOβ
    have hAO : A ≠ O := fun e => hOβ.1 (e ▸ hAβ)
    obtain ⟨L, hAL, hOL⟩ := Postulate1 A O hAO
    obtain ⟨C, hCβ, hCL, hACO⟩ := line_circle_between hAβ hAL hOβ hOL
    have hCα := RuleProofs.Intersections.inside_between_inside_on hOL hAL hCL hOα hAα (between_symm hACO)
    exact circles_meet hAα hCα hAβ hCβ
  rcases hBα with hBα | hBα
  · exact meet_of_inside_outside B hBα hBβ
  · obtain ⟨O, hOα, _⟩ := exists_point_inside_circle α []
    by_cases hOβ : InsideCircle O β
    · have hOB : O ≠ B := fun e => hBβ.1 (e ▸ hOβ)
      obtain ⟨L, hOL, hBL⟩ := Postulate1 O B hOB
      obtain ⟨C, hCβ, hCL, hOCB⟩ := line_circle_between hOβ hOL hBβ hBL
      have hCα := RuleProofs.Intersections.inside_between_inside_on hOL hBL hCL hOα hBα hOCB
      exact circles_meet hAα hCα hAβ hCβ
    · by_cases hOon : OnCircle O β
      · exact circles_meet hAα hOα hAβ hOon
      · exact meet_of_inside_outside O hOα ⟨hOβ, hOon⟩

/-- Let a point be taken on the other side of L from B. (Points 6) Produce the line from B
through a point of L; Pasch 3 separates its endpoints. -/
theorem Tacit.exists_point_opposite_side {B : Point} {L : Line} (hB : ¬ OnLine B L)
    (avoid : List Point) : ∃ A : Point, OppositeSides A B L ∧ A ∉ avoid := by
  obtain ⟨O, hO, _⟩ := exists_point_on_line L []
  have hBO : B ≠ O := fun e => hB (e ▸ hO)
  obtain ⟨M, hBM, hOM⟩ := Postulate1 B O hBO
  obtain ⟨A, _, hBOA, hA⟩ := Postulate2 hBM hOM hBO avoid
  refine ⟨A, ⟨?_, hB, pasch3 (between_symm hBOA) hO⟩, hA⟩
  exact fun hAL => hB (on_line_of_between (between_symm hBOA) hAL hO)

/-- The same, on the side away from B. (Intersections 9) Choose a point opposite B and take the
common circle point on that point's side. -/
theorem Tacit.circles_meet_opposite_side {α β : Circle} {B C D : Point} {L : Line}
    (h : CirclesMeet α β) (hC : Centre C α) (hD : Centre D β) (hCL : OnLine C L)
    (hDL : OnLine D L) (hB : ¬ OnLine B L) :
    ∃ A : Point, OnCircle A α ∧ OnCircle A β ∧ OppositeSides A B L := by
  obtain ⟨P, hP, _⟩ := exists_point_opposite_side hB []
  obtain ⟨A, hAα, hAβ, hA⟩ :=
    Elements.Tacit.circles_meet_same_side h hC hD hCL hDL hP.1
  exact ⟨A, hAα, hAβ, not_on_line_of_same_side hA, hB,
    fun hAB => hP.2.2 (same_side_trans hA hAB)⟩

namespace RuleProofs.Construction

/-- If two radii differed, the nearer circumference point would be inside the circle. -/
theorem definition15 : type_of% @Elements.Definition15 := by
  intro A B C α hA hB hC
  rcases lt_trichotomy ‖A B‖ ‖A C‖ with h | h | h
  · exact False.elim (inside_not_on (inside_of_len_lt hA hC h) hB)
  · exact h
  · exact False.elim (inside_not_on (inside_of_len_lt hA hB h) hC)

end RuleProofs.Construction

/-- Let a point be taken between B and C. (Points 3) A smaller concentric circle supplies one
interior division; repeat within a smaller segment to avoid each forbidden point. -/
theorem Tacit.exists_point_between {B C : Point} {L : Line} (hB : OnLine B L) (hC : OnLine C L)
    (hBC : B ≠ C) (avoid : List Point) : ∃ A : Point, OnLine A L ∧ Between B A C ∧ A ∉ avoid := by
  induction avoid generalizing B C with
  | nil =>
      obtain ⟨α, hBα, hCα⟩ := Postulate3 B C hBC
      obtain ⟨D, hDα, hD⟩ := exists_point_inside_circle α [B]
      have hBD : B ≠ D := by
        intro h
        exact hD (by simp [h])
      have hlt := len_lt_of_inside hBα hCα hDα
      obtain ⟨β, hBβ, hDβ⟩ := Postulate3 B D hBD
      have hCβ : OutsideCircle C β := by
        constructor
        · intro h
          exact lt_irrefl _ (lt_trans hlt (len_lt_of_inside hBβ hDβ h))
        · intro h
          exact lt_irrefl _ ((RuleProofs.Construction.definition15 hBβ hDβ h) ▸ hlt)
      obtain ⟨A, _, hAL, hBAC⟩ := line_circle_between (centre_inside hBβ) hB hCβ hC
      exact ⟨A, hAL, hBAC, by simp⟩
  | cons P avoid ih =>
      obtain ⟨X, hXL, hBXC, hX⟩ := ih hB hC hBC
      by_cases hXP : X = P
      · obtain ⟨Y, hYL, hBYX, hY⟩ := ih hB hXL (ne_of_between hBXC)
        have hYP : Y ≠ P := hXP ▸ (ne_of_between (between_symm hBYX)).symm
        exact ⟨Y, hYL, between_of_between_left hBXC hBYX, by simp [hYP, hY]⟩
      · exact ⟨X, hXL, hBXC, by simp [hXP, hX]⟩

/-- A straight line through a point inside a circle cuts the circle. (Intersection 3) Produce
the line in both directions from the interior point to obtain distinct circumference points. -/
theorem Tacit.line_meets_circle_of_inside (hA : InsideCircle A α) (hAL : OnLine A L) :
    LineMeetsCircle L α := by
  obtain ⟨C, hCL, hCA⟩ := exists_point_on_line L [A]
  have hCA' : C ≠ A := by simpa using hCA
  obtain ⟨P, hP, hPL, hPAC⟩ := line_circle_beyond hA hAL hCL hCA'
  obtain ⟨Q, hQ, hQL, hQAP⟩ :=
    line_circle_beyond hA hAL hPL (ne_of_between hPAC)
  exact ⟨Q, P, ne_of_between_ends hQAP, hQL, hQ, hPL, hP⟩

namespace RuleProofs.Separation

/-- A circle about the middle point locates a shorter distance on either ray. -/
theorem between_cases_of_len_lt {A B C : Point} {L : Line}
    (hBA : B ≠ A) (hA : OnLine A L) (hB : OnLine B L) (hC : OnLine C L)
    (hlt : ‖B A‖ < ‖B C‖) : Between A B C ∨ Between B A C := by
  obtain ⟨α, hcenter, hAon⟩ := Postulate3 B A hBA
  have hCout : OutsideCircle C α := by
    constructor
    · intro hCin
      exact lt_irrefl _ (lt_trans hlt (len_lt_of_inside hcenter hAon hCin))
    · intro hCon
      exact Magnitude.ne_of_lt hlt (Definition15 hcenter hAon hCon)
  obtain ⟨X, hXon, hXL, hBXC⟩ := line_circle_between (centre_inside hcenter) hB hCout hC
  by_cases hAX : A = X
  · exact Or.inr (hAX ▸ hBXC)
  · have hABX := between_of_inside_chord hB hA hXL (centre_inside hcenter) hAon hXon hAX
    exact Or.inl (between_of_between_right hABX hBXC)


/-- Trichotomy of distances and Circle 1 give the three collinear orders. -/
theorem between_cases : type_of% @Elements.Tacit.between_cases := by
  intro A B C L hAB hBC hAC hA hB hC
  rcases lt_trichotomy ‖B A‖ ‖B C‖ with hlt | heq | hgt
  · exact (between_cases_of_len_lt hAB.symm hA hB hC hlt).elim Or.inl (Or.inr ∘ Or.inl)
  · obtain ⟨α, hcenter, hAon⟩ := Postulate3 B A hAB.symm
    have hCon := on_circle_of_len_eq hcenter hAon heq.symm
    exact Or.inl (between_of_inside_chord hB hA hC (centre_inside hcenter) hAon hCon hAC)
  · rcases between_cases_of_len_lt hBC hC hB hA hgt with hCBA | hBCA
    · exact Or.inl (between_symm hCBA)
    · exact Or.inr (Or.inr (between_symm hBCA))


/-- Two strict length comparisons contradict equal decompositions of the whole. -/
theorem spoke_order_impossible {A B C D : Point}
    (hABC : Between A B C) (hABD : Between A B D)
    (hCBD : Between C B D) (hACD : Between A C D) : False := by
  have h₁ : ‖A B‖ < ‖A C‖ := len_lt_of_between hABC
  have h₂ : ‖B D‖ < ‖C D‖ := by
    rw [len_symm B D, len_symm C D]
    exact len_lt_of_between (between_symm hCBD)
  have h₃ := add_lt_add_right ‖B D‖ h₁
  have h₄ := add_lt_add_right ‖A C‖ h₂
  rw [add_comm ‖B D‖ ‖A C‖, add_comm ‖C D‖ ‖A C‖] at h₄
  have h₅ := lt_trans h₃ h₄
  rw [len_add_of_between hABD, len_add_of_between hACD] at h₅
  exact lt_irrefl _ h₅

end RuleProofs.Separation

/-- If B is between A and C, and also between A and D, then B is not between C and D: C and D
lie on the same side of B. (Between 7) The three orders obtained from circle crossings each
contradict length addition. -/
theorem Tacit.not_between_of_between_between (h₁ : Between A B C) (h₂ : Between A B D) :
    ¬ Between C B D := by
  intro hCBD
  obtain ⟨L, hA, hB⟩ := Postulate1 A B (ne_of_between h₁)
  have hC := on_line_of_between h₁ hA hB
  have hD := on_line_of_between h₂ hA hB
  rcases RuleProofs.Separation.between_cases (ne_of_between_ends h₁) (ne_of_between_ends hCBD)
    (ne_of_between_ends h₂) hA hC hD with hACD | hCAD | hADC
  · exact RuleProofs.Separation.spoke_order_impossible h₁ h₂ hCBD hACD
  · exact RuleProofs.Separation.spoke_order_impossible (between_symm h₁) hCBD h₂ hCAD
  · exact RuleProofs.Separation.spoke_order_impossible h₂ h₁ (between_symm hCBD) hADC

namespace RuleProofs.Pasch

/-- Triple incidence 1 excludes a same-side relation whose second point is on the line. -/
theorem same_side_right_off {A B : Point} {L : Line} (hAB : SameSide A B L) :
    ¬ OnLine B L := by
  intro hB
  have hBB := same_side_trans hAB hAB
  exact triple_incidence1 hB hB hB hB hB hB hBB hBB hBB


/-- A small segment through a point on the line contradicts Triple incidence 2 if its side
relation is asserted. -/
theorem not_on_line_of_same_side : type_of% @Elements.Tacit.not_on_line_of_same_side := by
  intro A B L hAB hAL
  have hB := same_side_right_off hAB
  obtain ⟨C, hCL, havoid⟩ := exists_point_on_line L [A]
  have hCA : C ≠ A := fun e => havoid (e ▸ List.mem_singleton_self A)
  have hCB : C ≠ B := fun e => hB (e ▸ hCL)
  have hABne : A ≠ B := fun e => hB (e ▸ hAL)
  obtain ⟨N, hCN, hBN⟩ := Postulate1 C B hCB
  obtain ⟨X, _, hCXB, _⟩ := exists_point_between hCN hBN hCB []
  have hX : ¬ OnLine X L := fun hXL => hB (on_line_of_between hCXB hCL hXL)
  obtain ⟨K, hAK, hXK⟩ := Postulate1 A X (fun e => hX (e ▸ hAL))
  obtain ⟨M, hAM, hBM⟩ := Postulate1 A B hABne
  have hBK : ¬ OnLine B K := by
    intro hBK
    have hCK := on_line_of_between (between_symm hCXB) hBK hXK
    exact hB (line_unique hCA hCK hAK hCL hAL ▸ hBK)
  have hCA_M := triple_incidence2 hAL hAK hAM hCL hAK hBM hAB
    (Elements.Tacit.pasch3 hCXB hXK) hBK hCA
  exact same_side_right_off hCA_M hAM


/-- The intersection rule and Pasch 4 locate the crossing between opposite endpoints. -/
theorem opposite_sides_exists_between
    (hrefl : type_of% @Elements.Tacit.same_side_refl) {P Q : Point} {L : Line}
    (h : OppositeSides P Q L) : ∃ X : Point, OnLine X L ∧ Between P X Q := by
  have hPQ : P ≠ Q := fun e => h.2.2 (e ▸ hrefl h.1)
  obtain ⟨M, hP, hQ⟩ := Postulate1 P Q hPQ
  obtain ⟨hLM, X, hXL, hXM⟩ := lines_meet_of_opposite_sides h hP hQ
  exact ⟨X, hXL, pasch4 hLM hXL hXM hP hQ hPQ (fun e => h.1 (e ▸ hXL))
    (fun e => h.2.1 (e ▸ hXL)) h.2.2⟩

end RuleProofs.Pasch

/-- If A and C are on the same side of L, so is any point between them: if B is between A and C,
then A and B are on the same side of L. (Pasch 1) Opposite sides would give a crossing
before B, contradicting Pasch 3 on the full segment. -/
theorem Tacit.pasch1 (h : Between A B C) (hAC : SameSide A C L) : SameSide A B L := by
  have hA := RuleProofs.Pasch.not_on_line_of_same_side hAC
  have hB : ¬ OnLine B L := fun hB => Elements.Tacit.pasch3 h hB hAC
  apply Classical.byContradiction
  intro hAB
  obtain ⟨X, hX, hAXB⟩ := RuleProofs.Pasch.opposite_sides_exists_between @same_side_refl ⟨hA, hB, hAB⟩
  exact Elements.Tacit.pasch3 (between_of_between_left h hAXB) hX hAC

namespace RuleProofs.Construction

/-- A circle about the last endpoint extends a segment; iteration avoids a finite list. -/
theorem postulate2 : type_of% @Elements.Postulate2 := by
  intro B C L hB hC hBC avoid
  induction avoid generalizing B C with
  | nil =>
      obtain ⟨α, hα, hBα⟩ := Postulate3 C B hBC.symm
      obtain ⟨A, _, hAL, hACB⟩ := line_circle_beyond (centre_inside hα) hC hB hBC
      exact ⟨A, hAL, between_symm hACB, by simp⟩
  | cons P avoid ih =>
      obtain ⟨X, hXL, hBCX, hX⟩ := ih hB hC hBC
      by_cases hXP : X = P
      · obtain ⟨Y, hYL, hCXY, hY⟩ :=
          ih hC hXL (ne_of_between (between_symm hBCX)).symm
        have hYP : Y ≠ P := hXP ▸ ne_of_between (between_symm hCXY)
        exact ⟨Y, hYL, between_of_between_right hBCX hCXY, by simp [hYP, hY]⟩
      · exact ⟨X, hXL, hBCX, by simp [hXP, hX]⟩


/-- An opposite-side crossing gives a point of the line; a circle through it and extensions
avoid a finite list. -/
theorem exists_point_on_line : type_of% @Elements.Tacit.exists_point_on_line := by
  intro L avoid
  obtain ⟨A, _⟩ := Elements.Tacit.exists_point []
  have hP : ∃ P : Point, OnLine P L := by
    by_cases hAL : OnLine A L
    · exact ⟨A, hAL⟩
    · obtain ⟨B, hB, _⟩ := exists_point_opposite_side hAL []
      have hAB : A ≠ B := by
        intro h
        subst B
        exact hB.2.2 (same_side_refl hAL)
      obtain ⟨M, hAM, hBM⟩ := Postulate1 A B hAB
      obtain ⟨P, hPL, _⟩ := (lines_meet_of_opposite_sides hB hBM hAM).2
      exact ⟨P, hPL⟩
  obtain ⟨P, hPL⟩ := hP
  obtain ⟨Q, hQ⟩ := Elements.Tacit.exists_point [P]
  have hPQ : P ≠ Q := by
    intro h
    exact hQ (by simp [h])
  obtain ⟨α, hPα, _⟩ := Postulate3 P Q hPQ
  obtain ⟨B, C, hBC, hBL, _, hCL, _⟩ :=
    line_meets_circle_of_inside (centre_inside hPα) hPL
  obtain ⟨R, hRL, _, hR⟩ := postulate2 hBL hCL hBC avoid
  exact ⟨R, hRL, hR⟩

end RuleProofs.Construction

/-- Let a point be taken on L, not on the different straight line M. (Points 2, with "distinct
from M") Choose a point of L; if it is on M, a second point of L differs from it and cannot
also be on M. -/
theorem Tacit.exists_point_on_line_off_line {L M : Line} (h : L ≠ M) (avoid : List Point) :
    ∃ A : Point, OnLine A L ∧ ¬ OnLine A M ∧ A ∉ avoid := by
  obtain ⟨A, hAL, hA⟩ := RuleProofs.Construction.exists_point_on_line L avoid
  by_cases hAM : OnLine A M
  · obtain ⟨B, hBL, hB⟩ := RuleProofs.Construction.exists_point_on_line L (A :: avoid)
    have hBA : B ≠ A := fun e => hB (by simp [e])
    have hBM : ¬ OnLine B M := fun hBM => h (line_unique hBA hBL hAL hBM hAM)
    exact ⟨B, hBL, hBM, fun hmem => hB (List.mem_cons_of_mem A hmem)⟩
  · exact ⟨A, hAL, hAM, hA⟩

end Elements
