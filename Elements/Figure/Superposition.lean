import Elements.Foundations.Tacit.Superposition
import Elements.Foundations.Superposition.Restriction
import Elements.Figure.Angles

/-!
# Superposition: the geometric laws a derivation cites

The restricted rule asks for proofs of the laws used inside a hypothetical placement.
Here the seven laws needed by I.4 follow from the foundations and Book Zero, with no
construction rule. The angle-to-ray law takes its three straight lines as given; in
I.4 the third is the side AC laid down by the placement.

I.7's law is supplied where I.8 cites it. Its proof belongs after I.7, since Book Zero
uses no proposition. The pure restriction theorems are imported here so that the
library also checks what can leave a hypothetical placement.
-/

namespace Elements.Superposition

open Tacit

/-- **One ray for one angle**, with its three straight lines named: D and E on L, D and F on
M, D and P on N. If P is on F's side of L and the angle EDP is the angle EDF, then P is on M.
`onRay_of_angle_eq` draws its straight lines; here they are given, so the proof
draws nothing. Otherwise either P would lie within the angle EDF, or F within the angle
EDP (Triple incidence 2 says which), and either way an angle would be a part of an angle
equal to it (Diagram-angle 1 and 2, with C.N. 5). -/
theorem onLine_of_angle_eq_named {D E F P : Point} {L M N : Line} (hDE : D ≠ E)
    (hD : OnLine D L) (hE : OnLine E L) (hDM : OnLine D M) (hFM : OnLine F M)
    (hDN : OnLine D N) (hPN : OnLine P N) (hPF : SameSide P F L) (h : ∠ E D P = ∠ E D F) :
    OnLine P M := by
  have hP_L : ¬ OnLine P L := not_on_line_of_same_side hPF
  have hF_L : ¬ OnLine F L := not_on_line_of_same_side (same_side_symm hPF)
  have hDF : D ≠ F := fun e => hF_L (e ▸ hD)
  have hPD : P ≠ D := fun e => hP_L (e ▸ hD)
  have hLM : L ≠ M := fun e => hF_L (e ▸ hFM)
  refine Classical.byContradiction fun hP_M => ?_
  /- Off M, the point P makes some angle with DF (Diagram-angle 1). -/
  have hFDP : 0 < ∠ F D P := Magnitude.pos_of_ne_zero fun h0 =>
    hP_M (same_ray_of_angle_eq_zero hDF hPD.symm hDM hFM h0).1
  by_cases hs : SameSide E P M
  · /- P lies within the angle EDF: the part would be equal to the whole. -/
    have hadd : ∠ E D F = ∠ E D P + ∠ P D F :=
      angle_add_of_inside hD hDM hE hFM hDE hDF hP_L hP_M hLM hs (same_side_symm hPF)
    rw [h, angle_symm hPD hDF.symm] at hadd
    have hlt := CommonNotion5 (a := ∠ E D F) hFDP
    rw [← hadd] at hlt
    exact lt_irrefl _ hlt
  · /- F lies within the angle EDP (Triple incidence 2, along the named N): again the part
       would be equal to the whole. -/
    have hEF_N : SameSide E F N :=
      triple_incidence2 hD hDM hDN hE hFM hPN (same_side_symm hPF) hs hP_M hDE.symm
    have hF_N : ¬ OnLine F N := fun hF_N => hP_M (line_unique hDF hDN hF_N hDM hFM ▸ hPN)
    have hLN : L ≠ N := fun e => hP_L (e ▸ hPN)
    have hadd : ∠ E D P = ∠ E D F + ∠ F D P :=
      angle_add_of_inside hD hDN hE hPN hDE hPD.symm hF_L hF_N hLN hEF_N hPF
    rw [h] at hadd
    have hlt := CommonNotion5 (a := ∠ E D F) hFDP
    rw [← hadd] at hlt
    exact lt_irrefl _ hlt

/-- Metric 3, as `Tacit.len_symm` states it. -/
theorem Cited.holds_lenSymm : Cited.lenSymm.Holds primitives := fun v _ => len_symm (v.pt .A) (v.pt .B)

/-- Metric 4, as `Tacit.angle_symm` states it. -/
theorem Cited.holds_angleSymm : Cited.angleSymm.Holds primitives := by
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  exact angle_symm h.1 h.2.1

/-- Metric 9, as `Tacit.area_congruent` states it. -/
theorem Cited.holds_areaCongruent : Cited.areaCongruent.Holds primitives := by
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := h
  exact area_congruent h₁ h₂ h₃ h₄ h₅ h₆

/-- Book Zero's `ne_of_len_eq`. -/
theorem Cited.holds_neOfLen : Cited.neOfLen.Holds primitives := by
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  exact ne_of_len_eq h.1 h.2.1

/-- Book Zero's `OnRay.eq_of_len_eq`, with the straight line named. -/
theorem Cited.holds_rayUnique : Cited.rayUnique.Holds primitives := by
  intro v h
  simp only [Cited.law, List.forall_mem_cons] at h
  obtain ⟨hAB, hPA, hA, hB, hP, hPAB, hlen, -⟩ := h
  exact OnRay.eq_of_len_eq ⟨hAB, hPA, ⟨_, hA, hB, hP⟩, hPAB⟩ hlen

/-- One ray for one angle, its straight line: `onLine_of_angle_eq_named`. -/
theorem Cited.holds_rayOfAngle : Cited.rayOfAngle.Holds primitives := by
  intro v h
  simp only [Cited.law, rayOfAnglePremises, List.forall_mem_cons] at h
  obtain ⟨hDE, hD, hE, hDM, hFM, hDN, hPN, hPF, hang, -⟩ := h
  exact onLine_of_angle_eq_named hDE hD hE hDM hFM hDN hPN hPF hang

/-- One ray for one angle, its side: D is not between P and F, for they are on one side of L
(Pasch 3). -/
theorem Cited.holds_rayOfAngleSide : Cited.rayOfAngleSide.Holds primitives := by
  intro v h
  simp only [Cited.law, rayOfAnglePremises, List.forall_mem_cons] at h
  obtain ⟨-, hD, -, -, -, -, -, hPF, -, -⟩ := h
  exact fun hb => pasch3 hb hD hPF

/-- **Every law that draws nothing holds**, from the proofs above. `#print axioms` for this
theorem lists every axiom those proofs use; none of them constructs an object. -/
theorem Cited.holds_of_drawsNothing : ∀ c : Cited, c.drawsNothing = true → c.Holds primitives
  | .lenSymm, _ => Cited.holds_lenSymm
  | .angleSymm, _ => Cited.holds_angleSymm
  | .areaCongruent, _ => Cited.holds_areaCongruent
  | .neOfLen, _ => Cited.holds_neOfLen
  | .rayUnique, _ => Cited.holds_rayUnique
  | .rayOfAngle, _ => Cited.holds_rayOfAngle
  | .rayOfAngleSide, _ => Cited.holds_rayOfAngleSide

end Elements.Superposition
