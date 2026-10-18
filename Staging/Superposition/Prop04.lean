import Staging.Superposition.Rule

/-!
# I.4 from the restricted rule

A prototype of Book I, Proposition 4 proved from the restricted rule of superposition
([brief 0009](../../docs/briefs/0009-superposition.md)), beside the edition's
`Elements.BookI.Prop4`, which uses the present rule. The statement is I.4's, word for
word, with one more hypothesis: the rule itself, `S : Rule`.

Euclid's argument is kept. The triangle ABC is laid on DEF, A on D and AB along DE, on
F's side. In Lean the triangle as laid down is DB′C′, and B′, C′ are names in a
derivation, never points that Lean holds. Euclid's coincidences are steps of the
derivation: B′ is E because AB is DE; AC falls along DF because the angles at A and D are
equal; C′ is F because AC is DF. What leaves the placement is four equalities among the
given points: the bases, the triangles and the two remaining angles.
-/

namespace Elements.Superposition

open Lit Tacit

namespace Prop4

/-- B′: where B comes down when ABC is laid on DEF. A name in the derivation. -/
abbrev B' : Name := .second

/-- C′: where C comes down. A name in the derivation. -/
abbrev C' : Name := .third

/-- The laws the derivation cites: Metric 3, Metric 4, Metric 9, that a straight line
equal to one with distinct ends has distinct ends, one point at one distance on a ray, and
one ray for one angle. -/
abbrev cites : List Cited :=
  [.lenSymm, .angleSymm, .areaCongruent, .neOfLen, .rayUnique, .rayOfAngle]

end Prop4

open Prop4 in
/-- If two triangles have the two sides equal to two sides respectively, and have the angles
contained by the equal straight lines equal, they will also have the base equal to the base, the
triangle will be equal to the triangle, and the remaining angles will be equal to the remaining
angles respectively, namely those which the equal sides subtend. -/
theorem Prop4 (S : Rule) {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
    (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (hA : ∠ B A C = ∠ E D F) :
    ‖B C‖ = ‖E F‖ ∧ △ A B C = △ D E F ∧ ∠ A B C = ∠ D E F ∧ ∠ A C B = ∠ D F E := by
  -- Let ABC, DEF be two triangles having the two sides AB, AC equal to the two sides DE, DF
  -- respectively, namely AB to DE and AC to DF, and the angle BAC equal to the angle EDF.
  have hAB' : A ≠ B := hABC.ne₁₂
  have hBC' : B ≠ C := hABC.ne₂₃
  have hAC' : A ≠ C := hABC.ne₁₃
  have hDE : D ≠ E := hDEF.ne₁₂
  have hDF : D ≠ F := hDEF.ne₁₃
  have hEF : E ≠ F := hDEF.ne₂₃
  -- I say that the base BC is also equal to the base EF, the triangle ABC will be equal to the
  -- triangle DEF, and the remaining angles will be equal to the remaining angles respectively,
  -- namely those which the equal sides subtend, that is, the angle ABC to the angle DEF, and
  -- the angle ACB to the angle DFE.
  -- For, if the triangle ABC be applied to the triangle DEF,
  /- Euclid lays the triangle along the straight line DE, on the side where F is. The
     restricted rule takes that line by name, and F off it. The arguments below also name
     the straight line DF, the side of the triangle along which AC will fall, so that no
     step inside the placement draws a line. -/
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDE
  have hF_DE : ¬ OnLine F DE := fun hF => hDEF ⟨DE, hD_DE, hE_DE, hF⟩
  obtain ⟨DF, hD_DF, hF_DF⟩ := Postulate1 D F hDF
  /- The facts given, as literals the placement may use. -/
  let Γ : List (Lit Point) :=
    [pos (.len A B D E), pos (.len A C D F), pos (.angle B A C E D F),
     pos (.onLine D DF), pos (.onLine F DF), neg (.eq D F), neg (.eq E F),
     neg (.eq A B), neg (.eq B C), neg (.eq A C)]
  have hΓ : ∀ ℓ ∈ Γ, ℓ.Holds id := by
    intro ℓ hℓ
    simp only [Γ, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hAB
    · exact hAC
    · exact hA
    · exact hD_DF
    · exact hF_DF
    · exact hDF
    · exact hEF
    · exact hAB'
    · exact hBC'
    · exact hAC'
  -- and if the point A be placed on the point D
  -- and the straight line AB on DE,
  /- The restricted rule of superposition: the triangle ABC, laid down with A on D, is
     DB′C′, with B′ on the ray from D through E, C′ on F's side of DE, and every side and
     angle kept (`kept`). Everything that follows, until the four equalities come out, is
     a derivation inside the placement. -/
  /- Δ is the context of the placement: the facts given, the guards, and what the
     placement keeps (`branch`). -/
  let Δ := branch Γ A B C D E F DE
  have hAB_ : Derives cites Δ (neg (.eq A B)) := Branch.given (ℓ := neg (.eq A B)) (by simp [Γ])
  have hBC_ : Derives cites Δ (neg (.eq B C)) := Branch.given (ℓ := neg (.eq B C)) (by simp [Γ])
  have hAC_ : Derives cites Δ (neg (.eq A C)) := Branch.given (ℓ := neg (.eq A C)) (by simp [Γ])
  /- The corners laid down are three points: DB′, B′C′, C′D are AB, BC, CA, whose ends
     are distinct. -/
  have hB'D : Derives cites Δ (neg (.eq B' D)) := .ne_of_len (.len_trans .len_comm Kept.len₁) hAB_
  have hC'D : Derives cites Δ (neg (.eq C' D)) := .ne_of_len Kept.len₃ (.ne_symm hAC_)
  have hB'C' : Derives cites Δ (neg (.eq B' C')) := .ne_of_len Kept.len₂ hBC_
  -- then the point B will also coincide with E, because AB is equal to DE.
  /- On the ray from D through E, the one point as far from D as E is, is E itself
     (Savile's argument). -/
  have hDB'_DE : Derives cites Δ (pos (.len D B' D E)) :=
    .len_trans Kept.len₁ (Branch.given (ℓ := pos (.len A B D E)) (by simp [Γ]))
  have hB'E : Derives cites Δ (pos (.eq B' E)) :=
    .ray_unique Guard.ne_DG hB'D Guard.on_D Guard.on_G Kept.on_line Kept.not_between
      hDB'_DE
  -- Again, AB coinciding with DE,
  have hEDC' : Derives cites Δ (pos (.angle E D C' B' D C')) :=
    .angle_congr (.eq_symm hB'E) .eq_refl .eq_refl
  -- the straight line AC will also coincide with DF, because the angle BAC is equal to the
  -- angle EDF;
  /- On F's side of DE only one ray from D makes this angle with DE, so C′ lies on the
     straight line DF, on F's side of D. -/
  have hEDC'_EDF : Derives cites Δ (pos (.angle E D C' E D F)) :=
    .angle_trans hEDC' <|
    .angle_trans Kept.angle₁ (Branch.given (ℓ := pos (.angle B A C E D F)) (by simp [Γ]))
  have hD_DF' : Derives cites Δ (pos (.onLine D DF)) :=
    Branch.given (ℓ := pos (.onLine D DF)) (by simp [Γ])
  have hF_DF' : Derives cites Δ (pos (.onLine F DF)) :=
    Branch.given (ℓ := pos (.onLine F DF)) (by simp [Γ])
  have hC'_DF : Derives cites Δ (pos (.onLine C' DF)) :=
    .ray_of_angle Guard.ne_DG Guard.on_D Guard.on_G hD_DF' hF_DF' Kept.same_side hEDC'_EDF
  have hC'_ray : Derives cites Δ (neg (.between C' D F)) :=
    .ray_of_angle_side Guard.ne_DG Guard.on_D Guard.on_G hD_DF' hF_DF' Kept.same_side
      hEDC'_EDF
  -- hence the point C will also coincide with the point F, because AC is again equal to DF.
  have hDC'_DF : Derives cites Δ (pos (.len D C' D F)) :=
    .len_trans .len_comm <|
    .len_trans Kept.len₃ <|
    .len_trans .len_comm (Branch.given (ℓ := pos (.len A C D F)) (by simp [Γ]))
  have hC'F : Derives cites Δ (pos (.eq C' F)) :=
    .ray_unique (Branch.given (ℓ := neg (.eq D F)) (by simp [Γ])) hC'D hD_DF' hF_DF'
      hC'_DF hC'_ray hDC'_DF
  -- But B also coincided with E;
  -- hence the base BC will coincide with the base EF.
  -- [For if, when B coincides with E and C with F, the base BC does not coincide with the base
  -- EF, two straight lines will enclose a space: which is impossible.
  /- Heiberg brackets this passage as an early scholium. Our proof has no need of it: a
     finite straight line is fixed by its ends, so once B′ is E and C′ is F, the base
     B′C′ is EF. -/
  -- Therefore the base BC will coincide with EF] and will be equal to it. [C.N. 4]
  have hBC : Derives cites Δ (pos (.len B C E F)) :=
    .len_trans (.len_symm Kept.len₂) (.len_congr hB'E hC'F)
  -- Thus the whole triangle ABC will coincide with the whole triangle DEF,
  have hcoincide : Derives cites Δ (pos (.area D B' C' D E F)) :=
    .area_congr .eq_refl hB'E hC'F
  -- and will be equal to it.
  /- Being moved does not change the triangle: DB′C′ has the same sides and angles as
     ABC, so the same area (System E, Metric 9). -/
  have hmoved : Derives cites Δ (pos (.area A B C D B' C')) :=
    .area_of_congruent (.len_symm Kept.len₁) (.len_symm Kept.len₂) (.len_symm Kept.len₃)
      (.angle_trans (.angle_comm hAB_ (.ne_symm hBC_)) <|
        .angle_trans (.angle_symm Kept.angle₃) (.angle_comm (.ne_symm hB'C') (.ne_symm hB'D)))
      (.angle_trans (.angle_comm hBC_ hAC_) <|
        .angle_trans (.angle_symm Kept.angle₂) (.angle_comm (.ne_symm hC'D) hB'C'))
      (.angle_trans (.angle_comm (.ne_symm hAC_) (.ne_symm hAB_)) <|
        .angle_trans (.angle_symm Kept.angle₁) (.angle_comm hB'D hC'D))
  have harea : Derives cites Δ (pos (.area A B C D E F)) :=
    .area_trans hmoved hcoincide
  -- And the remaining angles will also coincide with the remaining angles and will be equal to
  -- them,
  -- the angle ABC to the angle DEF,
  have hB : Derives cites Δ (pos (.angle A B C D E F)) :=
    .angle_trans (.angle_comm hAB_ (.ne_symm hBC_)) <|
    .angle_trans (.angle_symm Kept.angle₃) <|
    .angle_trans (.angle_congr hC'F hB'E .eq_refl) <|
      .angle_comm (.ne_symm (Branch.given (ℓ := neg (.eq E F)) (by simp [Γ]))) Guard.ne_DG
  -- and the angle ACB to the angle DFE.
  have hC : Derives cites Δ (pos (.angle A C B D F E)) :=
    .angle_trans (.angle_symm Kept.angle₂) (.angle_congr .eq_refl hC'F hB'E)
  /- Four equalities among the given points: they leave the placement, and B′, C′ stay
     behind. -/
  /- The laws cited, each from its proof in Book Zero and the foundations. -/
  have hcites : ∀ c ∈ cites, c.Law := by
    intro c hc
    simp only [cites, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Cited.law_lenSymm
    · exact Cited.law_angleSymm
    · exact Cited.law_areaCongruent
    · exact Cited.law_neOfLen
    · exact Cited.law_rayUnique
    · exact Cited.law_rayOfAngle
  have hout := S.infer hcites hABC hD_DE hE_DE hDE hF_DE hΓ
    (φ := [.len B C E F, .area A B C D E F, .angle A B C D E F, .angle A C B D F E])
    fun m hm => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact hBC
      · exact harea
      · exact hB
      · exact hC
  -- Therefore etc.
  exact ⟨hout (.len B C E F) (by simp), hout (.area A B C D E F) (by simp),
    hout (.angle A B C D E F) (by simp), hout (.angle A C B D F E) (by simp)⟩
  -- (Being) what it was required to prove.

end Elements.Superposition
