import Elements.Figure.Basics
import Elements.Figure.Superposition

/-!
# Book I, Proposition 4

Euclid's text, in Heath's translation: [`heath/I/04.md`](../../heath/I/04.md).
Each of his sentences is a `--` comment, followed by the Lean that carries it out.

The triangle ABC is hypothetically laid on DEF, with A on D and AB along DE, on F's
side. Lower-case symbols name the figure's corners and straight lines; b′, c′ and
ac′ name the placed corners and the side AC as it falls. The valuation gives points
and straight lines only to the original figure's symbols.

Euclid's coincidences are steps of the restricted derivation: b′ is e because AB is
DE; AC falls along DF because the angles at A and D are equal; c′ is f because AC is
DF. Four equalities leave the placement: the bases, the areas and the two remaining
angles. The hypothetical corners and side stay within the derivation.
-/

namespace Elements.BookI

open Superposition hiding Triangle Collinear
open Superposition.Lit Tacit

namespace Prop4

/-- The points of I.4's figure, as symbols: the corners of the two triangles. -/
inductive Pt where
  | a | b | c | d | e | f

/-- The straight lines of I.4's figure, as symbols: DE, along which ABC is laid, and DF, along
which AC will fall. -/
inductive Ln where
  | de | df

instance : Symbols Pt where
  card := 6
  index
    | .a => 0 | .b => 1 | .c => 2 | .d => 3 | .e => 4 | .f => 5
  symbol i := [Pt.a, .b, .c, .d, .e, .f].getD i.val .a
  symbol_index p := by cases p <;> rfl

instance : Symbols Ln where
  card := 2
  index
    | .de => 0 | .df => 1
  symbol i := [Ln.de, .df].getD i.val .de
  symbol_index l := by cases l <;> rfl

/-- A, in the placement. -/
abbrev a : Name Pt := .given .a
/-- B, in the placement. -/
abbrev b : Name Pt := .given .b
/-- C, in the placement. -/
abbrev c : Name Pt := .given .c
/-- D, in the placement. -/
abbrev d : Name Pt := .given .d
/-- E, in the placement. -/
abbrev e : Name Pt := .given .e
/-- F, in the placement. -/
abbrev f : Name Pt := .given .f
/-- B′: where B comes down when ABC is laid on DEF. A symbol, with no point. -/
abbrev b' : Name Pt := .second
/-- C′: where C comes down. A symbol, with no point. -/
abbrev c' : Name Pt := .third
/-- DE, in the placement. -/
abbrev de : LineName Ln := .given .de
/-- DF, in the placement. -/
abbrev df : LineName Ln := .given .df
/-- The side AC as it falls: a straight line through D and C′. A symbol, with no straight
line. -/
abbrev ac' : LineName Ln := .side

/-- The laws the derivation cites: Metric 3, Metric 4, Metric 9, that a straight line equal to
one with distinct ends has distinct ends, one point at one distance on a ray, and one ray for
one angle. -/
abbrev cites : List Cited :=
  [.lenSymm, .angleSymm, .areaCongruent, .neOfLen, .rayUnique, .rayOfAngle, .rayOfAngleSide]

end Prop4

open Prop4 in
/-- If two triangles have the two sides equal to two sides respectively, and have the angles
contained by the equal straight lines equal, they will also have the base equal to the base, the
triangle will be equal to the triangle, and the remaining angles will be equal to the remaining
angles respectively, namely those which the equal sides subtend. -/
theorem Prop4 {A B C D E F : Point} (hABC : Triangle A B C) (hDEF : Triangle D E F)
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
  /- Euclid lays the triangle along the straight line DE, on the side where F is. The rule
     takes that line by its symbol, and F off it. The figure also has the straight line DF,
     along which AC will fall: both are drawn here, before the placement, and nothing is
     drawn inside it. -/
  obtain ⟨DE, hD_DE, hE_DE⟩ := Postulate1 D E hDE
  have hF_DE : ¬ OnLine F DE := fun hF => hDEF ⟨DE, hD_DE, hE_DE, hF⟩
  obtain ⟨DF, hD_DF, hF_DF⟩ := Postulate1 D F hDF
  /- The figure: each symbol of I.4's vocabulary stands for its point or straight line. -/
  let v : Val primitives Pt Ln :=
    ⟨fun | .a => A | .b => B | .c => C | .d => D | .e => E | .f => F,
     fun | .de => DE | .df => DF⟩
  /- The facts given, as literals over the figure's symbols. -/
  let Γ : List (Lit Pt Ln) :=
    [pos (.len .a .b .d .e), pos (.len .a .c .d .f), pos (.angle .b .a .c .e .d .f),
     pos (.onLine .d .df), pos (.onLine .f .df), neg (.eq .d .f), neg (.eq .e .f),
     neg (.eq .a .b), neg (.eq .b .c), neg (.eq .a .c)]
  have hΓ : ∀ ℓ ∈ Γ, ℓ.Holds v := by
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
     d b′ c′, with b′ on the ray from d through e, c′ on f's side of de, every side and angle
     kept, and the side AC laid down along ac′, through d and c′ (`kept`). Everything that
     follows, until the four equalities come out, is a derivation inside the placement:
     symbols only, and no point. -/
  /- Δ is the context of the placement: the facts given, the guards, and what the placement
     keeps (`branch`). -/
  let Δ := branch Γ .a .b .c .d .e .f .de
  have given : ∀ {ℓ : Lit Pt Ln}, ℓ ∈ Γ → Derives cites Δ (ℓ.map .given .given) :=
    fun hℓ => Branch.given hℓ
  have hAB_ : Derives cites Δ (neg (.eq a b)) := given (ℓ := neg (.eq .a .b)) (by simp [Γ])
  have hBC_ : Derives cites Δ (neg (.eq b c)) := given (ℓ := neg (.eq .b .c)) (by simp [Γ])
  have hAC_ : Derives cites Δ (neg (.eq a c)) := given (ℓ := neg (.eq .a .c)) (by simp [Γ])
  /- The corners laid down are three points: db′, b′c′, c′d are AB, BC, CA, whose ends are
     distinct. -/
  have hB'D : Derives cites Δ (neg (.eq b' d)) := .ne_of_len (.len_trans .len_comm Kept.len₁) hAB_
  have hC'D : Derives cites Δ (neg (.eq c' d)) := .ne_of_len Kept.len₃ (.ne_symm hAC_)
  have hB'C' : Derives cites Δ (neg (.eq b' c')) := .ne_of_len Kept.len₂ hBC_
  -- then the point B will also coincide with E, because AB is equal to DE.
  /- On the ray from d through e, the one point as far from d as e is, is e itself (Savile's
     argument). -/
  have hDB'_DE : Derives cites Δ (pos (.len d b' d e)) :=
    .len_trans Kept.len₁ (given (ℓ := pos (.len .a .b .d .e)) (by simp [Γ]))
  have hB'E : Derives cites Δ (pos (.eq b' e)) :=
    .ray_unique Guard.ne_DG hB'D Guard.on_D Guard.on_G Kept.on_line Kept.not_between hDB'_DE
  -- Again, AB coinciding with DE,
  have hEDC' : Derives cites Δ (pos (.angle e d c' b' d c')) :=
    .angle_congr Coincidence.step (.eq_symm hB'E) .eq_refl .eq_refl
  -- the straight line AC will also coincide with DF, because the angle BAC is equal to the
  -- angle EDF;
  /- On f's side of de only one ray from d makes this angle with de, so the side AC laid
     down, through d and c′, puts c′ on df, on f's side of d. -/
  have hEDC'_EDF : Derives cites Δ (pos (.angle e d c' e d f)) :=
    .angle_trans hEDC' <|
    .angle_trans Kept.angle₁ (given (ℓ := pos (.angle .b .a .c .e .d .f)) (by simp [Γ]))
  have hD_DF' : Derives cites Δ (pos (.onLine d df)) :=
    given (ℓ := pos (.onLine .d .df)) (by simp [Γ])
  have hF_DF' : Derives cites Δ (pos (.onLine f df)) :=
    given (ℓ := pos (.onLine .f .df)) (by simp [Γ])
  have hC'_DF : Derives cites Δ (pos (.onLine c' df)) :=
    .ray_of_angle Guard.ne_DG Guard.on_D Guard.on_G hD_DF' hF_DF' Kept.side_first
      Kept.side_third Kept.same_side hEDC'_EDF
  have hC'_ray : Derives cites Δ (neg (.between c' d f)) :=
    .ray_of_angle_side Guard.ne_DG Guard.on_D Guard.on_G hD_DF' hF_DF' Kept.side_first
      Kept.side_third Kept.same_side hEDC'_EDF
  -- hence the point C will also coincide with the point F, because AC is again equal to DF.
  have hDC'_DF : Derives cites Δ (pos (.len d c' d f)) :=
    .len_trans .len_comm <|
    .len_trans Kept.len₃ <|
    .len_trans .len_comm (given (ℓ := pos (.len .a .c .d .f)) (by simp [Γ]))
  have hC'F : Derives cites Δ (pos (.eq c' f)) :=
    .ray_unique (given (ℓ := neg (.eq .d .f)) (by simp [Γ])) hC'D hD_DF' hF_DF'
      hC'_DF hC'_ray hDC'_DF
  -- But B also coincided with E;
  -- hence the base BC will coincide with the base EF.
  -- [For if, when B coincides with E and C with F, the base BC does not coincide with the base
  -- EF, two straight lines will enclose a space: which is impossible.
  /- Heiberg brackets this passage as an early scholium. Our proof has no need of it: a
     finite straight line is fixed by its ends, so once b′ is e and c′ is f, the base b′c′
     is ef. -/
  -- Therefore the base BC will coincide with EF] and will be equal to it. [C.N. 4]
  have hBC : Derives cites Δ (pos (.len b c e f)) :=
    .len_trans (.len_symm Kept.len₂) (.len_congr Coincidence.step hB'E hC'F)
  -- Thus the whole triangle ABC will coincide with the whole triangle DEF,
  have hcoincide : Derives cites Δ (pos (.area d b' c' d e f)) :=
    .area_congr Coincidence.step .eq_refl hB'E hC'F
  -- and will be equal to it.
  /- Being moved does not change the triangle: d b′ c′ has the same sides and angles as
     ABC, so the same area (System E, Metric 9). -/
  have hmoved : Derives cites Δ (pos (.area a b c d b' c')) :=
    .area_of_congruent (.len_symm Kept.len₁) (.len_symm Kept.len₂) (.len_symm Kept.len₃)
      (.angle_trans (.angle_comm hAB_ (.ne_symm hBC_)) <|
        .angle_trans (.angle_symm Kept.angle₃) (.angle_comm (.ne_symm hB'C') (.ne_symm hB'D)))
      (.angle_trans (.angle_comm hBC_ hAC_) <|
        .angle_trans (.angle_symm Kept.angle₂) (.angle_comm (.ne_symm hC'D) hB'C'))
      (.angle_trans (.angle_comm (.ne_symm hAC_) (.ne_symm hAB_)) <|
        .angle_trans (.angle_symm Kept.angle₁) (.angle_comm hB'D hC'D))
  have harea : Derives cites Δ (pos (.area a b c d e f)) :=
    .area_trans hmoved hcoincide
  -- And the remaining angles will also coincide with the remaining angles and will be equal to
  -- them,
  -- the angle ABC to the angle DEF,
  have hB : Derives cites Δ (pos (.angle a b c d e f)) :=
    .angle_trans (.angle_comm hAB_ (.ne_symm hBC_)) <|
    .angle_trans (.angle_symm Kept.angle₃) <|
    .angle_trans (.angle_congr Coincidence.step hC'F hB'E .eq_refl) <|
      .angle_comm (.ne_symm (given (ℓ := neg (.eq .e .f)) (by simp [Γ]))) Guard.ne_DG
  -- and the angle ACB to the angle DFE.
  have hC : Derives cites Δ (pos (.angle a c b d f e)) :=
    .angle_trans (.angle_symm Kept.angle₂) (.angle_congr Coincidence.step .eq_refl hC'F hB'E)
  /- Four equalities among the figure's symbols: they leave the placement, and b′, c′ and
     ac′ stay behind. The laws cited are supplied by their proofs, one each, from Book Zero
     and the foundations; the guards are the triangle ABC, D and E on DE, D not E, and F off
     DE. -/
  have hcites : ∀ c ∈ cites, c.Holds primitives := by
    intro c hc
    simp only [cites, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Cited.holds_lenSymm
    · exact Cited.holds_angleSymm
    · exact Cited.holds_areaCongruent
    · exact Cited.holds_neOfLen
    · exact Cited.holds_rayUnique
    · exact Cited.holds_rayOfAngle
    · exact Cited.holds_rayOfAngleSide
  have out := fun {φ : Metric Pt}
      (dφ : Derives cites Δ (pos (φ.map Name.given).toAtom)) =>
    Tacit.superposition.apply hcites dφ v hABC hD_DE hE_DE hDE hF_DE hΓ
  -- Therefore etc.
  exact ⟨out (φ := .len .b .c .e .f) hBC, out (φ := .area .a .b .c .d .e .f) harea,
    out (φ := .angle .a .b .c .d .e .f) hB, out (φ := .angle .a .c .b .d .f .e) hC⟩
  -- (Being) what it was required to prove.

end Elements.BookI
