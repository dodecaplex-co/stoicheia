import Staging.Superposition.Rule
import Elements.BookI.Prop07

/-!
# I.8 from the restricted rule

A prototype of Book I, Proposition 8 proved from the restricted rule of superposition
([brief 0009](../../docs/briefs/0009-superposition.md)), beside the edition's
`Elements.BookI.Prop8`, which uses the present rule. The statement is I.8's, word for
word, with two more hypotheses: the rule itself, `S : Rule`, and I.7's statement, `h7`,
which Euclid cites inside the placement. In the edition I.7 is proved before I.8, from I.5
and I.4; once I.4 is proved from the restricted rule, the library's `Prop7` supplies `h7`
(the `example` at the end checks that it fits).

Euclid's argument is kept. The triangle ABC is laid down with B on E and BC along EF, on
D's side. In Lean the copy has its own corners: C′, where C comes down, and G, where A
comes down. Those two are names in a derivation, never points that Lean holds: Euclid's
coincidences are steps of the derivation (C′ is F because BC is EF; G is D by I.7), and
what leaves the placement is one equality of angles among the given points.
-/

namespace Elements.Superposition

open Lit Tacit

namespace Prop8

/-- C′: where C comes down when BC is laid along EF. A name in the derivation. -/
abbrev C' : Name := .second

/-- G: where A comes down. A name in the derivation; Euclid calls it G. -/
abbrev G : Name := .third

/-- The laws the derivation cites: Metric 3, that a straight line equal to one with two
distinct ends has two distinct ends, one point at one distance on a ray, and I.7. -/
abbrev cites : List Cited := [.lenSymm, .neOfLen, .rayUnique, .prop7]

end Prop8

open Prop8 in
/-- If two triangles have the two sides equal to two sides respectively, and have also the base
equal to the base, they will also have the angles equal which are contained by the equal
straight lines. -/
theorem Prop8 (S : Rule)
    (h7 : ∀ {A B C D : Point}, SameSideOf C D A B → ‖C A‖ = ‖D A‖ → ‖C B‖ = ‖D B‖ → C = D)
    {A B C D E F : Point} (hABC : Triangle A B C)
    (hDEF : Triangle D E F) (hAB : ‖A B‖ = ‖D E‖) (hAC : ‖A C‖ = ‖D F‖) (hBC : ‖B C‖ = ‖E F‖) :
    ∠ B A C = ∠ E D F := by
  -- Let ABC, DEF be two triangles having the two sides AB, AC equal to the two sides DE, DF
  -- respectively, namely AB to DE, and AC to DF; and let them have the base BC equal to the
  -- base EF;
  /- The facts given, as literals the placement may use. -/
  let Γ : List (Lit Point) := [pos (.len A B D E), pos (.len A C D F), pos (.len B C E F)]
  have hΓ : ∀ ℓ ∈ Γ, ℓ.Holds id := by
    intro ℓ hℓ
    simp only [Γ, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact hAB
    · exact hAC
    · exact hBC
  -- I say that the angle BAC is also equal to the angle EDF.
  -- For, if the triangle ABC be applied to the triangle DEF, and if the point B be placed on
  -- the point E and the straight line BC on EF,
  /- To lay BC along EF we need the straight line EF itself (Postulate 1), and D off it,
     for the side on which A comes down. The placement is of the triangle BCA, with B on
     E, C along the ray from E through F, and A on D's side: everything that follows,
     until the angle comes out, is a derivation inside it. -/
  have hEF : E ≠ F := hDEF.ne₂₃
  obtain ⟨EF, hE_EF, hF_EF⟩ := Postulate1 E F hEF
  have hD_EF : ¬ OnLine D EF := fun hD => hDEF ⟨EF, hD, hE_EF, hF_EF⟩
  /- Δ is the context of the placement: the facts given, the guards, and what the
     placement keeps (`branch`). -/
  let Δ := branch Γ B C A E F D EF
  -- the point C will also coincide with F,
  -- because BC is equal to EF.
  /- C′ is on the ray from E through F, as far from E as F is; on a ray only one point is
     at that distance (Savile's argument). -/
  have hEC'_EF : Derives cites Δ (pos (.len E C' E F)) :=
    .len_trans Kept.len₁ (Branch.given (ℓ := pos (.len B C E F)) (by simp [Γ]))
  have hC'F : Derives cites Δ (pos (.eq C' F)) :=
    .ray_unique Guard.ne_DG (.ne_symm (.ne_of_len hEC'_EF Guard.ne_DG)) Guard.on_D Guard.on_G
      Kept.on_line Kept.not_between hEC'_EF
  -- Then, BC coinciding with EF,
  -- BA, AC will also coincide with ED, DF;
  /- The sides BA, AC have been carried to GE, GC′, that is GF, and they are equal to ED,
     DF. -/
  have hGE_DE : Derives cites Δ (pos (.len G E D E)) :=
    .len_trans Kept.len₃ (Branch.given (ℓ := pos (.len A B D E)) (by simp [Γ]))
  have hGF_DF : Derives cites Δ (pos (.len G F D F)) :=
    .len_trans .len_comm <|
    .len_trans (.len_congr (.eq_symm hC'F) .eq_refl) <|
    .len_trans Kept.len₂ <|
    .len_trans .len_comm (Branch.given (ℓ := pos (.len A C D F)) (by simp [Γ]))
  -- for, if the base BC coincides with the base EF, and the sides BA, AC do not coincide with
  -- ED, DF but fall beside them as EG, GF,
  -- then, given two straight lines constructed on a straight line (from its extremities) and
  -- meeting in a point, there will have been constructed on the same straight line (from its
  -- extremities), and on the same side of it, two other straight lines meeting in another
  -- point and equal to the former two respectively, namely each to that which has the same
  -- extremity with it.
  /- G and D are on the same side of EF: the placement put G there (`Kept.same_side`). -/
  -- But they cannot be so constructed. [I. 7]
  -- Therefore it is not possible that, if the base BC be applied to the base EF, the sides BA,
  -- AC should not coincide with ED, DF;
  -- they will therefore coincide,
  /- I.7, cited inside the placement: two points on one side of EF, each as far from E and
     from F as the other, are one point. Our I.7 is stated positively, so Euclid's
     reduction to the impossible is this one step. -/
  have hGD : Derives cites Δ (pos (.eq G D)) :=
    .prop7 Guard.ne_DG Guard.on_D Guard.on_G Kept.same_side hGE_DE hGF_DF
  -- so that the angle BAC will also coincide with the angle EDF, and will be equal to it.
  /- The angle BAC was carried to the angle EGC′, and G is D, C′ is F. This equality of
     angles names only given points, so it leaves the placement. -/
  have hBAC : Derives cites Δ (pos (.angle B A C E D F)) :=
    .angle_trans (.angle_symm Kept.angle₂) (.angle_congr .eq_refl hGD hC'F)
  /- The laws cited, each from its proof: three from Book Zero and the foundations, and
     I.7. -/
  have hcites : ∀ c ∈ cites, c.Law := by
    intro c hc
    simp only [cites, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact Cited.law_lenSymm
    · exact Cited.law_neOfLen
    · exact Cited.law_rayUnique
    · exact Cited.law_prop7 h7
  have hout := S.infer hcites hABC.bca hE_EF hF_EF hEF hD_EF hΓ
    (φ := [.angle B A C E D F]) fun m hm => by
      simp only [List.mem_singleton] at hm
      subst hm
      exact hBAC
  exact hout _ (List.mem_singleton_self _)
  -- If therefore etc.
  -- Q. E. D.

/-- The library's I.7 is the statement `Prop8` takes as `h7`. -/
example : ∀ {A B C D : Point}, SameSideOf C D A B → ‖C A‖ = ‖D A‖ → ‖C B‖ = ‖D B‖ → C = D :=
  fun hCD hCA hCB => BookI.Prop7 hCD hCA hCB

end Elements.Superposition
