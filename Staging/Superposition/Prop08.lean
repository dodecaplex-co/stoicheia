import Staging.Superposition.Rule
import Elements.BookI.Prop07

/-!
# I.8 from the restricted rule

A prototype of Book I, Proposition 8 proved from the restricted rule of superposition
([brief 0009](../../docs/briefs/0009-superposition.md)), beside the edition's
`Elements.BookI.Prop8`, which uses the present rule. The statement is I.8's, word for word,
with two more hypotheses: the rule itself, `S : Rule`, and I.7's statement, `h7`, which
Euclid cites inside the placement. In the edition I.7 is proved before I.8: it cites I.5,
and rests on I.4 through it. Once I.4 is proved from the restricted rule, the library's
`Prop7` supplies `h7` (the `example` at the end checks that it fits).

Euclid's argument is kept. The triangle ABC is laid down with B on E and BC along EF, on D's
side. The derivation works on symbols, written in lower case: `a`, …, `f` for the corners of
the two triangles and `ef` for the straight line EF, and, for what the placement lays down,
`c'` for where C comes down and `g` for where A comes down, Euclid's G. The figure is the
valuation `v`; it gives nothing to `c'` or `g`. Euclid's coincidences are steps of the
derivation (c′ is f because BC is EF; g is d by I.7), and what leaves the placement is one
equality of angles among the figure's symbols.

I.7 is the one law cited here whose own proof draws: it draws three straight lines, produces
two and cites I.5. Citing it draws nothing in the placement. Brief 0009, open question 4,
asks whether a stricter reading should forbid it there; Euclid's route needs it.
-/

namespace Elements.Superposition

open Lit Tacit

namespace Prop8

/-- The points of I.8's figure, as symbols: the corners of the two triangles. -/
inductive Pt where
  | a | b | c | d | e | f

/-- The straight line of I.8's figure, as a symbol: EF, along which BC is laid. -/
inductive Ln where
  | ef

instance : Symbols Pt where
  card := 6
  index
    | .a => 0 | .b => 1 | .c => 2 | .d => 3 | .e => 4 | .f => 5
  symbol i := [Pt.a, .b, .c, .d, .e, .f].getD i.val .a
  symbol_index p := by cases p <;> rfl

instance : Symbols Ln where
  card := 1
  index _ := 0
  symbol _ := .ef
  symbol_index l := by cases l; rfl

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
/-- C′: where C comes down when BC is laid along EF. A symbol, with no point. -/
abbrev c' : Name Pt := .second
/-- G: where A comes down; Euclid calls it G. A symbol, with no point. -/
abbrev g : Name Pt := .third
/-- EF, in the placement. -/
abbrev ef : LineName Ln := .given .ef

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
  /- To lay BC along EF we need the straight line EF itself (Postulate 1), and D off it, for
     the side on which A comes down. -/
  have hEF : E ≠ F := hDEF.ne₂₃
  obtain ⟨EF, hE_EF, hF_EF⟩ := Postulate1 E F hEF
  have hD_EF : ¬ OnLine D EF := fun hD => hDEF ⟨EF, hD, hE_EF, hF_EF⟩
  /- The figure: each symbol of I.8's vocabulary stands for its point or straight line. -/
  let v : Val Pt Ln :=
    ⟨fun | .a => A | .b => B | .c => C | .d => D | .e => E | .f => F, fun | .ef => EF⟩
  /- The facts given, as literals over the figure's symbols. -/
  let Γ : List (Lit Pt Ln) := [pos (.len .a .b .d .e), pos (.len .a .c .d .f), pos (.len .b .c .e .f)]
  have hΓ : ∀ ℓ ∈ Γ, ℓ.Holds v := by
    intro ℓ hℓ
    simp only [Γ, List.mem_cons, List.mem_nil_iff, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact hAB
    · exact hAC
    · exact hBC
  -- I say that the angle BAC is also equal to the angle EDF.
  -- For, if the triangle ABC be applied to the triangle DEF, and if the point B be placed on
  -- the point E and the straight line BC on EF,
  /- The placement is of the triangle BCA, with B on E, C along the ray from E through F, and
     A on D's side: everything that follows, until the angle comes out, is a derivation
     inside it, on symbols only. -/
  /- Δ is the context of the placement: the facts given, the guards, and what the placement
     keeps (`branch`). -/
  let Δ := branch Γ .b .c .a .e .f .d .ef
  have given : ∀ {ℓ : Lit Pt Ln}, ℓ ∈ Γ → Derives cites Δ (ℓ.map .given .given) :=
    fun hℓ => Branch.given hℓ
  -- the point C will also coincide with F,
  -- because BC is equal to EF.
  /- c′ is on the ray from e through f, as far from e as f is; on a ray only one point is at
     that distance (Savile's argument). -/
  have hEC'_EF : Derives cites Δ (pos (.len e c' e f)) :=
    .len_trans Kept.len₁ (given (ℓ := pos (.len .b .c .e .f)) (by simp [Γ]))
  have hC'F : Derives cites Δ (pos (.eq c' f)) :=
    .ray_unique Guard.ne_DG (.ne_symm (.ne_of_len hEC'_EF Guard.ne_DG)) Guard.on_D Guard.on_G
      Kept.on_line Kept.not_between hEC'_EF
  -- Then, BC coinciding with EF,
  -- BA, AC will also coincide with ED, DF;
  /- The sides BA, AC have been carried to ge, gc′, that is gf, and they are equal to ED,
     DF. -/
  have hGE_DE : Derives cites Δ (pos (.len g e d e)) :=
    .len_trans Kept.len₃ (given (ℓ := pos (.len .a .b .d .e)) (by simp [Γ]))
  have hGF_DF : Derives cites Δ (pos (.len g f d f)) :=
    .len_trans .len_comm <|
    .len_trans (.len_congr (.eq_symm hC'F) .eq_refl) <|
    .len_trans Kept.len₂ <|
    .len_trans .len_comm (given (ℓ := pos (.len .a .c .d .f)) (by simp [Γ]))
  -- for, if the base BC coincides with the base EF, and the sides BA, AC do not coincide with
  -- ED, DF but fall beside them as EG, GF,
  -- then, given two straight lines constructed on a straight line (from its extremities) and
  -- meeting in a point, there will have been constructed on the same straight line (from its
  -- extremities), and on the same side of it, two other straight lines meeting in another
  -- point and equal to the former two respectively, namely each to that which has the same
  -- extremity with it.
  /- g and d are on the same side of ef: the placement put g there (`Kept.same_side`). -/
  -- But they cannot be so constructed. [I. 7]
  -- Therefore it is not possible that, if the base BC be applied to the base EF, the sides BA,
  -- AC should not coincide with ED, DF;
  -- they will therefore coincide,
  /- I.7, cited inside the placement: two points on one side of ef, each as far from e and
     from f as the other, are one point. Our I.7 is stated positively, so Euclid's reduction
     to the impossible is this one step. -/
  have hGD : Derives cites Δ (pos (.eq g d)) :=
    .prop7 Guard.ne_DG Guard.on_D Guard.on_G Kept.same_side hGE_DE hGF_DF
  -- so that the angle BAC will also coincide with the angle EDF, and will be equal to it.
  /- The angle BAC was carried to the angle e g c′, and g is d, c′ is f. This equality of
     angles names only the figure's symbols, so it leaves the placement. -/
  have hBAC : Derives cites Δ (pos (.angle b a c e d f)) :=
    .angle_trans (.angle_symm Kept.angle₂) (.angle_congr .eq_refl hGD hC'F)
  /- The laws cited, each from its proof: three from Book Zero and the foundations, and I.7.
     The guards are the triangle BCA, E and F on EF, E not F, and D off EF. -/
  have hcites : ∀ c ∈ cites, c.Holds := by
    intro c hc
    simp only [cites, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact Cited.holds_lenSymm
    · exact Cited.holds_neOfLen
    · exact Cited.holds_rayUnique
    · exact Cited.holds_prop7 h7
  have out := S.apply hcites (φ := .angle .b .a .c .e .d .f) hBAC v
  exact out hABC.bca hE_EF hF_EF hEF hD_EF hΓ
  -- If therefore etc.
  -- Q. E. D.

/-- The library's I.7 is the statement `Prop8` takes as `h7`. -/
example : ∀ {A B C D : Point}, SameSideOf C D A B → ‖C A‖ = ‖D A‖ → ‖C B‖ = ‖D B‖ → C = D :=
  fun hCD hCA hCB => BookI.Prop7 hCD hCA hCB

end Elements.Superposition
