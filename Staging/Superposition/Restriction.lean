import Staging.Superposition.Rule

/-!
# Superposition, restricted: what the rule cannot do

The restriction theorem of [brief 0009](../../docs/briefs/0009-superposition.md), for the
prototype. Astra's third answer asks for evidence that the represented derivation system
cannot export the laid-down points as witnesses, nor take construction steps inside the
placement. Here it is, in four parts:

1. **No laid-down corner is exported** (`exportable_iff`, `not_exportable_second`,
   `not_exportable_third`): the rule's conclusions are formulas over given points, and a
   formula of the placement that names B′ or C′ is the image of none of them.
2. **The conclusions say nothing of where the corners went** (`Metric.holds_lift`): an
   exported formula reads the same whatever points B′ and C′ are taken to be. So the rule
   asserts no point exists, here or anywhere.
3. **No construction step** (`Derives.map`, with `Derives.sound`): every rule of a
   derivation is a scheme in its names, carried along any renaming, even one that merges
   names; and whatever it proves holds of the very points its names stand for. A step that
   built a point would need a name for it, and no rule supplies one.
4. **Nothing refutable is exported** (`Metric.holds_const`): every exportable formula
   holds when all its points are one point, so neither `False` nor any formula false in
   every figure can be a conclusion. This closes the door Astra's second observation
   opens, below.

The two observations of Astra's answer are kept as theorems, as warnings for anyone who
tries a shorter road: a Prop-valued eliminator over every conclusion is the existential
rule itself (`eliminator_iff_exists`), and one allowed only `False` still gives the points
back, classically (`eliminator_false_gives_exists`). Astra checked both in Lean 4.35; they
are restated here with thanks.

What is not here: a non-derivability result, that the restricted rule with the other laws
cannot prove the present rule. Astra's third kind of evidence asks for one only if it is
claimed, with the fragment of rules stated; this prototype claims none (brief 0009,
"Evidence before landing").
-/

namespace Elements.Superposition

/-! ## 1. No laid-down corner is exported -/

/-- **A formula of the placement can be exported exactly when it names only given
points.** The rule's conclusions are `Metric Point`; a formula over the placement's names
is the image of one of them exactly when every name in it is a given point. -/
theorem exportable_iff (m : Metric Name) :
    (∃ m₀ : Metric Point, m₀.map Name.given = m) ↔ ∀ n ∈ m.names, ∃ P : Point, n = .given P := by
  constructor
  · rintro ⟨m₀, rfl⟩ n hn
    rw [Metric.names_map, List.mem_map] at hn
    obtain ⟨P, -, rfl⟩ := hn
    exact ⟨P, rfl⟩
  · intro h
    cases m with
    | len P Q R S =>
      obtain ⟨P, rfl⟩ := h P (by simp [Metric.names])
      obtain ⟨Q, rfl⟩ := h Q (by simp [Metric.names])
      obtain ⟨R, rfl⟩ := h R (by simp [Metric.names])
      obtain ⟨S, rfl⟩ := h S (by simp [Metric.names])
      exact ⟨.len P Q R S, rfl⟩
    | angle P Q R S T U =>
      obtain ⟨P, rfl⟩ := h P (by simp [Metric.names])
      obtain ⟨Q, rfl⟩ := h Q (by simp [Metric.names])
      obtain ⟨R, rfl⟩ := h R (by simp [Metric.names])
      obtain ⟨S, rfl⟩ := h S (by simp [Metric.names])
      obtain ⟨T, rfl⟩ := h T (by simp [Metric.names])
      obtain ⟨U, rfl⟩ := h U (by simp [Metric.names])
      exact ⟨.angle P Q R S T U, rfl⟩
    | area P Q R S T U =>
      obtain ⟨P, rfl⟩ := h P (by simp [Metric.names])
      obtain ⟨Q, rfl⟩ := h Q (by simp [Metric.names])
      obtain ⟨R, rfl⟩ := h R (by simp [Metric.names])
      obtain ⟨S, rfl⟩ := h S (by simp [Metric.names])
      obtain ⟨T, rfl⟩ := h T (by simp [Metric.names])
      obtain ⟨U, rfl⟩ := h U (by simp [Metric.names])
      exact ⟨.area P Q R S T U, rfl⟩

/-- **B′ is never exported.** A formula of the placement that names B′ (`Name.second`) is
the image of no conclusion the rule can give. -/
theorem not_exportable_second {m : Metric Name} (h : Name.second ∈ m.names) :
    ¬ ∃ m₀ : Metric Point, m₀.map Name.given = m := fun hm => by
  obtain ⟨P, hP⟩ := (exportable_iff m).1 hm _ h
  exact Name.noConfusion hP

/-- **C′ is never exported.** A formula of the placement that names C′ (`Name.third`) is
the image of no conclusion the rule can give. -/
theorem not_exportable_third {m : Metric Name} (h : Name.third ∈ m.names) :
    ¬ ∃ m₀ : Metric Point, m₀.map Name.given = m := fun hm => by
  obtain ⟨P, hP⟩ := (exportable_iff m).1 hm _ h
  exact Name.noConfusion hP

/-! ## 2. The conclusions say nothing of where the corners went -/

/-- **An exported formula reads the same wherever B′ and C′ are.** Read in the placement,
with B′ and C′ at any points at all, an exported formula says exactly what it says of the
given points. -/
theorem Metric.holds_lift (m : Metric Point) (B' C' : Point) :
    (m.map Name.given).Holds (Name.at B' C') ↔ m.Holds id :=
  Metric.holds_map _ _ m

/-- **What the rule gives is a fact about the given points.** Every conclusion of `Rule`
is an equality of magnitudes among the given points, and nothing else: no point is said to
exist. (A restatement of `Rule.infer` in these words, so that a reader can find it.) -/
theorem Rule.conclusion (S : Rule) {cites : List Cited} (hcites : ∀ c ∈ cites, c.Law)
    {A B C D G H : Point} {L : Line} (hABC : Triangle A B C) (hD : OnLine D L)
    (hG : OnLine G L) (hDG : D ≠ G) (hH : ¬ OnLine H L) {Γ : List (Lit Point)}
    (hΓ : ∀ ℓ ∈ Γ, ℓ.Holds id) {m : Metric Point}
    (d : Derives cites (branch Γ A B C D G H L) (.pos (m.map Name.given).toAtom)) :
    m.toAtom.Holds id :=
  S.infer hcites hABC hD hG hDG hH hΓ (φ := [m]) (by simpa using d) m (by simp)

/-! ## 3. No construction step -/

namespace Derives

variable {V W : Type} {cites : List Cited} {Γ : List (Lit V)}

/-- **Every rule is a scheme in its names.** A derivation, its names renamed by any `f`
(even one that merges names), is a derivation from the renamed context. No rule depends on
which points its names are, and none introduces a name: a step that constructed a point
would need a fresh name, and no rule has one. -/
theorem map (f : V → W) {ℓ : Lit V} (d : Derives cites Γ ℓ) :
    Derives cites (Γ.map (Lit.map f)) (ℓ.map f) := by
  induction d with
  | given h => exact .given (List.mem_map_of_mem h)
  | eq_refl => exact .eq_refl
  | eq_symm _ ih => exact .eq_symm ih
  | ne_symm _ ih => exact .ne_symm ih
  | len_refl => exact .len_refl
  | len_symm _ ih => exact .len_symm ih
  | len_trans _ _ ih₁ ih₂ => exact .len_trans ih₁ ih₂
  | angle_refl => exact .angle_refl
  | angle_symm _ ih => exact .angle_symm ih
  | angle_trans _ _ ih₁ ih₂ => exact .angle_trans ih₁ ih₂
  | area_refl => exact .area_refl
  | area_symm _ ih => exact .area_symm ih
  | area_trans _ _ ih₁ ih₂ => exact .area_trans ih₁ ih₂
  | len_congr _ _ ih₁ ih₂ => exact .len_congr ih₁ ih₂
  | angle_congr _ _ _ ih₁ ih₂ ih₃ => exact .angle_congr ih₁ ih₂ ih₃
  | area_congr _ _ _ ih₁ ih₂ ih₃ => exact .area_congr ih₁ ih₂ ih₃
  | len_comm cite => exact .len_comm cite
  | angle_comm _ _ cite ih₁ ih₂ => exact .angle_comm ih₁ ih₂ cite
  | ne_of_len _ _ cite ih₁ ih₂ => exact .ne_of_len ih₁ ih₂ cite
  | area_of_congruent _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
    exact .area_of_congruent ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ cite
  | ray_unique _ _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ =>
    exact .ray_unique ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ cite
  | ray_of_angle _ _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ =>
    exact .ray_of_angle ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ cite
  | ray_of_angle_side _ _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ =>
    exact .ray_of_angle_side ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ cite
  | prop7 _ _ _ _ _ _ cite ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
    exact .prop7 ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ cite

end Derives

/-! ## 4. Nothing refutable is exported -/

/-- **No exported formula is `False` in disguise.** Every equality of magnitudes holds when
all the points it names are one point X. So the rule never concludes `False`, nor any
formula that fails in every figure: the contradiction Astra's second observation turns
into points is not a conclusion it can reach. -/
theorem Metric.holds_const {V : Type} (m : Metric V) (X : Point) : m.Holds (fun _ => X) := by
  cases m <;> exact rfl

/-! ## The shorter roads, and why they fail -/

/-- **Astra's first observation.** An eliminator that lets the placement prove any
proposition Q whatever is the existential rule itself: take Q to be "such points exist".
This is why the restricted rule is stated over derivations, not over propositions. -/
theorem eliminator_iff_exists (placed : Point → Point → Prop) :
    (∀ Q : Prop, (∀ B' C' : Point, placed B' C' → Q) → Q) ↔ ∃ B' C' : Point, placed B' C' :=
  ⟨fun h => h _ fun B' C' hp => ⟨B', C', hp⟩, fun ⟨B', C', hp⟩ _ hQ => hQ B' C' hp⟩

/-- **Astra's second observation.** Even an eliminator allowed only the conclusion `False`,
which names no point, gives the points back: it says their absence is absurd, and Lean's
classical logic turns that into existence. This is why the exported conclusions are
equalities of magnitudes (`Metric.holds_const`), and why no rule of a derivation concludes
anything from a contradiction. -/
theorem eliminator_false_gives_exists (placed : Point → Point → Prop)
    (h : (∀ B' C' : Point, placed B' C' → False) → False) : ∃ B' C' : Point, placed B' C' :=
  Classical.byContradiction fun hne => h fun B' C' hp => hne ⟨B', C', hp⟩

end Elements.Superposition
