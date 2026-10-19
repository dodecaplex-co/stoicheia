import Elements.BookIII.Prop30

/-!
# III.30: congruent halves and their division

Proposed for the owner's approval. This statement is not yet assigned for proof.
It is staged only, with no companion registration or review record entry.
-/

namespace Elements.BookIII

theorem Prop30.halves {A B D P : Point} {ADB : Circle}
    (hA : OnCircle A ADB) (hB : OnCircle B ADB)
    (hD : OnCircle D ADB) (hDP : SameSideOf D P A B)
    (hequal : standing ADB A B D = standing ADB D A B) :
    ∃ Q R : Point,
      OppositeSidesOf Q B A D ∧ OppositeSidesOf R A D B ∧
      Arc.Drawn ⟨ADB, A, D, Q⟩ ∧ Arc.Drawn ⟨ADB, D, B, R⟩ ∧
      Arc.Congruent ⟨ADB, A, D, Q⟩ ⟨ADB, D, B, R⟩ ∧
      circumference ADB A Q D + circumference ADB D R B =
        circumference ADB A P B ∧
      (∀ X : Point, OnArc X ⟨ADB, A, B, P⟩ ↔
        OnArc X ⟨ADB, A, D, Q⟩ ∨ OnArc X ⟨ADB, D, B, R⟩) ∧
      (∀ X : Point,
        (OnArc X ⟨ADB, A, D, Q⟩ ∧ OnArc X ⟨ADB, D, B, R⟩) ↔
          X = D) := by
  sorry

end Elements.BookIII
