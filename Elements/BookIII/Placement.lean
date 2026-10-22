import Elements.Figure.Basics
import Elements.BookI.HelpersTriangles
import Elements.BookIII.Placement.Exists
import Elements.BookIII.Placement.Unique
import Elements.BookIII.Placement.OnLine
import Elements.BookIII.Placement.Mixed
import Elements.BookIII.Placement.Strict

/-!
# Placement: one segment applied to another

Euclid applies one figure to another: "let the point A be placed on C and the straight line
AB on CD" (III.24). On equal straight lines AB, CD, `placement` carries the closed
half-plane on E's side of AB (the side with the straight line itself) onto the closed
half-plane on F's side of CD, A on C and B on D, keeping every distance between its points;
each point goes to the point as far from C as it was from A, and as far from D as it was
from B; and a point stays off the base, or between its ends, exactly when its image does.

**How.** No motion is assumed beyond I.4 and I.8, the two propositions that use
superposition. The place of each point is chosen (`Classical.epsilon`): it exists (I.22, or
I.3 and producing on the base) and is the only one (I.7 off the base, the order of points
on it, and I.20's degenerate case between them). That every distance is kept is the long
part, split by where the two points lie: both on the base, one on it, or both off it, where
whichever end of the base gives unequal angles is used (I.8, `BookI.Prop24.within`, C.N. 3,
I.4). The map is onto because the same construction runs back from CD to AB. The cases are
in `Elements/BookIII/Placement/`, a file each.

**Who may cite it.** III.24, where Euclid applies one segment to the other, and the bridge
theorems of `Elements/BookIII/Arcs.lean`, and no other proof. The lemmas of the `Placement`
namespace carry the same distance-keeping content, so `scripts/check_fidelity.py` holds them
all to the same rule.
-/

namespace Elements.BookIII

open Tacit

/-- A is a point of the straight line AB. -/
private theorem collinear_self_left (A B : Point) : Collinear A B A := by
  obtain ⟨L, hA, hB⟩ := collinear_of_two A B
  exact ⟨L, hA, hB, hA⟩

/-- B is a point of the straight line AB. -/
private theorem collinear_self_right (A B : Point) : Collinear A B B := by
  obtain ⟨L, hA, hB⟩ := collinear_of_two A B
  exact ⟨L, hA, hB, hB⟩

/-- **Every point of the half-plane has a place.** On equal straight lines AB, CD, a point P
on E's side of AB or on AB has a point Q on F's side of CD or on CD, as far from C as P is
from A and from D as P is from B. (`Placement.exists_off`, `Placement.exists_on`.) -/
theorem Placement.exists {A B C D E F P : Point} (hE : ¬ Collinear A B E)
    (hF : ¬ Collinear C D F) (hlen : ‖A B‖ = ‖C D‖) (hP : OnSideOrLine P E A B) :
    ∃ Q : Point, OnSideOrLine Q F C D ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖ := by
  rcases hP with hPE | hPl
  · obtain ⟨Q, hQ, h₁, h₂⟩ := Placement.exists_off hlen hF hPE.triangle
    exact ⟨Q, Or.inl hQ, h₁, h₂⟩
  · obtain ⟨Q, hQ, h₁, h₂⟩ := Placement.exists_on hlen (show Triangle A B E from hE).ne₁₂ hPl
    exact ⟨Q, Or.inr hQ, h₁, h₂⟩

/-- **Only one place in the half-plane.** Two points on F's side of CD or on CD, equally far
from C and equally far from D, are one point: by I.7 when both are off CD, by the order of
points when both are on it, and never one on and one off, by I.20's degenerate case. -/
theorem Placement.unique {C D F Q₁ Q₂ : Point} (hF : ¬ Collinear C D F)
    (hQ₁ : OnSideOrLine Q₁ F C D) (hQ₂ : OnSideOrLine Q₂ F C D) (hC : ‖C Q₁‖ = ‖C Q₂‖)
    (hD : ‖D Q₁‖ = ‖D Q₂‖) : Q₁ = Q₂ := by
  have hcol : Collinear C D Q₁ ↔ Collinear C D Q₂ := BookI.Prop20.collinear_congr rfl hC hD
  rcases hQ₁ with h₁ | h₁ <;> rcases hQ₂ with h₂ | h₂
  · exact Placement.unique_off h₁ h₂ hC hD
  · exact absurd (hcol.mpr h₂) h₁.triangle
  · exact absurd (hcol.mp h₁) h₂.triangle
  · exact Placement.unique_on (show Triangle C D F from hF).ne₁₂ h₁ h₂ hC hD

/-- **Two points off the base keep their distance.** The base point is chosen: at A if the
angles BAP, BAQ differ, at B otherwise (`Placement.base_choice`), and the lesser angle
named first (`Placement.dist_strict`). One point twice over goes to one point (I.7). -/
theorem Placement.dist_off_off {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hPQ : SameSideOf P Q A B) (hP'Q' : SameSideOf P' Q' C D)
    (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖) (hQ₁ : ‖C Q'‖ = ‖A Q‖)
    (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖ := by
  by_cases hne : P = Q
  · subst hne
    have h : P' = Q' := Placement.unique_off hP'Q' (hP'Q'.symm.trans hP'Q')
      (hP₁.trans hQ₁.symm) (hP₂.trans hQ₂.symm)
    rw [h, len_self, len_self]
  · have hlen' : ‖B A‖ = ‖D C‖ := by rw [len_symm B A, hlen, len_symm C D]
    rcases Placement.base_choice hPQ hne with h | h
    · rcases lt_trichotomy (∠ B A P) (∠ B A Q) with hlt | heq | hgt
      · exact Placement.dist_strict hlen hPQ hP'Q' hP₁ hP₂ hQ₁ hQ₂ hlt
      · exact absurd heq h
      · rw [len_symm P' Q', len_symm P Q]
        exact Placement.dist_strict hlen hPQ.symm hP'Q'.symm hQ₁ hQ₂ hP₁ hP₂ hgt
    · rcases lt_trichotomy (∠ A B P) (∠ A B Q) with hlt | heq | hgt
      · exact Placement.dist_strict hlen' hPQ.swap hP'Q'.swap hP₂ hP₁ hQ₂ hQ₁ hlt
      · exact absurd heq h
      · rw [len_symm P' Q', len_symm P Q]
        exact Placement.dist_strict hlen' hPQ.symm.swap hP'Q'.symm.swap hQ₂ hQ₁ hP₂ hP₁ hgt

/-- **Any two points of the half-plane keep their distance**, by where they lie: both on the
base, one on it, or both off it. Whether a place is on the base is decided by the distances
(`Prop20.collinear_congr`). -/
theorem Placement.dist {A B C D E F P Q P' Q' : Point} (hE : ¬ Collinear A B E)
    (hlen : ‖A B‖ = ‖C D‖) (hP : OnSideOrLine P E A B) (hQ : OnSideOrLine Q E A B)
    (hP' : OnSideOrLine P' F C D) (hQ' : OnSideOrLine Q' F C D)
    (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖) (hQ₁ : ‖C Q'‖ = ‖A Q‖)
    (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖ := by
  have cP : Collinear A B P ↔ Collinear C D P' :=
    BookI.Prop20.collinear_congr hlen hP₁.symm hP₂.symm
  have cQ : Collinear A B Q ↔ Collinear C D Q' :=
    BookI.Prop20.collinear_congr hlen hQ₁.symm hQ₂.symm
  rcases hP with hPE | hPl <;> rcases hQ with hQE | hQl
  · have hP'F : SameSideOf P' F C D := hP'.resolve_right fun h => hPE.triangle (cP.mpr h)
    have hQ'F : SameSideOf Q' F C D := hQ'.resolve_right fun h => hQE.triangle (cQ.mpr h)
    exact Placement.dist_off_off hlen (hPE.trans hQE.symm) (hP'F.trans hQ'F.symm)
      hP₁ hP₂ hQ₁ hQ₂
  · rw [len_symm P' Q', len_symm P Q]
    exact Placement.dist_on_off hlen hQl hPE.triangle (cQ.mp hQl)
      (fun h => hPE.triangle (cP.mpr h)) hQ₁ hQ₂ hP₁ hP₂
  · exact Placement.dist_on_off hlen hPl hQE.triangle (cP.mp hPl)
      (fun h => hQE.triangle (cQ.mpr h)) hP₁ hP₂ hQ₁ hQ₂
  · exact Placement.dist_on_on hlen (show Triangle A B E from hE).ne₁₂ hPl hQl (cP.mp hPl)
      (cQ.mp hQl) hP₁ hP₂ hQ₁ hQ₂

/-- **Placement.** On equal straight lines AB, CD, with E off AB and F off CD, there is a
map of points that puts A on C and B on D, and carries the points on E's side of AB or on
AB onto the points on F's side of CD or on CD, keeping every distance between them. Each
such point P goes to a point as far from C as P is from A, and from D as P is from B; P is
on E's side exactly when its image is on F's side; and P is between A and B exactly when
its image is between C and D.

Proved from its cases: each point's place is chosen; it exists and is unique;
A's place is C and B's is D; the map is onto because the construction runs back from CD to
AB, and the place found there is the one chosen.

Ground for III.24 (Euclid's application of one segment to the other), and for `Arcs.lean`;
no other proof may cite it, or any lemma of the `Placement` namespace. -/
theorem placement {A B C D E F : Point} (hE : ¬ Collinear A B E) (hF : ¬ Collinear C D F)
    (hlen : ‖A B‖ = ‖C D‖) :
    ∃ f : Point → Point, f A = C ∧ f B = D ∧
      Places f (OnSideOrLine · E A B) (OnSideOrLine · F C D) ∧
      ∀ P : Point, OnSideOrLine P E A B → ‖C (f P)‖ = ‖A P‖ ∧ ‖D (f P)‖ = ‖B P‖ ∧
        (SameSideOf P E A B ↔ SameSideOf (f P) F C D) ∧ (Between A P B ↔ Between C (f P) D) := by
  haveI : Nonempty Point := ⟨A⟩
  /- The place of each point P of the half-plane is chosen: a point on F's side of CD or on
     CD, as far from C as P is from A, and from D as P is from B. -/
  obtain ⟨f, hf⟩ : ∃ f : Point → Point, ∀ P : Point, OnSideOrLine P E A B →
      OnSideOrLine (f P) F C D ∧ ‖C (f P)‖ = ‖A P‖ ∧ ‖D (f P)‖ = ‖B P‖ :=
    ⟨fun P => Classical.epsilon fun Q => OnSideOrLine Q F C D ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖,
      fun P hP => Classical.epsilon_spec
        (p := fun Q => OnSideOrLine Q F C D ∧ ‖C Q‖ = ‖A P‖ ∧ ‖D Q‖ = ‖B P‖)
        (Placement.exists hE hF hlen hP)⟩
  /- Any point with those distances is the one chosen. -/
  have hf_eq : ∀ P Q : Point, OnSideOrLine P E A B → OnSideOrLine Q F C D →
      ‖C Q‖ = ‖A P‖ → ‖D Q‖ = ‖B P‖ → f P = Q := fun P Q hP hQ h₁ h₂ =>
    Placement.unique hF (hf P hP).1 hQ ((hf P hP).2.1.trans h₁.symm)
      ((hf P hP).2.2.trans h₂.symm)
  refine ⟨f, ?_, ?_, ⟨fun P hP => (hf P hP).1, ?_, ?_⟩, ?_⟩
  /- A goes to C, and B to D. -/
  · exact hf_eq A C (Or.inr (collinear_self_left A B)) (Or.inr (collinear_self_left C D))
      (by rw [len_self, len_self]) (by rw [len_symm D C, ← hlen, len_symm A B])
  · exact hf_eq B D (Or.inr (collinear_self_right A B)) (Or.inr (collinear_self_right C D))
      hlen.symm (by rw [len_self, len_self])
  /- Onto: the construction run back from CD to AB finds a point whose place is Q. -/
  · intro Q hQ
    obtain ⟨P, hP, h₁, h₂⟩ := Placement.exists hF hE hlen.symm hQ
    exact ⟨P, hP, hf_eq P Q hP hQ h₁.symm h₂.symm⟩
  /- Every distance is kept. -/
  · intro P Q hP hQ
    exact Placement.dist hE hlen hP hQ (hf P hP).1 (hf Q hQ).1 (hf P hP).2.1 (hf P hP).2.2
      (hf Q hQ).2.1 (hf Q hQ).2.2
  /- Off the base, and between its ends, are decided by the distances. -/
  · intro P hP
    obtain ⟨hQ, h₁, h₂⟩ := hf P hP
    have hcol : Collinear A B P ↔ Collinear C D (f P) :=
      BookI.Prop20.collinear_congr hlen h₁.symm h₂.symm
    exact ⟨h₁, h₂,
      ⟨fun hPE => hQ.resolve_right fun h => hPE.triangle (hcol.mpr h),
        fun hQF => hP.resolve_right fun h => hQF.triangle (hcol.mp h)⟩,
      BookI.Prop20.between_congr hlen h₁.symm h₂.symm⟩

end Elements.BookIII
