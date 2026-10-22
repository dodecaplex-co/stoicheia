import Elements.Figure.Basics
import Elements.BookI.HelpersTriangles

/-!
# Placement: two points of the base

One of the five files of placement's cases (`Elements/BookIII/Placement.lean` gathers them).
Two points of the straight line AB keep their distance when they are sent to CD: their
order about A, decided by their distances from A and B (`Prop20.between_congr`), is their
images' order about C, and the distance between them is the sum or the difference of their
distances from A.
-/

namespace Elements.BookIII

open Tacit

/-- **Opposite rays, read off from B.** For two points P, Q of the straight line AB, neither
of them A, A lies between P and Q exactly when one of them, and not both, lies beyond A from
B. A figure shows it at a glance. It is what lets the order of P, Q about A be decided by
their distances from A and B, and so carried to C (`dist_on_on`). -/
theorem Placement.dist_on_on.opposite {A B P Q : Point} (hAB : A ≠ B)
    (hP : Collinear A B P) (hQ : Collinear A B Q) (hPA : P ≠ A) (hQA : Q ≠ A) :
    Between P A Q ↔
      (Between P A B ∧ ¬ Between Q A B) ∨ (¬ Between P A B ∧ Between Q A B) := by
  constructor
  · intro h
    by_cases hPAB : Between P A B
    · /- P is beyond A from B, and Q beyond A from P: so Q is not beyond A from B. -/
      exact Or.inl ⟨hPAB, fun hQAB =>
        not_between_of_between_between hPAB h (between_symm hQAB)⟩
    · /- P is on the ray AB; were Q on it too, A would not lie between them. -/
      refine Or.inr ⟨hPAB, ?_⟩
      exact Classical.byContradiction fun hQAB =>
        (show OnRay P A B from ⟨hAB, hPA, hP, hPAB⟩).not_between
          ⟨hAB, hQA, hQ, hQAB⟩ h
  · /- One point on the ray AB, the other beyond A from B: A lies between them. -/
    rintro (⟨hPAB, hQAB⟩ | ⟨hPAB, hQAB⟩)
    · exact (show OnRay Q A B from ⟨hAB, hQA, hQ, hQAB⟩).between hPAB
    · exact between_symm
        ((show OnRay P A B from ⟨hAB, hPA, hP, hPAB⟩).between hQAB)

/-- **Two points of the base keep their distance.** On equal straight lines AB, CD, let P,
Q be points of the straight line AB, and P', Q' points of the straight line CD, each as far
from C as its fellow is from A, and from D as its fellow is from B. Then P'Q' is equal to PQ.

Proved from the order of points on a straight line: P and Q are on one ray from A or
on opposite rays, and P', Q' alike (their distances from B and D decide it, by
`Prop20.between_congr`); then PQ is the difference or the sum of AP and AQ
(`len_add_of_between`), and P'Q' the same of CP' and CQ'. -/
theorem Placement.dist_on_on {A B C D P Q P' Q' : Point} (hlen : ‖A B‖ = ‖C D‖)
    (hAB : A ≠ B) (hP : Collinear A B P) (hQ : Collinear A B Q) (hP' : Collinear C D P')
    (hQ' : Collinear C D Q') (hP₁ : ‖C P'‖ = ‖A P‖) (hP₂ : ‖D P'‖ = ‖B P‖)
    (hQ₁ : ‖C Q'‖ = ‖A Q‖) (hQ₂ : ‖D Q'‖ = ‖B Q‖) : ‖P' Q'‖ = ‖P Q‖ := by
  /- A point at the start is carried to the start. -/
  by_cases hPA : P = A
  · subst P
    have hCP' : C = P' := eq_of_len_eq_zero (hP₁.trans (len_self A))
    subst P'
    exact hQ₁
  by_cases hQA : Q = A
  · subst Q
    have hCQ' : C = Q' := eq_of_len_eq_zero (hQ₁.trans (len_self A))
    subst Q'
    simpa only [len_symm P' C, len_symm P A] using hP₁
  have hCD : C ≠ D := ne_of_len_eq hlen.symm hAB
  have hCP' : C ≠ P' := ne_of_len_eq hP₁ (Ne.symm hPA)
  have hCQ' : C ≠ Q' := ne_of_len_eq hQ₁ (Ne.symm hQA)
  /- The distances from the two ends decide which points lie beyond A from B,
     and carry that order to C and D. -/
  have hPbetween : Between P A B ↔ Between P' C D :=
    BookI.Prop20.between_congr
      (by rw [len_symm P B, len_symm P' D]; exact hP₂.symm)
      (by rw [len_symm P A, len_symm P' C]; exact hP₁.symm)
      (by rw [len_symm B A, len_symm D C]; exact hlen)
  have hQbetween : Between Q A B ↔ Between Q' C D :=
    BookI.Prop20.between_congr
      (by rw [len_symm Q B, len_symm Q' D]; exact hQ₂.symm)
      (by rw [len_symm Q A, len_symm Q' C]; exact hQ₁.symm)
      (by rw [len_symm B A, len_symm D C]; exact hlen)
  have hbetween : Between P A Q ↔ Between P' C Q' := by
    rw [dist_on_on.opposite hAB hP hQ hPA hQA,
      dist_on_on.opposite hCD hP' hQ' hCP'.symm hCQ'.symm, ← hPbetween, ← hQbetween]
  by_cases hPAQ : Between P A Q
  · /- On opposite rays, the distance is the sum of the distances from the start. -/
    calc
      ‖P' Q'‖ = ‖P' C‖ + ‖C Q'‖ := (len_add_of_between (hbetween.mp hPAQ)).symm
      _ = ‖P A‖ + ‖A Q‖ := by rw [len_symm P' C, hP₁, hQ₁, len_symm A P]
      _ = ‖P Q‖ := len_add_of_between hPAQ
  · /- Otherwise the two points lie on one ray, in both figures. -/
    have hPQ : Collinear A Q P := by
      obtain ⟨L, hAL, hBL, hPL⟩ := hP
      obtain ⟨M, hAM, hBM, hQM⟩ := hQ
      exact ⟨L, hAL, line_unique hAB hAM hBM hAL hBL ▸ hQM, hPL⟩
    have hP'Q' : Collinear C Q' P' := by
      obtain ⟨L, hCL, hDL, hP'L⟩ := hP'
      obtain ⟨M, hCM, hDM, hQ'M⟩ := hQ'
      exact ⟨L, hCL, line_unique hCD hCM hDM hCL hDL ▸ hQ'M, hP'L⟩
    have hPray : OnRay P A Q := ⟨Ne.symm hQA, hPA, hPQ, hPAQ⟩
    have hP'ray : OnRay P' C Q' :=
      ⟨hCQ', hCP'.symm, hP'Q', fun h => hPAQ (hbetween.mpr h)⟩
    rcases lt_trichotomy ‖A P‖ ‖A Q‖ with hlt | heq | hgt
    · /- P is nearer the start. Subtract the equal first parts from the wholes. -/
      have hAPQ : Between A P Q := hPray.between_of_len_lt (OnRay.self (Ne.symm hQA)) hlt
      have hCP'Q' : Between C P' Q' := hP'ray.between_of_len_lt (OnRay.self hCQ')
        (by rw [hP₁, hQ₁]; exact hlt)
      apply CommonNotion3 (c := ‖C P'‖) (d := ‖A P‖) _ hP₁
      calc
        ‖P' Q'‖ + ‖C P'‖ = ‖C Q'‖ := by rw [add_comm, len_add_of_between hCP'Q']
        _ = ‖A Q‖ := hQ₁
        _ = ‖P Q‖ + ‖A P‖ := by rw [add_comm, len_add_of_between hAPQ]
    · /- Equal distances on one ray give coincident points in both figures. -/
      have hPQeq : P = Q := hPray.eq_of_len_eq heq
      have hP'Q'eq : P' = Q' := hP'ray.eq_of_len_eq (by rw [hP₁, hQ₁, heq])
      rw [hPQeq, hP'Q'eq, len_self, len_self]
    · /- Q is nearer the start. Subtract AQ and CQ' instead. -/
      have hAQP : Between A Q P := hPray.symm.between_of_len_lt
        (OnRay.self (Ne.symm hPA)) hgt
      have hCQ'P' : Between C Q' P' := hP'ray.symm.between_of_len_lt (OnRay.self hCP')
        (by rw [hP₁, hQ₁]; exact hgt)
      have hremainder : ‖Q' P'‖ = ‖Q P‖ := by
        apply CommonNotion3 (c := ‖C Q'‖) (d := ‖A Q‖) _ hQ₁
        calc
          ‖Q' P'‖ + ‖C Q'‖ = ‖C P'‖ := by rw [add_comm, len_add_of_between hCQ'P']
          _ = ‖A P‖ := hP₁
          _ = ‖Q P‖ + ‖A Q‖ := by rw [add_comm, len_add_of_between hAQP]
      simpa only [len_symm Q' P', len_symm Q P] using hremainder

end Elements.BookIII
