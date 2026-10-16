import Elements.Figure.Basics
import Elements.BookI.Prop04
import Elements.BookI.Prop13
import Elements.BookI.Prop14
import Elements.BookI.Prop41
import Elements.BookI.Prop46

/-!
# Book I, Proposition 47

Euclid's text, in Heath's translation: [`heath/I/47.md`](../../heath/I/47.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Before the proposition, `Prop47.within` says where the squares fall: a fact of
Euclid's figure that the proof needs three times.
-/

namespace Elements.BookI

open Tacit

/-- Where the squares fall. If the angle `ABC` is less than a right angle, and `BD`
stands at right angles to `BC` on the other side of it from `A`, then `C` lies within
the angle `ABD`: on `A`'s side of `BD`, and on `D`'s side of `BA`. Euclid reads this
off his figure when he adds the angle `ABC` to the right angles `DBC`, `FBA`, and
again when he takes the parallelograms `BL`, `CL` to make up the square `BDEC`.

The straight line `AD` crosses `BC`, since it joins points on either side of it. Not
at `B`, for then the angles `ABC`, `CBD` would make two right angles [I. 13], and
`CBD` alone is right. Not beyond `B` from `C`, for then the angle `ABD` would be
greater than two right angles: the angle on the far side of `AB` from `C` is
greater than right [I. 13], and to it is added the right angle on the far side of
`BD`. So it crosses on the ray from `B` through `C`, and `C` lies where the crossing
point does. [I. 13] -/
theorem Prop47.within {A B C D : Point} (hABC : Triangle A B C) (hD : OppositeSidesOf D A B C)
    (hCBD : ∠ C B D = ∟) (hacute : ∠ A B C < ∟) :
    SameSideOf C A B D ∧ SameSideOf C D B A := by
  obtain ⟨BC, hB_BC, hC_BC⟩ := Postulate1 B C hABC.ne₂₃
  have hop : OppositeSides A D BC := hD.symm.oppositeSides hB_BC hC_BC
  have hA_BC : ¬ OnLine A BC := hop.1
  have hD_BC : ¬ OnLine D BC := hop.2.1
  /- `AD` crosses `BC` at a point `Y`. -/
  obtain ⟨Y, hY_BC, hAYD⟩ := OppositeSides.exists_between hop
  obtain ⟨AD, hA_AD, hD_AD⟩ := Postulate1 A D (ne_of_between_ends hAYD)
  have hY_AD : OnLine Y AD := on_line_of_between_ends hAYD hA_AD hD_AD
  have hBD : B ≠ D := fun e => hD_BC (e ▸ hB_BC)
  have hBA : B ≠ A := fun e => hA_BC (e ▸ hB_BC)
  obtain ⟨BD, hB_BD, hD_BD⟩ := Postulate1 B D hBD
  obtain ⟨BA, hB_BA, hA_BA⟩ := Postulate1 B A hBA
  by_cases hYB : Y = B
  · /- Not at `B`: the angles `ABC`, `CBD` would make two right angles. [I. 13] -/
    exfalso
    rw [hYB] at hAYD hY_AD
    have hC : ¬ Collinear A D C := fun ⟨K, hA_K, hD_K, hC_K⟩ => by
      have hK : K = AD := line_unique (ne_of_between_ends hAYD) hA_K hD_K hA_AD hD_AD
      rw [hK] at hC_K
      exact hA_BC ((line_unique hABC.ne₂₃ hY_AD hC_K hB_BC hC_BC) ▸ hA_AD)
    have h13 := Prop13 hAYD hC
    rw [hCBD] at h13
    exact Magnitude.ne_of_lt (add_lt_add_right ∟ hacute) h13
  · have hB_AD : ¬ OnLine B AD := fun hB =>
      hA_BC ((line_unique hYB hY_AD hB hY_BC hB_BC) ▸ hA_AD)
    have hY_BD : ¬ OnLine Y BD := fun hY =>
      hD_BC ((line_unique hYB hY hB_BD hY_BC hB_BC) ▸ hD_BD)
    have hY_BA : ¬ OnLine Y BA := fun hY =>
      hA_BC ((line_unique hYB hY hB_BA hY_BC hB_BC) ▸ hA_BA)
    by_cases hYBC : Between Y B C
    · /- Not beyond `B`: the angle `ABD` would be greater than two right angles. -/
      exfalso
      have hADB : Triangle A D B := fun ⟨K, hA_K, hD_K, hB_K⟩ =>
        hB_AD ((line_unique (ne_of_between_ends hAYD) hA_K hD_K hA_AD hD_AD) ▸ hB_K)
      have hsum : ∠ A B D = ∠ A B Y + ∠ Y B D := angle_add_of_between hADB hAYD
      have hYCA : ¬ Collinear Y C A := fun ⟨K, hY_K, hC_K, hA_K⟩ =>
        hA_BC ((line_unique (ne_of_between_ends hYBC) hY_K hC_K hY_BC hC_BC) ▸ hA_K)
      have hYCD : ¬ Collinear Y C D := fun ⟨K, hY_K, hC_K, hD_K⟩ =>
        hD_BC ((line_unique (ne_of_between_ends hYBC) hY_K hC_K hY_BC hC_BC) ▸ hD_K)
      have h₁ : ∠ Y B A + ∠ A B C = ∟ + ∟ := Prop13 hYBC hYCA
      have h₂ : ∠ Y B D + ∠ D B C = ∟ + ∟ := Prop13 hYBC hYCD
      rw [(angle_symm hBD.symm hABC.ne₂₃.symm).trans hCBD] at h₂
      have hYBD : ∠ Y B D = ∟ := by
        rcases lt_trichotomy (∠ Y B D) ∟ with h | h | h
        · exact absurd h₂ (Magnitude.ne_of_lt (add_lt_add_right ∟ h))
        · exact h
        · exact absurd h₂.symm (Magnitude.ne_of_lt (add_lt_add_right ∟ h))
      have hgt : ∟ < ∠ A B Y := by
        have h₃ : ∠ A B C + ∠ Y B A < ∟ + ∠ Y B A := add_lt_add_right _ hacute
        rw [add_comm (∠ A B C), add_comm ∟, h₁] at h₃
        rw [angle_symm hBA.symm (ne_of_between hYBC)]
        exact Magnitude.lt_of_add_lt_add_right h₃
      have h₄ : ∟ + ∟ < ∠ A B D := by
        rw [hsum, hYBD]
        exact add_lt_add_right ∟ hgt
      exact angle_le_two_right A B D h₄
    · /- So `Y` lies on the ray from `B` through `C`, and within the angle `ABD`. -/
      have hray : OnRay C B Y := OnRay.symm ⟨hABC.ne₂₃, hYB, ⟨BC, hB_BC, hC_BC, hY_BC⟩, hYBC⟩
      have h₁ : SameSideOf Y A B D :=
        SameSideOf.of_line hBD hB_BD hD_BD (pasch2 (between_symm hAYD) hD_BD hY_BD)
      have h₂ : SameSideOf Y D B A :=
        SameSideOf.of_line hBA hB_BA hA_BA (pasch2 hAYD hA_BA hY_BA)
      exact ⟨SameSideOf.of_onRay hray h₁, SameSideOf.of_onRay hray h₂⟩

/-- In right-angled triangles the square on the side subtending the right angle is equal to the
squares on the sides containing the right angle. -/
theorem Prop47 {A B C D E F G H K : Point} (hABC : Triangle A B C) (hright : ∠ B A C = ∟)
    (hBDEC : Square B D E C) (hD : OppositeSidesOf D A B C) (hE : OppositeSidesOf E A B C)
    (hABFG : Square A B F G) (hF : OppositeSidesOf F C A B) (hG : OppositeSidesOf G C A B)
    (hACKH : Square A C K H) (hK : OppositeSidesOf K B A C) (hH : OppositeSidesOf H B A C) :
    quadArea B D E C = quadArea A B F G + quadArea A C K H := by
  -- Let ABC be a right-angled triangle having the angle BAC right;
  -- I say that the square on BC is equal to the squares on BA, AC.
  -- For let there be described on BC the square BDEC, and on BA, AC the squares GB,
  -- HC; [I. 46] through A let AL be drawn parallel to either BD or CE, and let AD, FC be
  -- joined.
  -- Then, since each of the angles BAC, BAG is right, it follows that with a straight line BA,
  -- and at the point A on it, the two straight lines AC, AG not lying on the same side make
  -- the adjacent angles equal to two right angles; therefore CA is in a straight line with
  -- AG. [I. 14]
  -- For the same reason BA is also in a straight line with AH.
  -- And, since the angle DBC is equal to the angle FBA: for each is right: let the angle ABC
  -- be added to each; therefore the whole angle DBA is equal to the whole angle FBC. [C.N. 2]
  -- And, since DB is equal to BC, and FB to BA, the two sides AB, BD are equal to the two
  -- sides FB, BC respectively; and the angle ABD is equal to the angle FBC; therefore the base
  -- AD is equal to the base FC, and the triangle ABD is equal to the triangle FBC. [I. 4]
  -- Now the parallelogram BL is double of the triangle ABD, for they have the same base BD and
  -- are in the same parallels BD, AL. [I. 41]
  -- And the square GB is double of the triangle FBC, for they again have the same base FB and
  -- are in the same parallels FB, GC. [I. 41]
  -- [But the doubles of equals are equal to one another.]
  -- Therefore the parallelogram BL is also equal to the square GB.
  -- Similarly, if AE, BK be joined, the parallelogram CL can also be proved equal to the
  -- square HC; therefore the whole square BDEC is equal to the two squares GB, HC. [C.N. 2]
  -- And the square BDEC is described on BC, and the squares GB, HC on BA, AC.
  -- Therefore the square on the side BC is equal to the squares on the sides BA, AC.
  -- Therefore etc.
  -- Q. E. D.
  sorry

end Elements.BookI
