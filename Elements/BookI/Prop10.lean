import Elements.Figure.Basics
import Elements.BookI.Prop01
import Elements.BookI.Prop04
import Elements.BookI.Prop09

/-!
# Book I, Proposition 10

Euclid's text, in Heath's translation: [`heath/I/10.md`](../../heath/I/10.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid never says why the bisector `CD` meets `AB` between `A` and `B`. I.9 says
that it falls within the angle `ACB`, and `crossbar` (Book Zero) does the rest.
-/

namespace Elements.BookI

open Tacit

/-- To bisect a given finite straight line. -/
theorem Prop10 {A B : Point} (hAB : A ≠ B) :
    ∃ D : Point, Between A D B ∧ ‖A D‖ = ‖D B‖ := by
  -- Let AB be the given finite straight line.
  /- Lean needs the straight line itself, by name, to say later that `D` is on
     it and `C` is off it. -/
  obtain ⟨L, hA_L, hB_L⟩ := Postulate1 A B hAB
  -- Thus it is required to bisect the finite straight line AB.
  -- Let the equilateral triangle ABC be constructed on it, [I. 1]
  /- No side of `AB` matters here, so I.1 is given a point of `AB` itself, `A`,
     as the point whose side the triangle is to be on. -/
  obtain ⟨C, ⟨hABC, hAB_BC, hBC_CA⟩, -⟩ := Prop1 A B hAB A
  have hC_L : ¬ OnLine C L := hABC.off_line hA_L hB_L
  -- and let the angle ACB be bisected by the straight line CD; [I. 9]
  /- I.9 bisects the angle `ACB` by a straight line `CF`, with `F` within the
     angle: on `B`'s side of `CA` and on `A`'s side of `CB`. Euclid's `D` is the
     point where that straight line meets `AB`. He draws it there without a
     word; it is the crossbar (Book Zero, `crossbar`) that makes the bisector,
     falling within the angle, cross the base between `A` and `B`. -/
  obtain ⟨F, hF_CA, hF_CB, hACF_FCB, -⟩ := Prop9 hABC.acb
  obtain ⟨D, hADB, hD_CF⟩ := crossbar hF_CA hF_CB
  have hD_L : OnLine D L := on_line_of_between_ends hADB hA_L hB_L
  have hDC : D ≠ C := hD_CF.2.1
  -- I say that the straight line AB has been bisected at the point D.
  -- For, since AC is equal to CB,
  have hAC_CB : ‖A C‖ = ‖C B‖ :=
    (len_symm A C).trans (hBC_CA.symm.trans (len_symm B C))
  -- and CD is common,
  have hCD : ‖C D‖ = ‖C D‖ := rfl
  -- the two sides AC, CD are equal to the two sides BC, CD respectively;
  have hCA_CB : ‖C A‖ = ‖C B‖ := (len_symm C A).trans hAC_CB
  -- and the angle ACD is equal to the angle BCD;
  /- The angles ACD and BCD are the halves ACF and FCB that I.9 made equal,
     since `D` is on the ray from `C` through `F` (`angle_onRay_right`,
     `angle_onRay_left`); the second is then read the other way round. -/
  have hACD_BCD : ∠ A C D = ∠ B C D := by
    rw [angle_onRay_right hD_CF hABC.ne₁₃, hACF_FCB,
      ← angle_onRay_left hD_CF hABC.ne₂₃, angle_symm hDC hABC.ne₂₃]
  -- therefore the base AD is equal to the base BD. [I. 4]
  /- The two triangles are `CAD` and `CBD`: `D` is on `AB`, and `C` is off it. -/
  have hCAD : Triangle C A D := (Triangle.of_line hA_L hD_L (ne_of_between hADB) hC_L).cab
  have hCBD : Triangle C B D :=
    (Triangle.of_line hB_L hD_L (ne_of_between (between_symm hADB)) hC_L).cab
  have hAD_BD : ‖A D‖ = ‖B D‖ := (Prop4 hCAD hCBD hCA_CB hCD hACD_BCD).1
  -- Therefore the given finite straight line AB has been bisected at D.
  exact ⟨D, hADB, hAD_BD.trans (len_symm B D)⟩
  -- Q. E. F.

end Elements.BookI
