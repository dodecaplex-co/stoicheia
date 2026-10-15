import Elements.Figure.Basics
import Elements.BookI.Prop03

/-!
# Book I, Proposition 22

Euclid's text, in Heath's translation: [`heath/I/22.md`](../../heath/I/22.md).
Below, each of Euclid's sentences is a `--` comment, followed by the Lean that
carries it out.

Euclid names the three given straight lines by single letters, A, B, C. In Lean
they are the finite straight lines `A₁A₂`, `B₁B₂`, `C₁C₂`.

The statement says more than Euclid's, so that I.23 can use it as Euclid does:
the triangle `KFG` is put in a given place. Its corner `F` is a given point,
its side `FG` lies along the given ray from `F` through `E`, and `K` falls on the
side of `FE` where the given point `P` is. Euclid's straight line `DE` is then
set out through `F`, with `D` behind `F` and `DF` equal to A, and from there his
proof goes through as he writes it.
-/

namespace Elements.BookI

open Tacit

/-- Out of three straight lines, which are equal to three given straight lines, to construct a
triangle: thus it is necessary that two of the straight lines taken together in any manner
should be greater than the remaining one. [I. 20] -/
theorem Prop22 {A₁ A₂ B₁ B₂ C₁ C₂ E F P : Point}
    (hAB : ‖C₁ C₂‖ < ‖A₁ A₂‖ + ‖B₁ B₂‖) (hAC : ‖B₁ B₂‖ < ‖A₁ A₂‖ + ‖C₁ C₂‖)
    (hBC : ‖A₁ A₂‖ < ‖B₁ B₂‖ + ‖C₁ C₂‖) (hFE : F ≠ E) (hP : ¬ Collinear F E P) :
    ∃ G K : Point, OnRay G F E ∧ SameSideOf K P F E ∧
      ‖K F‖ = ‖A₁ A₂‖ ∧ ‖F G‖ = ‖B₁ B₂‖ ∧ ‖G K‖ = ‖C₁ C₂‖ := by
  -- Let the three given straight lines be A, B, C, and of these let two taken together in any
  -- manner be greater than the remaining one,
  -- namely A, B greater than C,
  -- A, C greater than B,
  -- and B, C greater than A;
  -- thus it is required to construct a triangle out of straight lines equal to A, B, C.
  -- Let there be set out a straight line DE, terminated at D but of infinite length in the
  -- direction of E,
  -- and let DF be made equal to A, FG equal to B, and GH equal to C. [I. 3]
  -- With centre F and distance FD let the circle DKL be described;
  -- again, with centre G and distance GH let the circle KLH be described;
  -- and let KF, KG be joined;
  -- I say that the triangle KFG has been constructed out of three straight lines equal to A,
  -- B, C.
  -- For, since the point F is the centre of the circle DKL,
  -- FD is equal to FK.
  -- But FD is equal to A;
  -- therefore KF is also equal to A.
  -- Again, since the point G is the centre of the circle LKH,
  -- GH is equal to GK.
  -- But GH is equal to C;
  -- therefore KG is also equal to C.
  -- And FG is also equal to B;
  -- therefore the three straight lines KF, FG, GK are equal to the three straight lines A, B,
  -- C.
  -- Therefore out of the three straight lines KF, FG, GK, which are equal to the three given
  -- straight lines A, B, C, the triangle KFG has been constructed.
  -- Q. E. F.
  sorry

end Elements.BookI
