module

public import SpectralIsometry.CommutingDyadicProjection
public import OAI.Analysis.BoundedHochschild.Corners

/-!
# Corner Commuting Dyadic

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open scoped ComplexOrder CStarAlgebra
open OAI.HochschildCorners

namespace SpectralIsometry.SquareZeroPreserver

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_commuting_corner_dyadic_projection
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {p a : M} (hp : IsStarProjection p)
    (ha : a ∈ corner p hp) (ha0 : 0 ≤ a) (ha1 : a ≤ p) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ Commute a q ∧
      0 ≤ (2 : ℝ) • a - q ∧ (2 : ℝ) • a - q ≤ p := by
  let aC : Corner p hp := ⟨a,ha⟩
  obtain ⟨q,hq,hcomm,h0,h1⟩ := exists_commuting_dyadic_projection
    (cornerPredualEquiv p hp e) aC (show 0 ≤ aC from ha0) (show aC ≤ 1 from ha1)
  refine ⟨(q : M),corner_projection_coe p hp hq,corner_projection_le p hp hq,?_,?_,?_⟩
  · exact congrArg Subtype.val hcomm.eq
  · exact h0
  · exact h1

end SpectralIsometry.SquareZeroPreserver

