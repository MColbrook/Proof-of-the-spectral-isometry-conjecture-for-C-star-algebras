module

public import SpectralIsometry.SquareZeroCornerImages
public import SpectralIsometry.ProperInfiniteCopiesBridge

/-!
# Square Zero Proper Infinite Corner

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped ComplexOrder CStarAlgebra
open OAI.HochschildCorners OAI.HochschildComparison
open OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.SquareZeroPreserver

universe u v
variable {M X : Type u} {B : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] [CStarAlgebra B]

theorem anticommute_images_of_orthogonal_properlyInfinite_corners
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (R : M →L[ℂ] B) (hR : PreservesSquareZero R.toLinearMap)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) (hqp : q * p = 0)
    (hpp : ProperlyInfiniteProjection p) (hqq : ProperlyInfiniteProjection q)
    {a b : M} (ha : a ∈ corner p hp) (hb : b ∈ corner q hq) :
    R a * R b + R b * R a = 0 := by
  obtain ⟨r₁,s₁,hr₁,hs₁,hrs₁⟩ := exists_corner_isometries_of_properlyInfinite hp hpp
  obtain ⟨r₂,s₂,hr₂,hs₂,hrs₂⟩ := exists_corner_isometries_of_properlyInfinite hq hqq
  exact anticommute_images_of_orthogonal_corner_copies e R hR hp hq hpq hqp
    r₁ s₁ hr₁ hs₁ hrs₁ r₂ s₂ hr₂ hs₂ hrs₂ ha hb

end SpectralIsometry.SquareZeroPreserver

