module

public import SpectralIsometry.SquareZeroPreserver
public import SpectralIsometry.SquareZeroCornerSpan

/-!
# Square Zero Corner Images

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped ComplexOrder CStarAlgebra
open OAI.HochschildCorners

namespace SpectralIsometry.SquareZeroPreserver

variable {M X B : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] [CStarAlgebra B]

def boundedJordanPair (R : M →L[ℂ] B) (b : M) : M →L[ℂ] B :=
  (((ContinuousLinearMap.mul ℂ B).flip (R b)) + ContinuousLinearMap.mul ℂ B (R b)).comp R

theorem anticommute_images_of_orthogonal_corner_copies
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (R : M →L[ℂ] B) (hR : PreservesSquareZero R.toLinearMap)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) (hqp : q * p = 0)
    (r₁ s₁ : Corner p hp) (hr₁ : star r₁ * r₁ = 1) (hs₁ : star s₁ * s₁ = 1)
    (hrs₁ : star r₁ * s₁ = 0)
    (r₂ s₂ : Corner q hq) (hr₂ : star r₂ * r₂ = 1) (hs₂ : star s₂ * s₂ = 1)
    (hrs₂ : star r₂ * s₂ = 0)
    {a b : M} (ha : a ∈ corner p hp) (hb : b ∈ corner q hq) :
    R a * R b + R b * R a = 0 := by
  have hnil (x : M) (hx : x ∈ supportedSquareZero p) : R x * R b + R b * R x = 0 := by
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro F
    rw [add_comm (R x * R b) (R b * R x)]
    apply dual_zero_on_corner_of_two_copies e hq r₂ s₂ hr₂ hs₂ hrs₂
      (F.comp (boundedJordanPair R x)) ?_ hb
    intro y hy
    change F (R y * R x + R x * R y) = 0
    rw [add_comm]
    have hz := anticommute_images_of_orthogonal_corners R.toLinearMap hR p q x y hpq hqp hx hy
    change R x * R y + R y * R x = 0 at hz
    rw [hz, map_zero]
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro F
  apply dual_zero_on_corner_of_two_copies e hp r₁ s₁ hr₁ hs₁ hrs₁
    (F.comp (boundedJordanPair R b)) ?_ ha
  intro x hx
  change F (R x * R b + R b * R x) = 0
  rw [hnil x hx, map_zero]

end SpectralIsometry.SquareZeroPreserver

