module

public import SpectralIsometry.BidualRestrictionNorm

/-!
# Bidual Restriction Equiv

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.UniversalWeakClosure

open Filter Topology
open scoped InnerProductSpace
open OAI.BoundedHochschild.KadisonRingrose

universe u
variable (A : Type u) [CStarAlgebra A]

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] predualNormedGroup predualNormedSpace

def restrictionLinearIsometry (hDense : ContractionStrongDense A) :
    predual A →ₗᵢ[ℂ] StrongDual ℂ A where
  toFun := restriction A
  map_add' := restriction_add A
  map_smul' := by intro z Φ; exact restriction_smul A z Φ
  norm_map' := restriction_norm_eq_of_density A hDense

def restrictionEquiv (hDense : ContractionStrongDense A) :
    predual A ≃ₗᵢ[ℂ] StrongDual ℂ A :=
  LinearIsometryEquiv.ofSurjective (restrictionLinearIsometry A hDense)
    (restriction_surjective A)

end SpectralIsometry.BidualFoundation.UniversalWeakClosure

