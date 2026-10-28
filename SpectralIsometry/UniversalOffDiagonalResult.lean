module
public import SpectralIsometry.UniversalProperCornerResult
public import SpectralIsometry.GenericCentralOffDiagonal

/-!
# Universal Off Diagonal Result

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Filter Topology
open OAI.HochschildCorners OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.EntireAssembly

open BidualFoundation UniversalWeakClosure CoefficientPredual OperatorExtension
open FiniteQuotientAssembly CornerFamilyHolomorphic
open StrongStarApproximation

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf predualNormedGroup predualNormedSpace
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder

universe u
variable {A : Type u} [CStarAlgebra A]

local instance (priority := 3000) offdiagResultModelOrder : PartialOrder (algebra A) :=
  CStarAlgebra.spectralOrder (algebra A)
local instance (priority := 3000) offdiagResultModelLE : LE (algebra A) :=
  (offdiagResultModelOrder (A:=A)).toLE
local instance (priority := 3000) offdiagResultModelStarOrder : StarOrderedRing (algebra A) :=
  CStarAlgebra.spectralOrderedRing (algebra A)

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

/-- The finite-to-properly-infinite block vanishes for every parameter.
Real spectra are transported by the actual unital central compression hom. -/
theorem universal_crossBlock_eq_zero
    (p q : algebra A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : algebra A, p*a=a*p) (hqc : ∀ a : algebra A, q*a=a*q)
    (hsum : p+q=1) (hproper : ProperlyInfiniteProjection p)
    (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) :
    ∀ z : ℂ, crossBlockCLM p hp hpc q hq
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))=0 := by
  exact GenericCentralOffDiagonal.family_zero p q hp hq hpc hqc hsum
    (fun z => lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))
    (universalComplementEquiv p q hp hq hpc hqc hsum hfinite δ hRad)
    (fun z a => rfl)
    (universal_complement_result p q hp hq hpc hqc hsum hproper hfinite δ h1 hRad)
    (universal_complementBlock_inverse p q hp hq hpc hqc hsum hfinite δ hRad)
    (universal_complementBlock_operator_differentiable p hp hpc δ)
    (universal_crossBlock_operator_differentiable p hp hpc q hq δ)
    (lift_exp_real_spectrum δ h1 hRad)
    (lift_exp_zero_apply_fast δ)

end SpectralIsometry.EntireAssembly

