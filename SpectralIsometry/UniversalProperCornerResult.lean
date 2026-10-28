module
public import SpectralIsometry.UniversalProperCornerFacts
public import SpectralIsometry.GenericWeightedFamilyResult
public import SpectralIsometry.GenericProperWeightedFamily
public import SpectralIsometry.CornerFamilyHolomorphic

/-!
# Universal Proper Corner Result

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

local instance (priority := 3000) properResultModelOrder : PartialOrder (algebra A) :=
  CStarAlgebra.spectralOrder (algebra A)
local instance (priority := 3000) properResultModelLE : LE (algebra A) :=
  (properResultModelOrder (A:=A)).toLE
local instance (priority := 3000) properResultModelStarOrder : StarOrderedRing (algebra A) :=
  CStarAlgebra.spectralOrderedRing (algebra A)

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

/-- The properly infinite restriction is unital and square preserving. Its
unitality is a conclusion of the central-weight proof, not an input. -/
theorem universal_complement_result
    (p q : algebra A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : algebra A, p*a=a*p) (hqc : ∀ a : algebra A, q*a=a*q)
    (hsum : p+q=1) (hproper : ProperlyInfiniteProjection p)
    (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) :
    WeightedFamilyResult.UnitalSquares (fun z : ℂ => centralBlockCLM p hp hpc
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))) := by
  exact WeightedFamilyResult.proper_corner_family_result (H:=Hilbert A)
    (algebra A) p hp hproper
    (fun z => centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)))
    (universal_complement_squareZero p q hp hq hpc hqc hsum hfinite δ h1 hRad)
    (universal_complement_surjective p q hp hq hpc hqc hsum hfinite δ hRad)
    (fun z a b _ ha => universal_complement_strongStar p q hp hq hpc hqc hsum hfinite δ hRad z a b ha)
    (universal_complementBlock_weight_differentiable p hp hpc δ)
    (universal_complement_weight_real p q hp hq hpc hqc hsum hfinite δ h1 hRad)
    (universal_complement_weight_zero p q hp hq hpc hqc hsum hfinite δ hRad)

end SpectralIsometry.EntireAssembly

