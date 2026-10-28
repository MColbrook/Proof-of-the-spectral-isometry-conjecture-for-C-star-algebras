module
public import SpectralIsometry.UniversalOffDiagonalResult
public import SpectralIsometry.SquareFamilyAssembly
public import SpectralIsometry.CentralSplitFamilyAssembly

/-!
# Entire Group

Derivations and automorphisms from entire groups of spectral isometries.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open OAI.HochschildCorners OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.EntireAssembly
open BidualFoundation UniversalWeakClosure CoefficientPredual OperatorExtension
open FiniteQuotientAssembly CornerFamilyHolomorphic
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA predualNormedGroup predualNormedSpace
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder
variable {A : Type*} [CStarAlgebra A]
local instance (priority := 3000) highLimitModelOrder : PartialOrder (algebra A) :=
  CStarAlgebra.spectralOrder (algebra A)
local instance (priority := 3000) highLimitModelLE : LE (algebra A) :=
  (highLimitModelOrder (A:=A)).toLE
local instance (priority := 3000) highLimitModelStarOrder : StarOrderedRing (algebra A) :=
  CStarAlgebra.spectralOrderedRing (algebra A)
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

theorem universal_entire_family (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) :
    SquareFamilyAssembly.SquaresFamily
      (fun z => lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) := by
  exact SquareFamilyAssembly.of_central_split (M:=algebra A) (X:=predual A)
    (concretePredualIsometry (algebra A))
    (fun z => lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))
    (fun p q hp hq hpc hqc hsum hproper hfinite =>
      SquareFamilyAssembly.central_family_squares p q hp hq hpc hqc hsum
        (fun z => lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))
        (universal_compression_kernel_invariant q hq hqc hfinite δ hRad)
        (universal_complement_result p q hp hq hpc hqc hsum hproper hfinite δ h1 hRad)
        (universal_crossBlock_eq_zero p q hp hq hpc hqc hsum hproper hfinite δ h1 hRad)
        (universal_finiteBlock_jordan q hq hqc hfinite δ hRad))

theorem entire_group (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hr : ∀ (z : ℂ) (a : A),
      spectralRadius ℂ ((NormedSpace.exp (z • δ) : A →L[ℂ] A) a)=spectralRadius ℂ a) :
    (∀ a b : A, δ (a*b)=δ a*b+a*δ b) ∧
      ∀ z : ℂ, Function.Bijective
        ((NormedSpace.exp (z • δ) : A →L[ℂ] A) : A → A) ∧
        ∀ a b : A, (NormedSpace.exp (z • δ) : A →L[ℂ] A) (a*b)=
          (NormedSpace.exp (z • δ) : A →L[ℂ] A) a*
            (NormedSpace.exp (z • δ) : A →L[ℂ] A) b := by
  have hsq := SquareFamilyAssembly.faithful_algHom_descent
    (inclusion A).toAlgHom (inclusion_injective A)
    (fun z => (NormedSpace.exp (z • δ) : A →L[ℂ] A))
    (fun z => lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))
    (universal_entire_family δ h1 hr)
    (fun z a => lift_inclusion (NormedSpace.exp (z • δ) : A →L[ℂ] A) a)
  have hd := SquareFamilyAssembly.exp_derivation_of_squaresFamily δ hsq
  exact ⟨hd,exp_derivation_automorphism δ hd⟩

end SpectralIsometry.EntireAssembly

