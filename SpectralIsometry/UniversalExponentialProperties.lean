module
public import SpectralIsometry.ExponentialCoercion
public import SpectralIsometry.UniversalRealSpectrumExtension

/-!
# Universal Exponential Properties

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.EntireAssembly
open BidualFoundation UniversalWeakClosure OperatorExtension
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA predualNormedGroup predualNormedSpace
attribute [local instance 2000] complexOrder complexStarOrder
variable {A : Type*} [CStarAlgebra A]
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

theorem lift_exp_squareZero (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z : ℂ) (n : algebra A) (hn : n^2=0) :
    (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) n)^2=0 := by
  have hv := UniversalSquareZeroExtension.spectral_lift_preserves_squareZero
    (expOperatorEquiv δ z) (hRad z) (h1 z) n hn
  rw [expOperatorEquiv_toCLM] at hv
  exact hv

theorem lift_exp_real_spectrum (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z : ℂ) (a : algebra A) (ha : IsSelfAdjoint a) :
    ∀ ζ∈spectrum ℂ (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) a), ζ.im=0 := by
  have hv := UniversalRealSpectrumExtension.lift_selfadjoint_real_spectrum
    (expOperatorEquiv δ z) (hRad z) (h1 z) a ha
  rw [expOperatorEquiv_toCLM] at hv
  exact hv

end SpectralIsometry.EntireAssembly

