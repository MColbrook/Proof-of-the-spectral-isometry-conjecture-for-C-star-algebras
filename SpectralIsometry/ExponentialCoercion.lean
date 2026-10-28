module
public import SpectralIsometry.UniversalExpZero

/-!
# Exponential Coercion

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.EntireAssembly
open BidualFoundation UniversalWeakClosure OperatorExtension
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] predualNormedGroup predualNormedSpace
variable {A : Type*} [CStarAlgebra A]

theorem expOperatorEquiv_toCLM (δ : A →L[ℂ] A) (z : ℂ) :
    (expOperatorEquiv δ z).toContinuousLinearMap=
      (NormedSpace.exp (z • δ) : A →L[ℂ] A) := rfl

theorem lift_exp_zero (δ : A →L[ℂ] A) :
    lift (NormedSpace.exp ((0:ℂ) • δ) : A →L[ℂ] A)=
      ContinuousLinearMap.id ℂ (algebra A) := by
  apply ContinuousLinearMap.ext
  intro a
  exact lift_exp_zero_apply_fast δ a

end SpectralIsometry.EntireAssembly

