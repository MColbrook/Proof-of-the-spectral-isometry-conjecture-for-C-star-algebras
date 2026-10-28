module

public import SpectralIsometry.BidualExponentialGroup

/-!
# Universal Exp Zero

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

theorem lift_exp_zero_apply_fast (δ : A →L[ℂ] A) (a : algebra A) :
    lift (NormedSpace.exp ((0:ℂ) • δ) : A →L[ℂ] A) a=a := by
  have h := congrArg (fun T : algebra A →L[ℂ] algebra A => T a) (lift_exp_smul δ 0)
  simpa only [zero_smul ℂ (lift δ),NormedSpace.exp_zero,one_apply_eq_self] using h

end SpectralIsometry.EntireAssembly

