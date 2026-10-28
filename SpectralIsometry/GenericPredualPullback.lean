module

public import SpectralIsometry.BidualNormality

/-!
# Generic Predual Pullback

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.CoefficientPredual

attribute [local instance] complexNormedSpaceSelf dualNormedGroup dualNormedSpace
  coefficientNormedGroup coefficientNormedSpace

open OAI.HochschildNormalPart OAI.BoundedHochschild

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : VonNeumannAlgebra H)

def coefficientPullback (Φ : coefficientPredual M) (L : M →L[ℂ] M)
    (hL : HasPreadjoint (concretePredualIsometry M) L) : coefficientPredual M :=
  ⟨(Φ : StrongDual ℂ M).comp L, by
    have h := normalDual_comp (concretePredualIsometry M)
      (coefficientPredual_normal M Φ) L hL
    exact (le_of_eq (normalDual_eq_coefficientPredual M)) h⟩

theorem coefficientPullback_apply (Φ : coefficientPredual M) (L : M →L[ℂ] M)
    (hL : HasPreadjoint (concretePredualIsometry M) L) (m : M) :
    ((coefficientPullback M Φ L hL : coefficientPredual M) : StrongDual ℂ M) m =
      (Φ : StrongDual ℂ M) (L m) := rfl

def leftMulPullback (Φ : coefficientPredual M) (m : M) : coefficientPredual M :=
  coefficientPullback M Φ (ContinuousLinearMap.mul ℂ M m)
    ((OAI.HochschildSakai.abstract_multiplication_normal (concretePredualIsometry M)).1 m)

def rightMulPullback (Φ : coefficientPredual M) (m : M) : coefficientPredual M :=
  coefficientPullback M Φ ((ContinuousLinearMap.mul ℂ M).flip m)
    ((OAI.HochschildSakai.abstract_multiplication_normal (concretePredualIsometry M)).2 m)

theorem leftMulPullback_apply (Φ : coefficientPredual M) (m n : M) :
    ((leftMulPullback M Φ m : coefficientPredual M) : StrongDual ℂ M) n =
      (Φ : StrongDual ℂ M) (m * n) := rfl

theorem rightMulPullback_apply (Φ : coefficientPredual M) (m n : M) :
    ((rightMulPullback M Φ m : coefficientPredual M) : StrongDual ℂ M) n =
      (Φ : StrongDual ℂ M) (n * m) := rfl

end SpectralIsometry.BidualFoundation.CoefficientPredual

