module

public import SpectralIsometry.MainTheorems
public import SpectralIsometry.SupportFunctionLimit
public import SpectralIsometry.SquareZeroContour
public import SpectralIsometry.NormalSeminorm
public import SpectralIsometry.InvertiblePolarDistance
public import SpectralIsometry.InverseOrderBounds
public import SpectralIsometry.InnerSimilarityExample
public import SpectralIsometry.NilpotentSupportIdentification
public import SpectralIsometry.FiniteQuotientInverse
public import SpectralIsometry.NormalSeminormStructure
public import SpectralIsometry.NormalSeminormTopology
public import SpectralIsometry.CenterValuedTraceConcrete
public import SpectralIsometry.SupportingTheorems

/-!
# Solution

Proofs of the principal statements recorded in Challenge.lean.
-/

@[expose] public section
noncomputable section
namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem main_result (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (h1 : T 1 = 1) (hr : PreservesRadius T) : IsJordanIsomorphism T := by
  exact PrincipalVerification.main_result T honto h1 hr

theorem entire_group (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1 = 1)
    (hr : ∀ (z : ℂ) (a : A),
      spectralRadius ℂ ((NormedSpace.exp (z • δ) : A →L[ℂ] A) a) = spectralRadius ℂ a) :
    (∀ a b : A, δ (a * b) = δ a * b + a * δ b) ∧
      ∀ z : ℂ, Function.Bijective
        ((NormedSpace.exp (z • δ) : A →L[ℂ] A) : A → A) ∧
        ∀ a b : A, (NormedSpace.exp (z • δ) : A →L[ℂ] A) (a * b) =
          (NormedSpace.exp (z • δ) : A →L[ℂ] A) a *
            (NormedSpace.exp (z • δ) : A →L[ℂ] A) b := by
  exact PrincipalVerification.entire_group δ h1 hr

theorem normalization (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) :
    T 1 ∈ unitary B ∧ (∀ b : B, T 1 * b = b * T 1) ∧
      ∃ J : A →ₗ[ℂ] B, J 1 = 1 ∧ IsJordanIsomorphism J ∧
        ∀ a : A, T a = T 1 * J a := by
  exact PrincipalVerification.normalization T honto hr

end SpectralIsometry
