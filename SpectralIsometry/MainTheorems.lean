module

public import SpectralIsometry.EntireGroup
public import SpectralIsometry.MainReductionSquares
public import SpectralIsometry.NormalizationUnitary

/-!
# Main Theorems

The main Jordan-isomorphism theorem, entire-group proposition and normalization corollary.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.PrincipalVerification

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem main_result (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (h1 : T 1=1) (hr : PreservesRadius T) : IsJordanIsomorphism T := by
  apply MainReduction.jordan_reduction_of_all_transported_leibniz T honto hr h1
  let U := MainReduction.radiusEquiv T honto hr
  have hU1 : U 1=1 := h1
  have hUr : PreservesRadius U.toLinearEquiv.toLinearMap := hr
  intro x a b
  exact (EntireAssembly.entire_group (TransportExp.transportedCLM U x)
    (TransportExp.exp_transportedCLM_one U hU1 x)
    (TransportExp.exp_transportedCLM_radius U hUr x)).1 a b

theorem entire_group (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hr : ∀ (z : ℂ) (a : A),
      spectralRadius ℂ ((NormedSpace.exp (z • δ) : A →L[ℂ] A) a)=spectralRadius ℂ a) :
    (∀ a b : A, δ (a*b)=δ a*b+a*δ b) ∧
      ∀ z : ℂ, Function.Bijective
        ((NormedSpace.exp (z • δ) : A →L[ℂ] A) : A → A) ∧
        ∀ a b : A, (NormedSpace.exp (z • δ) : A →L[ℂ] A) (a*b)=
          (NormedSpace.exp (z • δ) : A →L[ℂ] A) a*
            (NormedSpace.exp (z • δ) : A →L[ℂ] A) b :=
  EntireAssembly.entire_group δ h1 hr

theorem normalization (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) :
    T 1 ∈ unitary B ∧ (∀ b : B, T 1*b=b*T 1) ∧
      ∃ J : A →ₗ[ℂ] B, J 1=1 ∧ IsJordanIsomorphism J ∧
        ∀ a : A, T a=T 1*J a := by
  obtain ⟨u,J,hcen,hu,hJ1,hJon,hJr,hfac⟩ :=
    Normalization.exists_unital_radius_normalization T honto hr
  have hT1 : T 1=u := by simpa only [hJ1,mul_one] using hfac 1
  refine ⟨?_,?_,J,hJ1,main_result J hJon hJ1 hJr,?_⟩
  · rw [hT1]
    exact hu
  · intro b
    rw [hT1]
    exact hcen b
  · intro a
    rw [hT1]
    exact hfac a

end SpectralIsometry.PrincipalVerification

