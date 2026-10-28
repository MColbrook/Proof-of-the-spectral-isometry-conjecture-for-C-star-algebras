module

public import SpectralIsometry.Basic

/-!
# Jordan Spectral

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.JordanSpectral

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem linearEquiv_spectrum (R : A ≃ₗ[ℂ] B) (h1 : R 1 = 1)
    (hsquare : ∀ a : A, R (a^2) = (R a)^2) (a : A) :
    spectrum ℂ (R a) = spectrum ℂ a :=
  jordan_isomorphism_spectrum R.toLinearMap h1 ⟨R.bijective,hsquare⟩ a

end SpectralIsometry.JordanSpectral

