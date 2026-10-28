module

public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Spectral isometries of unital C*-algebras

The main theorem concerns arbitrary complex unital C*-algebras and ordinary
surjective complex-linear maps preserving the unit and every spectral radius.
It concludes bijectivity and preservation of squares, without an assumption
that the map is bounded or preserves adjoints.

The entire-group proposition proves the associative Leibniz identity for a
bounded generator whose exponentials are unital spectral isometries at every
complex parameter. The normalization corollary treats maps that need not
preserve the unit, with the prescribed central unitary factor T(1).

These are independent statements for comparison against Solution.lean.
-/

@[expose] public section
noncomputable section
namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Pointwise preservation of the spectral radius by a complex-linear map. -/
def PreservesRadius (T : A →ₗ[ℂ] B) : Prop :=
  ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a

/-- An algebraic Jordan isomorphism: a complex-linear bijection preserving squares. -/
def IsJordanIsomorphism (T : A →ₗ[ℂ] B) : Prop :=
  Function.Bijective T ∧ ∀ a : A, T (a ^ 2) = (T a) ^ 2

/-- A unital surjective spectral isometry is an algebraic Jordan isomorphism. -/
theorem main_result (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (h1 : T 1 = 1) (hr : PreservesRadius T) : IsJordanIsomorphism T := by
  sorry

/-- An entire spectral-isometric exponential group has a derivation as generator. -/
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
  sorry

/-- A surjective spectral isometry is T(1) times a unital Jordan isomorphism. -/
theorem normalization (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) :
    T 1 ∈ unitary B ∧ (∀ b : B, T 1 * b = b * T 1) ∧
      ∃ J : A →ₗ[ℂ] B, J 1 = 1 ∧ IsJordanIsomorphism J ∧
        ∀ a : A, T a = T 1 * J a := by
  sorry

end SpectralIsometry
