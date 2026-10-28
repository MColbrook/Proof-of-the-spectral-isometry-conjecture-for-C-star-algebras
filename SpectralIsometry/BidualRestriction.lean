module

public import SpectralIsometry.BidualDuality
public import SpectralIsometry.BidualNormality

/-!
# Bidual Restriction

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.UniversalWeakClosure

open Filter Topology
open scoped InnerProductSpace
open OAI.BoundedHochschild.KadisonRingrose

universe u
variable (A : Type u) [CStarAlgebra A]

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] predualNormedGroup predualNormedSpace

theorem canonicalPredualEquiv_symm_normal (φ : StrongDual ℂ A) :
    (((canonicalPredualEquiv A).symm φ : predual A) :
      StrongDual ℂ (algebra A)) ∈ OAI.HochschildNormalPart.normalDual
        (CoefficientPredual.concretePredualIsometry (algebra A)) :=
  CoefficientPredual.coefficientPredual_normal (algebra A) ((canonicalPredualEquiv A).symm φ)

theorem canonicalPredualEquiv_symm_eq_positiveExtension
    (ψ : A →ₚ[ℂ] ℂ) (φ : StrongDual ℂ A) (hφ : ∀ a : A, φ a = ψ a) :
    (canonicalPredualEquiv A).symm φ = positiveExtension A ψ := by
  apply (canonicalPredualEquiv A).injective
  calc
    canonicalPredualEquiv A ((canonicalPredualEquiv A).symm φ) = φ :=
      (canonicalPredualEquiv A).apply_symm_apply φ
    _ = canonicalPredualEquiv A (positiveExtension A ψ) := by
      ext a
      change φ a = restriction A (positiveExtension A ψ) a
      exact (hφ a).trans (positiveExtension_apply A ψ a).symm

/-- Positivity is supplied by a GNS coefficient, not an additional assumption
on the canonical extension of a positive functional. -/
theorem positiveExtension_starSquare_nonneg (ψ : A →ₚ[ℂ] ℂ) (T : algebra A) :
    0 ≤ ((positiveExtension A ψ : predual A) : StrongDual ℂ (algebra A)) (star T * T) := by
  let v := cyclicVector A ψ
  change 0 ≤ ⟪v, (T : Hilbert A →L[ℂ] Hilbert A).adjoint
    ((T : Hilbert A →L[ℂ] Hilbert A) v)⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right
    (T : Hilbert A →L[ℂ] Hilbert A) v ((T : Hilbert A →L[ℂ] Hilbert A) v),
    inner_self_eq_norm_sq_to_K ((T : Hilbert A →L[ℂ] Hilbert A) v)]
  positivity

theorem canonicalPredualEquiv_symm_starSquare_nonneg
    (ψ : A →ₚ[ℂ] ℂ) (φ : StrongDual ℂ A) (hφ : ∀ a : A, φ a = ψ a)
    (T : algebra A) :
    0 ≤ (((canonicalPredualEquiv A).symm φ : predual A) :
      StrongDual ℂ (algebra A)) (star T * T) := by
  exact Eq.mpr
    (congrArg (fun ρ : predual A =>
      0 ≤ (ρ : StrongDual ℂ (algebra A)) (star T * T))
      (canonicalPredualEquiv_symm_eq_positiveExtension A ψ φ hφ))
    (positiveExtension_starSquare_nonneg A ψ T)

end SpectralIsometry.BidualFoundation.UniversalWeakClosure

