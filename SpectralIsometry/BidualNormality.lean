module

public import SpectralIsometry.BidualConcretePredual

/-!
# Bidual Normality

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SpectralIsometry.BidualFoundation.CoefficientPredual

attribute [local instance] complexNormedSpaceSelf dualNormedGroup dualNormedSpace
  coefficientNormedGroup coefficientNormedSpace

open scoped InnerProductSpace
open OAI.HochschildNormalPart

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorFunctional_normal (M : VonNeumannAlgebra H) (ξ η : H) :
    vectorFunctional M ξ η ∈ normalDual (concretePredualIsometry M) := by
  apply (mem_normalDual (concretePredualIsometry M) _).mpr
  refine ⟨coefficientVector M η ξ, ?_⟩
  intro T
  change ⟪ξ, (T : H →L[ℂ] H) η⟫_ℂ =
    star ⟪η, star (T : H →L[ℂ] H) ξ⟫_ℂ
  symm
  rw [Complex.star_def, inner_conj_symm, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

theorem coefficientPredual_normal (M : VonNeumannAlgebra H)
    (φ : coefficientPredual M) : φ.val ∈ normalDual (concretePredualIsometry M) := by
  have hs : Submodule.span ℂ (Set.range (fun p : H × H => vectorFunctional M p.1 p.2)) ≤
      normalDual (concretePredualIsometry M) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨ξ, η⟩, rfl⟩
    exact vectorFunctional_normal M ξ η
  exact (Submodule.topologicalClosure_minimal _ hs
    (normalDual_closed (concretePredualIsometry M))) φ.property

theorem normalDual_eq_coefficientPredual (M : VonNeumannAlgebra H) :
    normalDual (concretePredualIsometry M) = coefficientPredual M := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨x, hx⟩ := hφ
    obtain ⟨w, hw⟩ := (mem_normalDual (concretePredualIsometry M) x.val).mp
      (coefficientPredual_normal M x)
    have he : predualEmbedding (concretePredualIsometry M) x = w.val := by
      ext T
      change star (x.val (star T)) = w.val T
      have h := hw (star T)
      change x.val (star T) = star (w.val (star (star T))) at h
      simpa only [star_star] using congrArg star h
    rw [← hx]
    change predualEmbedding (concretePredualIsometry M) x ∈ coefficientPredual M
    rw [he]
    exact w.property
  · intro φ hφ
    exact coefficientPredual_normal M ⟨φ, hφ⟩

end SpectralIsometry.BidualFoundation.CoefficientPredual

