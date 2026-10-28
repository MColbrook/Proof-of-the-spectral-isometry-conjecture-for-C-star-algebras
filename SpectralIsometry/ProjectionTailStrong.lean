module

public import SpectralIsometry.StrongStarApproximation
public import SpectralIsometry.BidualConcretePredual
public import OAI.Analysis.BoundedHochschild.CochainLimits
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Projection Tail Strong

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexOrder
open OAI.BoundedHochschild
open SpectralIsometry.BidualFoundation.CoefficientPredual

namespace SpectralIsometry.StrongStarApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance complexNormedSpaceSelf : NormedSpace ℂ ℂ := NormedField.toNormedSpace
local instance coefficientNormedGroup (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (coefficientPredual M) :=
  SpectralIsometry.BidualFoundation.CoefficientPredual.coefficientNormedGroup M
local instance coefficientNormedSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (coefficientPredual M) :=
  SpectralIsometry.BidualFoundation.CoefficientPredual.coefficientNormedSpace M

theorem strongStarTendsto_zero_of_projection_diagonal {ι : Type*} {l : Filter ι}
    (r : ι → Op (H := H)) (hr : ∀ i, IsStarProjection (r i))
    (hlim : ∀ ξ : H, Tendsto (fun i => inner ℂ ξ (r i ξ)) l (𝓝 0)) :
    StrongStarTendsto r l 0 := by
  have he (i : ι) (ξ : H) : ‖r i ξ‖ = Real.sqrt (inner ℂ ξ (r i ξ)).re := by
    have h := (r i).apply_norm_eq_sqrt_inner_adjoint_right ξ
    have hsq : (r i).adjoint.comp (r i) = r i := by
      change star (r i) * r i = r i
      rw [(hr i).isSelfAdjoint.star_eq,(hr i).isIdempotentElem.eq]
    rw [hsq] at h
    exact h
  have ht : StrongTendsto r l 0 := by
    intro ξ
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hre := Complex.continuous_re.continuousAt.tendsto.comp (hlim ξ)
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hre
    change Tendsto (fun i => Real.sqrt (inner ℂ ξ (r i ξ)).re) l (𝓝 (Real.sqrt (0 : ℝ))) at hh
    have hfn : (fun i => Real.sqrt (inner ℂ ξ (r i ξ)).re) = (fun i => ‖r i ξ‖) :=
      funext fun i => (he i ξ).symm
    rw [hfn,Real.sqrt_zero] at hh
    exact hh
  refine ⟨ht,?_⟩
  have hstar : (fun i => star (r i)) = r := funext fun i => (hr i).isSelfAdjoint.star_eq
  rw [hstar,star_zero]
  exact ht

theorem strongStarTendsto_zero_of_projection_predual
    (M : VonNeumannAlgebra H) {ι : Type*} {l : Filter ι}
    (r : ι → M) (hr : ∀ i, IsStarProjection (r i))
    (hlim : PredualTendsto (X := coefficientPredual M) (concretePredualIsometry M) r l 0) :
    StrongStarTendsto (fun i => (r i : Op (H := H))) l 0 := by
  have hrop (i : ι) : IsStarProjection (r i : Op (H := H)) :=
    ⟨congrArg Subtype.val (hr i).isIdempotentElem.eq,
      congrArg Subtype.val (hr i).isSelfAdjoint.star_eq⟩
  apply strongStarTendsto_zero_of_projection_diagonal _ hrop
  intro ξ
  have h := hlim (coefficientVector M ξ ξ)
  change Tendsto (fun i => vectorFunctional M ξ ξ (star (r i))) l
    (𝓝 (vectorFunctional M ξ ξ (star (0 : M)))) at h
  have hfn : (fun i => vectorFunctional M ξ ξ (star (r i))) =
      (fun i => vectorFunctional M ξ ξ (r i)) := by
    funext i
    rw [(hr i).isSelfAdjoint.star_eq]
  rw [hfn] at h
  simpa only [star_zero,map_zero,vectorFunctional_apply] using h

end SpectralIsometry.StrongStarApproximation

