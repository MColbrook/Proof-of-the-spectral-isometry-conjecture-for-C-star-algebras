module

public import OAI.Analysis.BoundedHochschild.NormalVectors
public import SpectralIsometry.StrongStarApproximation

/-!
# Generic Normal Projection Continuity

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.NormalProjectionContinuity

open Filter Topology OAI.HochschildNormalPart
open StrongStarApproximation
open scoped InnerProductSpace ComplexOrder

universe u v w
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))

local instance orderedM : PartialOrder M := CStarAlgebra.spectralOrder M
local instance starOrderedM : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
local instance (priority := 2000) complexOrder : PartialOrder ℂ := Complex.partialOrder
local instance (priority := 2000) complexStarOrder : StarOrderedRing ℂ := RCLike.toStarOrderedRing

/-- The manuscript's intrinsic normal-positive strong-star seminorm condition.
The bounded functional φ records exactly the same ψ and its actual predual
normality; neither continuity of an arbitrary map nor an operator norm bound
is built into this definition. Orders come from CStarAlgebra internally. -/
def NormalPositiveStrongStarTendsto {ι : Type w} (a : ι → M) (l : Filter ι) (b : M) : Prop :=
  ∀ (ψ : M →ₚ[ℂ] ℂ) (φ : StrongDual ℂ M),
    (∀ x : M, φ x = ψ x) → φ ∈ normalDual e →
    Tendsto (fun i => (ψ (star (a i-b)*(a i-b))).re +
      (ψ ((a i-b)*star (a i-b))).re) l (𝓝 0)

/-- A diagonal coefficient is positive for the canonical C*-order. Selected
body reuse: OAI.Analysis.BoundedHochschild.FiniteTraceCover.vectorPositiveFunctional. -/
def diagonalPositive (v : H) : M →ₚ[ℂ] ℂ where
  toLinearMap := (coefficient π v v).toLinearMap
  monotone' := by
    change Monotone (coefficient π v v)
    apply (monotone_iff_map_nonneg _).mpr
    intro a ha
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (map_nonneg π ha)).inner_nonneg_right v

@[simp] theorem diagonalPositive_apply (v : H) (a : M) :
    diagonalPositive π v a = inner ℂ v (π a v) := rfl

theorem diagonalPositive_star_mul_self (v : H) (a : M) :
    (diagonalPositive π v (star a*a)).re = ‖π a v‖^2 := by
  change (inner ℂ v (π (star a*a) v)).re = ‖π a v‖^2
  rw [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜:=ℂ) (π a v)).symm

theorem diagonalPositive_mul_star_self (v : H) (a : M) :
    (diagonalPositive π v (a*star a)).re = ‖π (star a) v‖^2 := by
  simpa only [star_star] using diagonalPositive_star_mul_self π v (star a)

/-- A normal diagonal coefficient forces its vector into the normal summand.
Evaluate the existing coefficient identity at 1, then use orthogonality. -/
theorem normalProjection_apply_eq_self_of_diagonal_normal (v : H)
    (h : coefficient π v v ∈ normalDual e) : normalProjection e π v=v := by
  have hh := congrArg (fun F : StrongDual ℂ M => F 1)
    (normalProjection_fixes_normal e π v v h)
  have hinner : inner ℂ v (normalProjection e π v)=inner ℂ v v := by
    simpa only [coefficient_apply,map_one,one_apply_eq_self] using hh
  have horth : inner ℂ (normalProjection e π v) (v-normalProjection e π v)=0 :=
    (normalVectors e π).sub_starProjection_mem_orthogonal v _ (by simp [normalProjection])
  have hzero : v-normalProjection e π v=0 := by
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    rw [inner_sub_left,horth,sub_zero,inner_sub_right,hinner,sub_self]
  exact (sub_eq_zero.mp hzero).symm

/-- The seminorm sum becomes the two actual squared vector norms on a normal vector. -/
theorem norm_squares_tendsto_zero_at_normal_vector {ι : Type w} {l : Filter ι}
    {a : ι → M} {b : M} (h : NormalPositiveStrongStarTendsto e a l b)
    (v : H) (hv : v ∈ normalVectors e π) :
    Tendsto (fun i => ‖π (a i-b) v‖^2 + ‖π (star (a i-b)) v‖^2) l (𝓝 0) := by
  have hn : coefficient π v v ∈ normalDual e := (mem_normalVectors e π v).mp hv v
  have ht := h (diagonalPositive π v) (coefficient π v v) (fun _ => rfl) hn
  simpa only [diagonalPositive_star_mul_self,diagonalPositive_mul_star_self] using ht

private theorem tendsto_zero_of_norm_sq {ι : Type w} {l : Filter ι}
    {f : ι → H} (h : Tendsto (fun i => ‖f i‖^2) l (𝓝 (0:ℝ))) :
    Tendsto f l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  change Tendsto (fun i => Real.sqrt (‖f i‖^2)) l (𝓝 (Real.sqrt (0:ℝ))) at hs
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs

theorem compressed_difference (a b : M) (v : H) :
    (normalProjection e π * π a) v - (normalProjection e π * π b) v =
      π (a-b) (normalProjection e π v) := by
  rw [normalProjection_mul e π a,normalProjection_mul e π b,map_sub]
  rfl

theorem star_compression (a : M) :
    star (normalProjection e π * π a)=normalProjection e π * π (star a) := by
  have hp : star (normalProjection e π)=normalProjection e π :=
    (isStarProjection_starProjection (U:=normalVectors e π)).isSelfAdjoint.star_eq
  rw [star_mul,hp,←map_star,normalProjection_mul e π (star a)]

/-- Intrinsic normal-positive seminorm convergence implies actual operator
strong-star convergence after normal projection. This theorem has no boundedness
assumption and applies to arbitrary filters and complete Hilbert spaces. -/
theorem strongStarTendsto_compressed_of_normalPositive {ι : Type w} {l : Filter ι}
    {a : ι → M} {b : M} (h : NormalPositiveStrongStarTendsto e a l b) :
    StrongStarTendsto (fun i => normalProjection e π * π (a i)) l
      (normalProjection e π * π b) := by
  have hv (v : H) : normalProjection e π v ∈ normalVectors e π := by
    simp [normalProjection]
  constructor
  · intro v
    have ht := norm_squares_tendsto_zero_at_normal_vector e π h
      (normalProjection e π v) (hv v)
    have hz : Tendsto (fun i => ‖π (a i-b) (normalProjection e π v)‖^2) l (𝓝 0) :=
      squeeze_zero (fun _ => sq_nonneg _) (fun _ => le_add_of_nonneg_right (sq_nonneg _)) ht
    have hf := (tendsto_zero_of_norm_sq hz).norm
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_eq_norm,compressed_difference,norm_zero] using hf
  · intro v
    have ht := norm_squares_tendsto_zero_at_normal_vector e π h
      (normalProjection e π v) (hv v)
    have hz : Tendsto (fun i => ‖π (star (a i-b)) (normalProjection e π v)‖^2) l (𝓝 0) :=
      squeeze_zero (fun _ => sq_nonneg _) (fun _ => le_add_of_nonneg_left (sq_nonneg _)) ht
    have hf := (tendsto_zero_of_norm_sq hz).norm
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_eq_norm,star_compression,compressed_difference,star_sub,norm_zero] using hf

end SpectralIsometry.NormalProjectionContinuity

