module

public import SpectralIsometry.DyadicThresholdEstimate
public import SpectralIsometry.StrongStarApproximation
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Tactic.Linarith

/-!
# Dyadic Projection Strong

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace SpectralIsometry.StrongStarApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_apply_sq_le_of_selfAdjoint_square_le
    (d e : Op (H := H)) (hd : IsSelfAdjoint d) (he : IsSelfAdjoint e)
    (hle : d ^ 2 ≤ 4 * e ^ 2) (ξ : H) : ‖d ξ‖ ^ 2 ≤ 4 * ‖e ξ‖ ^ 2 := by
  have hnorm (a : Op (H := H)) (ha : IsSelfAdjoint a) :
      ‖a ξ‖ ^ 2 = (inner ℂ ξ ((a ^ 2) ξ)).re := by
    have hh := a.apply_norm_sq_eq_inner_adjoint_right ξ
    change ‖a ξ‖ ^ 2 = (inner ℂ ξ ((star a * a) ξ)).re at hh
    simpa only [ha.star_eq,pow_two] using hh
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hle)).re_inner_nonneg_right ξ
  have hfour : (4 : Op (H := H)) * e ^ 2 = e ^ 2 + e ^ 2 + e ^ 2 + e ^ 2 := by noncomm_ring
  change 0 ≤ (inner ℂ ξ (((4 : Op (H := H)) * e ^ 2 - d ^ 2) ξ)).re at hp
  rw [hfour] at hp
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    inner_sub_right,inner_add_right,Complex.sub_re,Complex.add_re] at hp
  rw [←hnorm d hd,←hnorm e he] at hp
  linarith

theorem strongStarTendsto_dyadic_projections {ι : Type*} {l : Filter ι}
    (a q : ι → Op (H := H)) (p : Op (H := H))
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hq : ∀ i, IsStarProjection (q i)) (hp : IsStarProjection p)
    (haq : ∀ i, Commute (a i) (q i))
    (hc0 : ∀ i, 0 ≤ 2 * a i - q i) (hc1 : ∀ i, 2 * a i - q i ≤ 1)
    (halim : StrongStarTendsto a l p) : StrongStarTendsto q l p := by
  have hanorm (i : ι) : ‖a i‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (a i) (ha0 i)).mpr (ha1 i)
  have hprod : StrongTendsto (fun i => a i * a i) l (p * p) :=
    strongTendsto_mul_of_left_norm_bound halim.1 halim.1 (Eventually.of_forall hanorm)
  have hdef (ξ : H) : Tendsto (fun i => (a i - (a i) ^ 2) ξ) l (𝓝 0) := by
    have hh := (halim.1 ξ).sub (hprod ξ)
    simpa only [pow_two,ContinuousLinearMap.sub_apply,hp.isIdempotentElem.eq,sub_self] using hh
  have herr (i : ι) (ξ : H) : ‖(q i - a i) ξ‖ ≤ 2 * ‖(a i - (a i) ^ 2) ξ‖ := by
    have ha : IsSelfAdjoint (a i) := IsSelfAdjoint.of_nonneg (ha0 i)
    have he := norm_apply_sq_le_of_selfAdjoint_square_le (q i - a i) (a i - (a i)^2)
      ((hq i).isSelfAdjoint.sub ha) (ha.sub (ha.pow 2))
      (SpectralIsometry.SquareZeroPreserver.dyadic_projection_square_error_le
        (hq i) (haq i) (hc0 i) (hc1 i)) ξ
    nlinarith [norm_nonneg ((q i - a i) ξ),norm_nonneg ((a i - (a i)^2) ξ)]
  have hqstrong : StrongTendsto q l p := by
    intro ξ
    have herror : Tendsto (fun i => (q i - a i) ξ) l (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) (Eventually.of_forall fun i => herr i ξ)
      simpa only [norm_zero,mul_zero] using (hdef ξ).norm.const_mul (2 : ℝ)
    have hh := herror.add (halim.1 ξ)
    simpa only [ContinuousLinearMap.sub_apply,sub_add_cancel,zero_add] using hh
  refine ⟨hqstrong,?_⟩
  have hstar : (fun i => star (q i)) = q := funext fun i => (hq i).isSelfAdjoint.star_eq
  rw [hstar,hp.isSelfAdjoint.star_eq]
  exact hqstrong

end SpectralIsometry.StrongStarApproximation

