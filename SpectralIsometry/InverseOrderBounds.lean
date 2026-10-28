module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import SpectralIsometry.StrongStarApproximation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

/-!
# Inverse Order Bounds

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProductSpace

namespace SpectralIsometry.InverseOrderBounds

section GenericCStar
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem left_inverse_of_quadratic_lower (c : A) {r : ℝ} (hr : 0<r)
    (hc : algebraMap ℝ A r ≤ star c*c) :
    (Ring.inverse (star c*c)*star c)*c=1 := by
  have hu : IsUnit (star c*c) := CStarAlgebra.isUnit_of_le (algebraMap ℝ A r) hc
    (isStrictlyPositive_algebraMap hr)
  rw [mul_assoc,Ring.inverse_mul_cancel _ hu]

theorem right_inverse_of_quadratic_lower (c : A) {r : ℝ} (hr : 0<r)
    (hc : algebraMap ℝ A r ≤ c*star c) :
    c*(star c*Ring.inverse (c*star c))=1 := by
  have hu : IsUnit (c*star c) := CStarAlgebra.isUnit_of_le (algebraMap ℝ A r) hc
    (isStrictlyPositive_algebraMap hr)
  rw [←mul_assoc,Ring.mul_inverse_cancel _ hu]

theorem isUnit_of_two_quadratic_lower (c : A) {r : ℝ} (hr : 0<r)
    (hl : algebraMap ℝ A r ≤ star c*c) (hright : algebraMap ℝ A r ≤ c*star c) :
    IsUnit c := by
  let l := Ring.inverse (star c*c)*star c
  let d := star c*Ring.inverse (c*star c)
  have hlc : l*c=1 := left_inverse_of_quadratic_lower c hr hl
  have hcd : c*d=1 := right_inverse_of_quadratic_lower c hr hright
  have he : l=d := by
    calc l=l*(c*d) := by rw [hcd,mul_one]
         _=(l*c)*d := (mul_assoc _ _ _).symm
         _=d := by rw [hlc,one_mul]
  exact ⟨⟨c,l,by rw [he]; exact hcd,hlc⟩,rfl⟩

variable [Nontrivial A]

theorem positive_unit_spectral_lower (a : Aˣ) (ha : (0:A)≤a) :
    algebraMap ℝ A ‖(↑a⁻¹:A)‖⁻¹ ≤ (a:A) := by
  apply (algebraMap_le_iff_le_spectrum ha.isSelfAdjoint).mpr
  intro r hr
  have hrne : r≠0 := by
    intro he
    exact (spectrum.zero_notMem ℝ a.isUnit) (he ▸ hr)
  have hrpos : 0<r := lt_of_le_of_ne (spectrum_nonneg_of_nonneg ha hr) hrne.symm
  have hi : r⁻¹ ∈ spectrum ℝ (↑a⁻¹:A) := spectrum.inv₀_mem_inv_iff.mpr hr
  have hb : r⁻¹≤‖(↑a⁻¹:A)‖ := by
    simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hrpos)] using spectrum.norm_le_norm_of_mem hi
  exact (inv_le_comm₀ (Units.norm_pos a⁻¹) hrpos).mpr hb

theorem star_mul_self_inverse_lower (c : A) (hc : IsUnit c) :
    algebraMap ℝ A ((‖Ring.inverse c‖⁻¹)^2) ≤ star c*c := by
  have hq := hc.star.mul hc
  have hh := positive_unit_spectral_lower hq.unit
    (by simpa only [hq.unit_spec] using star_mul_self_nonneg c)
  have hi : (↑hq.unit⁻¹:A)=Ring.inverse (star c*c) := by
    rw [←Ring.inverse_unit,hq.unit_spec]
  have hn : ‖Ring.inverse (star c*c)‖=‖Ring.inverse c‖^2 := by
    rw [Ring.inverse_mul (Or.inl hc.star),Ring.inverse_star,CStarRing.norm_self_mul_star,pow_two]
  simpa only [hq.unit_spec,hi,hn,inv_pow] using hh

theorem star_mul_self_lower_of_inverse_norm_bound (c : A) (hc : IsUnit c)
    {L : ℝ} (hL : 0<L) (hbound : ‖Ring.inverse c‖≤L) :
    algebraMap ℝ A ((L⁻¹)^2) ≤ star c*c := by
  have hnpos : 0<‖Ring.inverse c‖ := norm_pos_iff.mpr hc.ringInverse.ne_zero
  have hInv : L⁻¹≤‖Ring.inverse c‖⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hnpos hbound
  have hs : (L⁻¹)^2≤(‖Ring.inverse c‖⁻¹)^2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hL.le) hInv 2
  apply (algebraMap_le_iff_le_spectrum (IsSelfAdjoint.star_mul_self c)).mpr
  have hh := (algebraMap_le_iff_le_spectrum (IsSelfAdjoint.star_mul_self c)).mp
    (star_mul_self_inverse_lower c hc)
  exact fun r hr => hs.trans (hh r hr)

theorem two_quadratic_lower_of_inverse_norm_bound (c : A) (hc : IsUnit c)
    {L : ℝ} (hL : 0<L) (hbound : ‖Ring.inverse c‖≤L) :
    algebraMap ℝ A ((L⁻¹)^2) ≤ star c*c ∧
      algebraMap ℝ A ((L⁻¹)^2) ≤ c*star c := by
  refine ⟨star_mul_self_lower_of_inverse_norm_bound c hc hL hbound,?_⟩
  simpa only [star_star] using star_mul_self_lower_of_inverse_norm_bound (star c) hc.star hL
    (by simpa only [Ring.inverse_star,norm_star] using hbound)
end GenericCStar

section HilbertOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem scalar_le_star_mul_self_iff (c : H →L[ℂ] H) (r : ℝ) :
    r • (1:H →L[ℂ] H) ≤ star c*c ↔ ∀ ξ : H, r*‖ξ‖^2≤‖c ξ‖^2 := by
  have hsa : IsSelfAdjoint (star c*c-r • (1:H →L[ℂ] H)) := by
    simp [isSelfAdjoint_iff]
  have hform (ξ : H) : (star c*c-r • (1:H →L[ℂ] H)).reApplyInnerSelf ξ=
      ‖c ξ‖^2-r*‖ξ‖^2 := by
    have hc : (inner ℂ ((star c*c) ξ) ξ).re=‖c ξ‖^2 :=
      (c.apply_norm_sq_eq_inner_adjoint_left ξ).symm
    have hr : (inner ℂ ((r • (1:H →L[ℂ] H)) ξ) ξ).re=r*‖ξ‖^2 := by
      simp [inner_smul_left_eq_star_smul,inner_self_eq_norm_sq_to_K,←Complex.ofReal_pow]
    rw [ContinuousLinearMap.reApplyInnerSelf_apply,ContinuousLinearMap.sub_apply,inner_sub_left]
    change (inner ℂ ((star c*c) ξ) ξ-inner ℂ ((r • (1:H →L[ℂ] H)) ξ) ξ).re=
      ‖c ξ‖^2-r*‖ξ‖^2
    rw [Complex.sub_re,hc,hr]
  rw [ContinuousLinearMap.le_def,ContinuousLinearMap.isPositive_def']
  constructor
  · intro h ξ
    have hh := h.2 ξ
    rw [hform] at hh
    exact sub_nonneg.mp hh
  · intro h
    refine ⟨hsa,fun ξ => ?_⟩
    rw [hform]
    exact sub_nonneg.mpr (h ξ)

theorem two_quadratic_bounds_pass_to_strongStar {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → (H →L[ℂ] H)) (b : H →L[ℂ] H) (r : ℝ)
    (ha : StrongStarApproximation.StrongStarTendsto a l b)
    (hl : ∀ i, r • (1:H →L[ℂ] H) ≤ star (a i)*a i)
    (hr : ∀ i, r • (1:H →L[ℂ] H) ≤ a i*star (a i)) :
    r • (1:H →L[ℂ] H) ≤ star b*b ∧ r • (1:H →L[ℂ] H) ≤ b*star b := by
  constructor
  · apply (scalar_le_star_mul_self_iff b r).mpr
    intro ξ
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ((ha.1 ξ).norm.pow 2)
      (Eventually.of_forall fun i => (scalar_le_star_mul_self_iff (a i) r).mp (hl i) ξ)
  · have hh : r • (1:H →L[ℂ] H) ≤ star (star b)*star b := by
      apply (scalar_le_star_mul_self_iff (star b) r).mpr
      intro ξ
      exact le_of_tendsto_of_tendsto tendsto_const_nhds ((ha.2 ξ).norm.pow 2)
        (Eventually.of_forall fun i => (scalar_le_star_mul_self_iff (star (a i)) r).mp
          (by simpa only [star_star] using hr i) ξ)
    simpa only [star_star] using hh

/-- Exact operator version of c_i*c_i and c_ic_i* ≥ L^-2 1,
including the zero Hilbert space. -/
theorem operator_quadratic_bounds_of_inverse_norm (c : H →L[ℂ] H) (hc : IsUnit c)
    {L : ℝ} (hL : 0<L) (hbound : ‖Ring.inverse c‖≤L) :
    (L⁻¹)^2 • (1:H →L[ℂ] H) ≤ star c*c ∧
      (L⁻¹)^2 • (1:H →L[ℂ] H) ≤ c*star c := by
  cases subsingleton_or_nontrivial (H →L[ℂ] H) with
  | inl hs =>
    letI := hs
    exact ⟨(Subsingleton.elim _ _).le,(Subsingleton.elim _ _).le⟩
  | inr hn =>
    letI := hn
    simpa only [Algebra.algebraMap_eq_smul_one] using
      two_quadratic_lower_of_inverse_norm_bound c hc hL hbound

/-- The first limiting inequality constructs a left inverse, the second a
right inverse; hence the strong-star limit is invertible, exactly as in L04d. -/
theorem isUnit_of_strongStar_quadratic_bounds {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → (H →L[ℂ] H)) (b : H →L[ℂ] H) {r : ℝ} (hr : 0<r)
    (ha : StrongStarApproximation.StrongStarTendsto a l b)
    (hl : ∀ i, r • (1:H →L[ℂ] H) ≤ star (a i)*a i)
    (hright : ∀ i, r • (1:H →L[ℂ] H) ≤ a i*star (a i)) : IsUnit b := by
  obtain ⟨hbl,hbr⟩ := two_quadratic_bounds_pass_to_strongStar a b r ha hl hright
  apply isUnit_of_two_quadratic_lower b hr
  · simpa only [Algebra.algebraMap_eq_smul_one] using hbl
  · simpa only [Algebra.algebraMap_eq_smul_one] using hbr
end HilbertOperators

end SpectralIsometry.InverseOrderBounds

