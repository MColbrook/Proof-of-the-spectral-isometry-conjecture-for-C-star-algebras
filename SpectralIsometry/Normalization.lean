module

public import SpectralIsometry.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalization

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open Filter Topology Finset
open scoped ENNReal

namespace SpectralIsometry.Normalization

variable {A : Type*} [CStarAlgebra A]

private theorem eventual_norm_pow_lt (a : A) {t : ℝ}
    (ht : (spectralRadius ℂ a).toReal < t) :
    ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ < t ^ n := by
  have ht0 : 0 < t := ENNReal.toReal_nonneg.trans_lt ht
  have hrfin : spectralRadius ℂ a ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜 := ℂ) a)
  have hrv : spectralRadius ℂ a < ENNReal.ofReal t :=
    (ENNReal.lt_ofReal_iff_toReal_lt hrfin).mpr ht
  have he := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
    (gt_mem_nhds hrv)
  filter_upwards [eventually_gt_atTop 0, he] with n hn hroot
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : (‖a ^ n‖₊ : ℝ≥0∞) < (ENNReal.ofReal t) ^ (n : ℝ) :=
    (ENNReal.rpow_inv_lt_iff hnR).mp (by simpa only [one_div] using hroot)
  rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow ht0.le] at hp
  simpa only [coe_nnnorm] using (ENNReal.coe_lt_ofReal.mp hp)

/-- Turn eventual Gelfand bounds into a bound on all powers, including zero. -/
theorem exists_uniform_power_bound (a : A) {t : ℝ}
    (ht : (spectralRadius ℂ a).toReal < t) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ K * t ^ n := by
  have ht0 : 0 < t := ENNReal.toReal_nonneg.trans_lt ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventual_norm_pow_lt a ht)
  let K : ℝ := 1 + ∑ k ∈ range N, ‖a ^ k‖ / t ^ k
  have hsum : 0 ≤ ∑ k ∈ range N, ‖a ^ k‖ / t ^ k :=
    sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg ht0.le _)
  have hK : 1 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).le.trans (le_mul_of_one_le_left (pow_nonneg ht0.le n) hK)
  · have hterm : ‖a ^ n‖ / t ^ n ≤ ∑ k ∈ range N, ‖a ^ k‖ / t ^ k :=
      single_le_sum (f := fun k : ℕ => ‖a ^ k‖ / t ^ k)
        (fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg ht0.le _))
        (mem_range.mpr (Nat.lt_of_not_ge hn))
    apply (div_le_iff₀ (pow_pos ht0 n)).mp
    exact hterm.trans (by dsimp [K]; linarith)

/-- Exact binomial norm estimate for commuting perturbations. -/
theorem norm_add_pow_le_of_power_bound [Nontrivial A] (a z : A) (haz : Commute a z)
    (t K : ℝ) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hpow : ∀ n : ℕ, ‖a ^ n‖ ≤ K * t ^ n) (n : ℕ) :
    ‖(a + z) ^ n‖ ≤ K * (t + ‖z‖) ^ n := by
  rw [haz.add_pow', (Commute.all t ‖z‖).add_pow', mul_sum]
  calc
    ‖∑ m ∈ Finset.antidiagonal n, n.choose m.1 • (a ^ m.1 * z ^ m.2)‖ ≤
        ∑ m ∈ Finset.antidiagonal n, ‖n.choose m.1 • (a ^ m.1 * z ^ m.2)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.antidiagonal n, K * (n.choose m.1 • (t ^ m.1 * ‖z‖ ^ m.2)) := by
      apply sum_le_sum
      intro m hm
      calc
        ‖n.choose m.1 • (a ^ m.1 * z ^ m.2)‖ ≤
            (n.choose m.1 : ℝ) * ‖a ^ m.1 * z ^ m.2‖ := norm_nsmul_le
        _ ≤ (n.choose m.1 : ℝ) * (‖a ^ m.1‖ * ‖z ^ m.2‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (Nat.cast_nonneg _)
        _ ≤ (n.choose m.1 : ℝ) * ((K * t ^ m.1) * ‖z‖ ^ m.2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hpow m.1) (norm_pow_le z m.2) (norm_nonneg _) (mul_nonneg hK (pow_nonneg ht _)))
            (Nat.cast_nonneg _)
        _ = K * (n.choose m.1 • (t ^ m.1 * ‖z‖ ^ m.2)) := by
          rw [nsmul_eq_mul]
          ring

/-- Spectral-radius perturbation bound for commuting elements. Zero algebra
is handled internally, so it is not a hypothesis of the public result. -/
theorem radius_add_le_radius_add_norm (a z : A) (haz : Commute a z) :
    (spectralRadius ℂ (a + z)).toReal ≤ (spectralRadius ℂ a).toReal + ‖z‖ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI := hA
    have ha : a = 0 := Subsingleton.elim _ _
    have hz : z = 0 := Subsingleton.elim _ _
    simp [ha, hz, spectrum.spectralRadius_zero]
  · letI := hA
    apply le_of_forall_pos_le_add
    intro ε hε
    let t : ℝ := (spectralRadius ℂ a).toReal + ε
    have ht : (spectralRadius ℂ a).toReal < t := by dsimp [t]; linarith
    have ht0 : 0 < t := ENNReal.toReal_nonneg.trans_lt ht
    obtain ⟨K, hK, hp⟩ := exists_uniform_power_bound a ht
    have hK0 : 0 < K := zero_lt_one.trans_le hK
    have hfrac : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
    have hrootK : Tendsto (fun n : ℕ => K ^ (1 / (n + 1) : ℝ)) atTop (𝓝 1) := by
      simpa only [Real.rpow_zero, Function.comp_def] using
        (Real.continuousAt_const_rpow hK0.ne').tendsto.comp hfrac
    have hlim : Tendsto (fun n : ℕ => K ^ (1 / (n + 1) : ℝ) * (t + ‖z‖)) atTop
        (𝓝 (t + ‖z‖)) := by simpa only [one_mul] using hrootK.mul_const (t + ‖z‖)
    have hineq (n : ℕ) : ‖(a + z) ^ (n + 1)‖ ^ (1 / (n + 1) : ℝ) ≤
        K ^ (1 / (n + 1) : ℝ) * (t + ‖z‖) := by
      calc
        ‖(a + z) ^ (n + 1)‖ ^ (1 / (n + 1) : ℝ) ≤
            (K * (t + ‖z‖) ^ (n + 1)) ^ (1 / (n + 1) : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _)
            (norm_add_pow_le_of_power_bound a z haz t K ht0.le hK0.le hp _) (by positivity)
        _ = K ^ (1 / (n + 1) : ℝ) * (t + ‖z‖) := by
          rw [Real.mul_rpow hK0.le (pow_nonneg (by positivity) _)]
          congr 1
          simpa only [one_div, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
            Real.pow_rpow_inv_natCast (x := t + ‖z‖) (by positivity) (Nat.succ_ne_zero n)
    have hr := le_of_tendsto_of_tendsto
      (AutomaticContinuity.power_root_tendsto_radiusReal (a + z)) hlim
      (Eventually.of_forall hineq)
    dsimp only [t] at hr
    linarith

/- Untested continuation. Append only after active proof check terminates.
The conjugation/Liouville derivative method reuses own NormRadiusWork, now in
Solution, but the hypothesis here is the proved translation-radius property. -/

def Central (c : A) : Prop := ∀ x : A, c * x = x * c

private theorem radius_neg (a : A) : spectralRadius ℂ (-a) = spectralRadius ℂ a := by
  apply tendsto_nhds_unique (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (-a))
  simpa only [nnnorm_neg_pow] using spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a

private theorem radius_unit_conjugate (u : Aˣ) (a : A) :
    spectralRadius ℂ ((u : A) * a * (↑u⁻¹ : A)) = spectralRadius ℂ a := by
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital, spectrum.units_conjugate]

private theorem radius_unit_conjugate' (u : Aˣ) (a : A) :
    spectralRadius ℂ ((↑u⁻¹ : A) * a * (u : A)) = spectralRadius ℂ a := by
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital, spectrum.units_conjugate']

/-- The translation property itself yields a uniform norm bound. -/
theorem norm_le_of_translation_radius_bound (c : A) (C : ℝ)
    (h : ∀ x : A, (spectralRadius ℂ (c + x)).toReal ≤ (spectralRadius ℂ x).toReal + C) :
    ‖c‖ ≤ 2 * C := by
  have hc : (spectralRadius ℂ c).toReal ≤ C := by
    simpa only [add_zero, spectrum.spectralRadius_zero, ENNReal.toReal_zero, zero_add] using h 0
  have hsum : ‖c + star c‖ ≤ 2 * C := by
    have he := h (star c)
    rw [(IsSelfAdjoint.add_star_self c).toReal_spectralRadius_complex_eq_norm,
      radius_star] at he
    linarith
  have hsk : star (c - star c) = -(c - star c) := by simp [star_sub]
  letI : IsStarNormal (c - star c) := ⟨by
    rw [hsk]
    exact (Commute.refl (c - star c)).neg_left⟩
  have hdiff : ‖c - star c‖ ≤ 2 * C := by
    have he := h (-star c)
    rw [← sub_eq_add_neg, IsStarNormal.spectralRadius_eq_nnnorm,
      ENNReal.coe_toReal, coe_nnnorm, radius_neg, radius_star] at he
    linarith
  have heq : (2 : ℝ) • c = (c + star c) + (c - star c) := by
    rw [two_smul]
    abel
  have he := norm_add_le (c + star c) (c - star c)
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)] at he
  linarith

/-- A translation-radius bound characterizes centrality in a C*-algebra. -/
theorem central_of_translation_radius_bound (c : A) (C : ℝ)
    (h : ∀ x : A, (spectralRadius ℂ (c + x)).toReal ≤ (spectralRadius ℂ x).toReal + C) :
    Central c := by
  have hconj (u : Aˣ) : ‖(u : A) * c * (↑u⁻¹ : A)‖ ≤ 2 * C := by
    apply norm_le_of_translation_radius_bound _ C
    intro x
    have he : (u : A) * c * (↑u⁻¹ : A) + x =
        (u : A) * (c + (↑u⁻¹ : A) * x * u) * (↑u⁻¹ : A) := by
      simp only [mul_add, add_mul, mul_assoc, Units.mul_inv, Units.inv_mul, one_mul, mul_one]
      rw [← mul_assoc (u : A) (↑u⁻¹ : A) x, Units.mul_inv, one_mul]
    rw [he, radius_unit_conjugate]
    simpa only [radius_unit_conjugate'] using h ((↑u⁻¹ : A) * x * u)
  intro y
  let f : ℂ → A := fun z => NormedSpace.exp (z • y) * c * NormedSpace.exp ((-z) • y)
  have hd : Differentiable ℂ f := by
    apply Differentiable.mul
    · exact (differentiable_exp_smul_const ℂ y).mul_const c
    · simpa only [smul_neg, neg_smul] using differentiable_exp_smul_const ℂ (-y)
  have hb : Bornology.IsBounded (Set.range f) := by
    apply (isBounded_iff_forall_norm_le).2
    refine ⟨2*C, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hex : z • y ∈ Metric.eball (0 : A) (NormedSpace.expSeries ℂ A).radius := by
      rw [NormedSpace.expSeries_radius_eq_top, Metric.eball_top_eq_univ]
      exact Set.mem_univ _
    letI := NormedSpace.invertibleExpOfMemBall (𝕂 := ℂ) hex
    let u : Aˣ := unitOfInvertible (NormedSpace.exp (z • y))
    have hu : (u : A) = NormedSpace.exp (z • y) := rfl
    have hi : (↑u⁻¹ : A) = NormedSpace.exp ((-z) • y) := by
      change ⅟(NormedSpace.exp (z • y)) = _
      rw [NormedSpace.invOf_exp_of_mem_ball (𝕂 := ℂ) hex, neg_smul]
    simpa only [f, hi, hu] using hconj u
  have heq : f = fun _ => c := by
    funext z
    simpa [f] using hd.apply_eq_apply_of_bounded hb z 0
  have hd0 : HasDerivAt f (y*c-c*y) 0 := by
    have hpos := (hasDerivAt_exp_smul_const y (0:ℂ)).mul_const c
    have hneg := hasDerivAt_exp_smul_const (-y) (0:ℂ)
    simpa [f, sub_eq_add_neg, smul_neg, neg_smul] using hpos.fun_mul hneg
  have hz : y*c-c*y=0 := by
    rw [heq] at hd0
    exact hd0.unique (hasDerivAt_const (0:ℂ) c)
  exact (sub_eq_zero.mp hz).symm

variable {B : Type*} [CStarAlgebra B]

/-- Centers are preserved under the original onto/radius hypotheses. -/
theorem central_image (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) (z : A) (hz : Central z) : Central (T z) := by
  apply central_of_translation_radius_bound (T z) ‖z‖
  intro x
  obtain ⟨a, rfl⟩ := honto x
  rw [← map_add, hr, hr]
  simpa only [add_comm z a] using radius_add_le_radius_add_norm a z (hz a).symm

/-- The image of one is central without assuming T is unital. -/
theorem map_one_central (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) : Central (T 1) :=
  central_image T honto hr 1 (fun x => by rw [one_mul, mul_one])

end SpectralIsometry.Normalization

