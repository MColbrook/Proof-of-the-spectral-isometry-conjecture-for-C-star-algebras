module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.FunProp
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Basic

Definitions and algebraic, spectral and analytic estimates.
-/

@[expose] public section
noncomputable section

namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The spectral-radius condition, using Mathlib's extended nonnegative radius. -/
def PreservesRadius (T : A →ₗ[ℂ] B) : Prop :=
  ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a

/-- The algebraic Jordan conclusion intended in the source, without a star condition. -/
def IsJordanIsomorphism (T : A →ₗ[ℂ] B) : Prop :=
  Function.Bijective T ∧ ∀ a : A, T (a ^ 2) = (T a) ^ 2

theorem radius_star (a : A) : spectralRadius ℂ (star a) = spectralRadius ℂ a := by
  apply tendsto_nhds_unique
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (star a))
  simpa only [← star_pow, nnnorm_star] using
    spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a

/-- Source lines 71–75; neither unitality nor surjectivity is needed. -/
theorem injective_of_preservesRadius (T : A →ₗ[ℂ] B) (hT : PreservesRadius T) :
    Function.Injective T := by
  have hz : ∀ a : A, T a = 0 → a = 0 := by
    intro a ha
    have hra : spectralRadius ℂ a = 0 := by
      rw [← hT a, ha, spectrum.spectralRadius_zero]
    have hrs : spectralRadius ℂ (star a) = 0 := by rw [radius_star, hra]
    have hsum : a + star a = 0 := by
      have hs : IsSelfAdjoint (a + star a) := IsSelfAdjoint.add_star_self a
      have hr : spectralRadius ℂ (a + star a) = 0 := by
        rw [← hT (a + star a), map_add, ha, zero_add, hT (star a), hrs]
      have hn : ‖a + star a‖ = 0 := by
        simpa only [hr, ENNReal.toReal_zero] using hs.toReal_spectralRadius_complex_eq_norm.symm
      exact norm_eq_zero.mp hn
    have hstar : star a = -a := by
      calc
        star a = -a + (a + star a) := by abel
        _ = -a := by rw [hsum, add_zero]
    have : IsStarNormal a := ⟨by simp [hstar, Commute, SemiconjBy]⟩
    have hn : ‖a‖ = 0 := by
      have h := IsStarNormal.spectralRadius_eq_nnnorm a
      rw [hra] at h
      simpa using congrArg ENNReal.toReal h.symm
    exact norm_eq_zero.mp hn
  intro a b hab
  exact sub_eq_zero.mp (hz (a - b) (by simp [hab]))

/-- The first identity in the proof of the convex-hull lemma. -/
theorem translated_radius (T : A →ₗ[ℂ] B) (hT : PreservesRadius T)
    (h1 : T 1 = 1) (a : A) (z : ℂ) :
    spectralRadius ℂ (T a - algebraMap ℂ B z) =
      spectralRadius ℂ (a - algebraMap ℂ A z) := by
  simpa only [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h1] using
    hT (a - algebraMap ℂ A z)

/-- The algebraic square-zero approximant in source lines 200–204. -/
theorem square_zero_sandwich (e f y : A) (hfe : f * e = 0) :
    (e * y * f) ^ 2 = 0 := by
  calc
    (e * y * f) ^ 2 = e * y * (f * e) * y * f := by simp only [pow_two, mul_assoc]
    _ = 0 := by simp [hfe]

/-- The orthogonality calculation for the support projections, before taking supports. -/
theorem square_zero_support_product (n : A) (hn : n ^ 2 = 0) :
    (star n * n) * (n * star n) = 0 := by
  calc
    (star n * n) * (n * star n) = star n * (n ^ 2) * star n := by
      simp only [pow_two, mul_assoc]
    _ = 0 := by simp [hn]

/-- Source constants: K = ‖U⁻¹‖ ≥ 1, H = 2‖n‖K + K² ≥ 1. -/
theorem square_zero_constant_ge_one (N K : ℝ) (hN : 0 ≤ N) (hK : 1 ≤ K) :
    1 ≤ 2 * N * K + K ^ 2 := by nlinarith

/-- Exact real arithmetic in the perturbation estimate; no numerical execution. -/
theorem square_zero_perturbation_bound (N K e h : ℝ)
    (hN : 0 ≤ N) (_hK : 0 ≤ K) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hh0 : 0 ≤ h) (hh : h ≤ K * e) :
    2 * N * h + h ^ 2 ≤ (2 * N * K + K ^ 2) * e := by
  have hsq : h ^ 2 ≤ (K * e) ^ 2 := by nlinarith
  have he2 : e ^ 2 ≤ e := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left he2 (sq_nonneg K)
  nlinarith

/-- Polarization in source lines 353–355. -/
theorem selfadjoint_jordan_product (T : A →ₗ[ℂ] B)
    (hs : ∀ h : A, IsSelfAdjoint h → T (h ^ 2) = (T h) ^ 2)
    (h k : A) (hh : IsSelfAdjoint h) (hk : IsSelfAdjoint k) :
    T (h * k + k * h) = T h * T k + T k * T h := by
  calc
    T (h * k + k * h) = T ((h + k) ^ 2 - h ^ 2 - k ^ 2) := by
      congr 1
      noncomm_ring
    _ = (T (h + k)) ^ 2 - (T h) ^ 2 - (T k) ^ 2 := by
      rw [map_sub, map_sub, hs (h + k) (hh.add hk), hs h hh, hs k hk]
    _ = T h * T k + T k * T h := by rw [map_add]; noncomm_ring

/-- The final extension from self-adjoint elements to all elements, source 357–363. -/
theorem squares_of_selfadjoint_squares (T : A →ₗ[ℂ] B)
    (hs : ∀ h : A, IsSelfAdjoint h → T (h ^ 2) = (T h) ^ 2) :
    ∀ a : A, T (a ^ 2) = (T a) ^ 2 := by
  intro a
  let h : A := (realPart a : A)
  let k : A := (imaginaryPart a : A)
  have hh : IsSelfAdjoint h := (realPart a).property
  have hk : IsSelfAdjoint k := (imaginaryPart a).property
  have ha : a = h + Complex.I • k := (realPart_add_I_smul_imaginaryPart a).symm
  have hexp (x y : A) : (x + Complex.I • y) ^ 2 =
      x ^ 2 - y ^ 2 + Complex.I • (x * y + y * x) := by
    simp [pow_two, mul_add, add_mul, smul_add,
      smul_smul, Complex.I_mul_I, sub_eq_add_neg]
    abel
  have hexpB (x y : B) : (x + Complex.I • y) ^ 2 =
      x ^ 2 - y ^ 2 + Complex.I • (x * y + y * x) := by
    simp [pow_two, mul_add, add_mul, smul_add,
      smul_smul, Complex.I_mul_I, sub_eq_add_neg]
    abel
  rw [ha, hexp, map_add, map_sub, map_smul, hs h hh, hs k hk,
    selfadjoint_jordan_product T hs h k hh hk, map_add, map_smul, hexpB]

/-- Source 336: the algebraic reason kernels of derivations are subalgebras. -/
theorem derivation_kernel_mul (δ : B →ₗ[ℂ] B)
    (hδ : ∀ x y : B, δ (x * y) = δ x * y + x * δ y)
    (a b : B) (ha : δ a = 0) (hb : δ b = 0) : δ (a * b) = 0 := by
  simp [hδ, ha, hb]

end SpectralIsometry

/- Algebraic trace components, prepared by a separate AI subagent. -/
namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The algebraic finite-quotient trace step in source lines 280--285. -/
theorem square_preserving_of_trace_pairings (K : A →ₗ[ℂ] B)
    (honto : Function.Surjective K) (traces : Set (B →ₗ[ℂ] ℂ))
    (hsep : ∀ d : B, (∀ τ ∈ traces, τ (star d * d) = 0) → d = 0)
    (hpair : ∀ τ ∈ traces, ∀ a b : A,
      τ (K a * K (b ^ 2)) = τ (K a * (K b) ^ 2)) :
    ∀ b : A, K (b ^ 2) = (K b) ^ 2 := by
  intro b
  apply sub_eq_zero.mp
  apply hsep
  intro τ hτ
  obtain ⟨a, ha⟩ := honto (star (K (b ^ 2) - (K b) ^ 2))
  rw [← ha, mul_sub, map_sub, hpair τ hτ a b, sub_self]

/-- Quadratic trace polarization, source line 259, with all hypotheses explicit. -/
theorem trace_quadratic_polarization (K : A →ₗ[ℂ] B)
    (σ : A →ₗ[ℂ] ℂ) (τ : B →ₗ[ℂ] ℂ)
    (hσ : ∀ a b : A, σ (a * b) = σ (b * a))
    (hτ : ∀ a b : B, τ (a * b) = τ (b * a))
    (hmoment : ∀ a : A, τ ((K a) ^ 2) = σ (a ^ 2)) :
    ∀ a b : A, τ (K a * K b) = σ (a * b) := by
  intro a b
  have hp := hmoment (a + b)
  have ha := hmoment a
  have hb := hmoment b
  have hsa := hσ a b
  have htb := hτ (K a) (K b)
  simp only [map_add, pow_two, add_mul, mul_add] at hp ha hb
  linear_combination (hp - ha - hb + htb - hsa) / 2

/-- Cubic trace polarization, source line 260. Only the cubic moments are needed. -/
theorem trace_cubic_polarization (K : A →ₗ[ℂ] B)
    (σ : A →ₗ[ℂ] ℂ) (τ : B →ₗ[ℂ] ℂ)
    (hσ : ∀ a b : A, σ (a * b) = σ (b * a))
    (hτ : ∀ a b : B, τ (a * b) = τ (b * a))
    (hmoment : ∀ a : A, τ ((K a) ^ 3) = σ (a ^ 3)) :
    ∀ a b : A, τ (K a * (K b) ^ 2) = σ (a * b ^ 2) := by
  intro a b
  have hp := hmoment (b + a)
  have hm := hmoment (b - a)
  have ha := hmoment a
  have hs1 := hσ (b * b) a
  have hs2 := hσ b (a * b)
  have ht1 := hτ (K b * K b) (K a)
  have ht2 := hτ (K b) (K a * K b)
  simp only [map_add, map_sub, pow_succ, pow_zero, one_mul,
    add_mul, mul_add, sub_mul, mul_sub, mul_assoc] at hp hm ha
  simp only [mul_assoc] at hs1 hs2 ht1 ht2
  simp only [pow_two]
  linear_combination (hp - hm - 2 * ha - 2 * ht1 - 2 * ht2 + 2 * hs1 + 2 * hs2) / 6

end SpectralIsometry

namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The real-spectrum consequence of the source's convex-hull lemma.
This argument uses translated spectral radii and attainment of the spectral radius,
without requiring surjectivity or continuity of the linear map. -/
theorem selfadjoint_image_real_spectrum (T : A →ₗ[ℂ] B)
    (hT : PreservesRadius T) (h1 : T 1 = 1) (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z ∈ spectrum ℂ (T a)) : z.im = 0 := by
  have : Nontrivial B := by
    rcases subsingleton_or_nontrivial B with hB | hB
    · have := hB
      simp [spectrum.of_subsingleton] at hz
    · exact hB
  have : Nontrivial A := ⟨⟨1, 0, fun h => one_ne_zero (by rw [← h1, h, map_zero])⟩⟩
  have hineq (t : ℝ) : z.re ^ 2 + (z.im - t) ^ 2 ≤ ‖a‖ ^ 2 + t ^ 2 := by
    let c : ℂ := Complex.I * t
    have hz' : z - c ∈ spectrum ℂ (T a - algebraMap ℂ B c) := by
      rw [← spectrum.sub_singleton_eq]
      exact Set.sub_mem_sub hz (Set.mem_singleton c)
    obtain ⟨w, hw, hwr⟩ := spectrum.exists_nnnorm_eq_spectralRadius
      (a - algebraMap ℂ A c)
    have hrad : (‖z - c‖₊ : ENNReal) ≤ (‖w‖₊ : ENNReal) := by
      rw [hwr, ← translated_radius T hT h1 a c, spectralRadius_eq_of_unital]
      apply le_iSup_of_le (z - c)
      exact le_iSup_of_le hz' le_rfl
    have hnorm : ‖z - c‖ ≤ ‖w‖ := by exact_mod_cast hrad
    have hw' : w + c ∈ spectrum ℂ a := by
      rw [← spectrum.sub_singleton_eq] at hw
      obtain ⟨v, hv, u, hu, hvu⟩ := hw
      have hu' : u = c := Set.mem_singleton_iff.mp hu
      subst u
      have heq : w + c = v := by rw [← hvu]; exact sub_add_cancel v c
      rw [heq]
      exact hv
    have hwim : w.im = -t := by
      have h := ha.im_eq_zero_of_mem_spectrum hw'
      simp [c] at h
      linarith
    have hwre : w.re ^ 2 ≤ ‖a‖ ^ 2 := by
      have hn := spectrum.norm_le_norm_of_mem hw'
      have hr : ‖(w + c)‖ ^ 2 = w.re ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, c, hwim, sq]
      nlinarith [norm_nonneg (w + c), norm_nonneg a]
    have hn2 : ‖z - c‖ ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [norm_nonneg (z - c)]
    simp only [Complex.sq_norm, Complex.normSq_apply] at hn2
    simp [c, hwim] at hn2
    nlinarith
  by_contra hzi
  have h := hineq ((‖a‖ ^ 2 + 1) / (-2 * z.im))
  have hid : 2 * ((‖a‖ ^ 2 + 1) / (-2 * z.im)) * z.im = -(‖a‖ ^ 2 + 1) := by
    field_simp [hzi]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

end SpectralIsometry

namespace SpectralIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def finiteBarycenters (K : Set E) (n : ℕ) : Set E :=
  (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
    ((stdSimplex ℝ (Fin n)) ×ˢ (Set.univ.pi fun _ : Fin n => K))

private theorem isCompact_finiteBarycenters (K : Set E) (hK : IsCompact K) (n : ℕ) :
    IsCompact (finiteBarycenters K n) := by
  apply IsCompact.image
    ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ => hK))
  fun_prop

/-- Compactness of a convex hull in finite dimension, from Carathéodory's theorem. -/
private theorem compact_convexHull [FiniteDimensional ℝ E] (K : Set E) (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  classical
  have heq : convexHull ℝ K =
      ⋃ n : Fin (Module.finrank ℝ E + 2), finiteBarycenters K n.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨ι, inst, z, w, hz, hind, hw, hsum, hbar⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      let := inst
      have hcard := hind.card_le_finrank_succ
      have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      have hn : Fintype.card ι < Module.finrank ℝ E + 2 := by omega
      let n : Fin (Module.finrank ℝ E + 2) := ⟨Fintype.card ι, hn⟩
      let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      refine ⟨(w ∘ e, z ∘ e), ?_, ?_⟩
      · refine ⟨⟨fun i => (hw (e i)).le, ?_⟩, ?_⟩
        · change (∑ i : Fin (Fintype.card ι), w (e i)) = 1
          exact (e.sum_comp w).trans hsum
        · exact fun i _ => hz ⟨e i, rfl⟩
      · change (∑ i : Fin (Fintype.card ι), w (e i) • z (e i)) = x
        exact (e.sum_comp (fun i => w i • z i)).trans hbar
    · intro hx
      obtain ⟨n, ⟨p, hp, rfl⟩⟩ := Set.mem_iUnion.mp hx
      exact mem_convexHull_of_exists_fintype p.1 p.2 hp.1.1 hp.1.2
        (fun i => hp.2 i (Set.mem_univ i)) rfl
  rw [heq]
  exact isCompact_iUnion fun n => isCompact_finiteBarycenters K hK n.val

end SpectralIsometry

namespace SpectralIsometry

private theorem real_functional_coordinates (f : ℂ →L[ℝ] ℝ) (z : ℂ) :
    f z = z.re * f 1 + z.im * f Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    f z = f (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg f hz
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

private theorem spectrum_subset_closedHull_of_translated_radius
    [Nontrivial A] [Nontrivial B] (a : A) (b : B)
    (h : ∀ c : ℂ, spectralRadius ℂ (b - algebraMap ℂ B c) =
      spectralRadius ℂ (a - algebraMap ℂ A c)) :
    spectrum ℂ b ⊆ closedConvexHull ℝ (spectrum ℂ a) := by
  intro z hz
  by_contra hout
  obtain ⟨f, u, hfu, huz⟩ := geometric_hahn_banach_closed_point
    (convex_closedConvexHull (𝕜 := ℝ)) isClosed_closedConvexHull hout
  let t : ℝ := (‖a‖ ^ 2 + 1) / (2 * (f z - u))
  have ht : 0 < t := by dsimp [t]; positivity
  let c : ℂ := -(t : ℂ) * ((f 1 : ℂ) + (f Complex.I : ℂ) * Complex.I)
  have hz' : z - c ∈ spectrum ℂ (b - algebraMap ℂ B c) := by
    rw [← spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub hz (Set.mem_singleton c)
  obtain ⟨v, hv, hvr⟩ := spectrum.exists_nnnorm_eq_spectralRadius
    (a - algebraMap ℂ A c)
  have hrad : (‖z - c‖₊ : ENNReal) ≤ (‖v‖₊ : ENNReal) := by
    rw [hvr, ← h c, spectralRadius_eq_of_unital]
    exact le_iSup_of_le (z - c) (le_iSup_of_le hz' le_rfl)
  have hnorm : ‖z - c‖ ≤ ‖v‖ := by exact_mod_cast hrad
  let w : ℂ := v + c
  have hw : w ∈ spectrum ℂ a := by
    rw [← spectrum.sub_singleton_eq] at hv
    obtain ⟨x, hx, y, hy, hxy⟩ := hv
    have hy' : y = c := Set.mem_singleton_iff.mp hy
    subst y
    have hwx : w = x := by dsimp [w]; rw [← hxy]; exact sub_add_cancel x c
    rw [hwx]
    exact hx
  have hnorm' : ‖z - c‖ ^ 2 ≤ ‖w - c‖ ^ 2 := by
    have hvc : w - c = v := add_sub_cancel_right v c
    rw [hvc]
    nlinarith [norm_nonneg (z - c)]
  have hwbound : w.re ^ 2 + w.im ^ 2 ≤ ‖a‖ ^ 2 := by
    have hn := spectrum.norm_le_norm_of_mem hw
    have hn2 : ‖w‖ ^ 2 ≤ ‖a‖ ^ 2 := by nlinarith [norm_nonneg w]
    rw [Complex.sq_norm, Complex.normSq_apply] at hn2
    nlinarith only [hn2]
  have hfw : f w ≤ u := le_of_lt (hfu w (subset_closedConvexHull hw))
  have htw : 2 * t * f w ≤ 2 * t * u :=
    mul_le_mul_of_nonneg_left hfw (by positivity)
  have hcoords := real_functional_coordinates f z
  have hwcoords := real_functional_coordinates f w
  have hid : 2 * t * (f z - u) = ‖a‖ ^ 2 + 1 := by
    dsimp [t]
    field_simp [ne_of_gt (sub_pos.mpr huz)]
  simp [c, Complex.sq_norm, Complex.normSq_apply] at hnorm'
  rw [hcoords] at hid
  rw [hwcoords] at htw
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- Closed convex hull preservation, a step toward the source convex hull lemma. -/
private theorem closed_spectral_hull (T : A →ₗ[ℂ] B)
    (hT : PreservesRadius T) (h1 : T 1 = 1) (a : A) :
    closedConvexHull ℝ (spectrum ℂ (T a)) = closedConvexHull ℝ (spectrum ℂ a) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · have : Subsingleton A := by
      apply (injective_of_preservesRadius T hT).subsingleton
    simp [spectrum.of_subsingleton, closedConvexHull]
  · have : Nontrivial A := ⟨⟨1, 0, fun h => one_ne_zero (by rw [← h1, h, map_zero])⟩⟩
    have hf := spectrum_subset_closedHull_of_translated_radius a (T a)
      (translated_radius T hT h1 a)
    have hg := spectrum_subset_closedHull_of_translated_radius (T a) a
      (fun c => (translated_radius T hT h1 a c).symm)
    exact Set.Subset.antisymm
      (closedConvexHull_min hf convex_closedConvexHull isClosed_closedConvexHull)
      (closedConvexHull_min hg convex_closedConvexHull isClosed_closedConvexHull)

/-- The full convex-hull equality in the source's Lemma 3.1. -/
theorem spectral_hull (T : A →ₗ[ℂ] B)
    (hT : PreservesRadius T) (h1 : T 1 = 1) (a : A) :
    convexHull ℝ (spectrum ℂ (T a)) = convexHull ℝ (spectrum ℂ a) := by
  have ha := (compact_convexHull (spectrum ℂ a) (spectrum.isCompact a)).isClosed
  have hb := (compact_convexHull (spectrum ℂ (T a)) (spectrum.isCompact (T a))).isClosed
  have h := closed_spectral_hull T hT h1 a
  simpa only [closedConvexHull_eq_closure_convexHull, ha.closure_eq, hb.closure_eq] using h

end SpectralIsometry

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

/-- The self-adjoint resolvent estimate used in the source's strip argument. -/
private theorem selfadjoint_inverse_shift_norm (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) (u : Aˣ)
    (hu : (u : A) = a - algebraMap ℂ A z) :
    ‖(↑u⁻¹ : A)‖ ≤ |z.im|⁻¹ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have hzero : (↑u⁻¹ : A) = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    positivity
  · have : IsStarNormal a := ha.isStarNormal
    have : IsStarNormal (algebraMap ℂ A z) := by
      rw [Algebra.algebraMap_eq_smul_one]
      infer_instance
    have hc : Commute a (star (algebraMap ℂ A z)) := by
      simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
      exact (Commute.one_right a).smul_right (star z)
    have : IsStarNormal (a - algebraMap ℂ A z) := hc.isStarNormal_sub
    have : IsStarNormal (u : A) := by rw [hu]; infer_instance
    obtain ⟨w, hw, hwr⟩ := spectrum.exists_nnnorm_eq_spectralRadius (↑u⁻¹ : A)
    have hnorm : ‖w‖ = ‖(↑u⁻¹ : A)‖ := by
      rw [IsStarNormal.spectralRadius_eq_nnnorm] at hwr
      have he : ‖w‖₊ = ‖(↑u⁻¹ : A)‖₊ := by exact_mod_cast hwr
      exact congrArg (fun x : NNReal => (x : ℝ)) he
    have hw' : w⁻¹ ∈ spectrum ℂ (u : A) := spectrum.inv₀_mem_iff.mpr hw
    rw [hu, ← spectrum.sub_singleton_eq] at hw'
    obtain ⟨v, hv, c, hc, hvc⟩ := hw'
    have hc' : c = z := Set.mem_singleton_iff.mp hc
    subst c
    have him : (w⁻¹).im = -z.im := by
      have hvim := ha.im_eq_zero_of_mem_spectrum hv
      rw [← hvc]
      simp [hvim]
    have hi : |z.im| ≤ ‖w‖⁻¹ := by
      simpa only [him, abs_neg, norm_inv] using Complex.abs_im_le_norm (w⁻¹)
    rw [← hnorm]
    exact le_inv_of_le_inv₀ (abs_pos.mpr hz) hi

/-- The full self-adjoint spectral-strip estimate used in source line 146. -/
theorem selfadjoint_perturbation_spectral_strip (a h : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z ∈ spectrum ℂ (a + h)) : |z.im| ≤ ‖h‖ := by
  have : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with hA | hA
    · simp [spectrum.of_subsingleton] at hz
    · exact hA
  by_contra hfail
  have hsmall : ‖h‖ < |z.im| := lt_of_not_ge hfail
  have hzi : z.im ≠ 0 := abs_pos.mp ((norm_nonneg h).trans_lt hsmall)
  have hout : z ∉ spectrum ℂ a := fun hza => hzi (ha.im_eq_zero_of_mem_spectrum hza)
  have hunit : IsUnit (algebraMap ℂ A z - a) := by
    by_contra hnu
    exact hout (spectrum.mem_iff.mpr hnu)
  have hunit' : IsUnit (a - algebraMap ℂ A z) := by
    simpa only [neg_sub] using hunit.neg
  obtain ⟨u, hu⟩ := hunit'
  have hnorm := selfadjoint_inverse_shift_norm a ha z hzi u hu
  have hthreshold : |z.im| ≤ ‖(↑u⁻¹ : A)‖⁻¹ :=
    le_inv_of_le_inv₀ (Units.norm_pos u⁻¹) hnorm
  have hpert : IsUnit (a + h - algebraMap ℂ A z) := by
    have hp := (u.add h (hsmall.trans_le hthreshold)).isUnit
    convert hp using 1
    change a + h - algebraMap ℂ A z = (u : A) + h
    rw [hu]
    abel
  apply (spectrum.mem_iff.mp hz)
  convert hpert.neg using 1; abel

end SpectralIsometry

namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Unital radius preservation transfers the full perturbation strip to the image. -/
theorem selfadjoint_image_perturbation_strip (T : A →ₗ[ℂ] B)
    (hT : PreservesRadius T) (h1 : T 1 = 1) (a h : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z ∈ spectrum ℂ (T (a + h))) : |z.im| ≤ ‖h‖ := by
  have hs : Convex ℝ {w : ℂ | |w.im| ≤ ‖h‖} := by
    simpa only [abs_le, Set.ofPred_and] using
      (convex_halfSpace_im_ge (-‖h‖)).inter (convex_halfSpace_im_le ‖h‖)
  have hh : convexHull ℝ (spectrum ℂ (a + h)) ⊆ {w : ℂ | |w.im| ≤ ‖h‖} :=
    convexHull_min (fun w hw => selfadjoint_perturbation_spectral_strip a h ha w hw) hs
  apply hh
  rw [← spectral_hull T hT h1 (a + h)]
  exact subset_convexHull ℝ (spectrum ℂ (T (a + h))) hz

end SpectralIsometry

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- A nearest nonunit to a unit, using its inverse rather than polar decomposition. -/
private theorem exists_nonunit_at_inverse_norm (u : Aˣ) :
    ∃ b : A, ¬IsUnit b ∧ ‖(u : A) - b‖ = ‖(↑u⁻¹ : A)‖⁻¹ := by
  let x : A := ↑u⁻¹
  let v : A := star x * x
  let N : ℝ := ‖x‖ ^ 2
  let r : ℝ := N⁻¹
  have hxpos : 0 < ‖x‖ := Units.norm_pos u⁻¹
  have hNpos : 0 < N := pow_pos hxpos 2
  have hN0 : N ≠ 0 := ne_of_gt hNpos
  have hnorm : ‖v‖ = N := by
    dsimp [v, N]
    rw [CStarRing.norm_star_mul_self, pow_two]
  have hmem : N ∈ spectrum ℝ v := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum v (IsSelfAdjoint.star_mul_self x) with hp | hn
    · simpa only [hnorm] using hp
    · have hnegative := spectrum_star_mul_self_nonneg (-‖v‖) hn
      rw [hnorm] at hnegative
      exfalso
      linarith
  have hnon : ¬IsUnit (algebraMap ℝ A N - v) := spectrum.mem_iff.mp hmem
  have hfactor : N • (1 - r • v) = algebraMap ℝ A N - v := by
    rw [smul_sub, smul_smul]
    simp [r, hN0, Algebra.algebraMap_eq_smul_one]
  have hbad : ¬IsUnit (1 - r • v) := by
    intro hs
    have hscalar : IsUnit (algebraMap ℝ A N) :=
      (isUnit_iff_ne_zero.mpr hN0).map (algebraMap ℝ A)
    have hh := hscalar.mul hs
    rw [← Algebra.smul_def, hfactor] at hh
    exact hnon hh
  let b : A := (u : A) - r • star x
  have hbeq : b = (1 - r • v) * (u : A) := by
    dsimp [b, v, x]
    simp only [sub_mul, one_mul, smul_mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  have hb : ¬IsUnit b := by
    intro hb
    have hh := hb.mul (u⁻¹).isUnit
    rw [hbeq, mul_assoc, Units.mul_inv, mul_one] at hh
    exact hbad hh
  refine ⟨b, hb, ?_⟩
  have hrpos : 0 < r := inv_pos.mpr hNpos
  have hnormdiff : ‖(u : A) - b‖ = r * ‖x‖ := by
    calc
      ‖(u : A) - b‖ = ‖r • star x‖ := by congr 1; dsimp [b]; abel
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, norm_star]
  rw [hnormdiff]
  change (‖x‖ ^ 2)⁻¹ * ‖x‖ = ‖x‖⁻¹
  field_simp [ne_of_gt hxpos]

/-- The exact distance formula in source Lemma 2.2, in its nonzero-algebra context. -/
private theorem distance_unit_to_nonunits (u : Aˣ) :
    Metric.infDist (u : A) {b : A | ¬IsUnit b} = ‖(↑u⁻¹ : A)‖⁻¹ := by
  obtain ⟨b, hb, hn⟩ := exists_nonunit_at_inverse_norm u
  apply le_antisymm
  · calc
      Metric.infDist (u : A) {c : A | ¬IsUnit c} ≤ dist (u : A) b :=
        Metric.infDist_le_dist_of_mem hb
      _ = _ := by rw [dist_eq_norm, hn]
  · apply (Metric.le_infDist ⟨b, hb⟩).mpr
    intro c hc
    by_contra hfail
    have hnear : ‖c - (u : A)‖ < ‖(↑u⁻¹ : A)‖⁻¹ := by
      rw [← dist_eq_norm, dist_comm]
      exact lt_of_not_ge hfail
    exact hc (u.ofNearby c hnear).isUnit

/-- Source Lemma 2.2 with an element and its original invertibility hypothesis. -/
theorem distance_to_nonunits (c : A) (hc : IsUnit c) :
    Metric.infDist c {b : A | ¬IsUnit b} = ‖Ring.inverse c‖⁻¹ := by
  obtain ⟨u, rfl⟩ := hc
  simpa only [Ring.inverse_unit] using distance_unit_to_nonunits u

end SpectralIsometry

namespace SpectralIsometry.JordanAlgebra

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]

private theorem jordan_product (T : A →ₗ[ℂ] B)
    (hs : ∀ a : A, T (a ^ 2) = (T a) ^ 2) (a b : A) :
    T (a * b + b * a) = T a * T b + T b * T a := by
  have hp := hs (a + b)
  have hd : (a + b) ^ 2 = a ^ 2 + (a * b + b * a) + b ^ 2 := by noncomm_ring
  have hc : (T a + T b) ^ 2 = (T a) ^ 2 + (T a * T b + T b * T a) + (T b) ^ 2 := by
    noncomm_ring
  rw [hd, map_add, map_add, hs a, hs b] at hp
  conv_rhs at hp => rw [map_add, hc]
  exact add_left_cancel (add_right_cancel hp)

private theorem jordan_triple (T : A →ₗ[ℂ] B)
    (hs : ∀ a : A, T (a ^ 2) = (T a) ^ 2) (a b : A) :
    T (a * b * a) = T a * T b * T a := by
  have hp := jordan_product T hs a (a * b + b * a)
  have hq := jordan_product T hs (a ^ 2) b
  rw [jordan_product T hs a b] at hp
  rw [hs a] at hq
  have hd : a * (a * b + b * a) + (a * b + b * a) * a =
      (a ^ 2 * b + b * a ^ 2) + (2 : ℂ) • (a * b * a) := by
    simp only [two_smul]
    noncomm_ring
  have hc : T a * (T a * T b + T b * T a) + (T a * T b + T b * T a) * T a =
      ((T a) ^ 2 * T b + T b * (T a) ^ 2) + (2 : ℂ) • (T a * T b * T a) := by
    simp only [two_smul]
    noncomm_ring
  rw [hd, map_add, map_smul, hq, hc] at hp
  have hm : (2 : ℂ) • T (a * b * a) = (2 : ℂ) • (T a * T b * T a) :=
    add_left_cancel hp
  have hz : (2 : ℂ) • (T (a * b * a) - T a * T b * T a) = 0 := by
    rw [smul_sub, hm, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))

private theorem isUnit_of_jordan_inverse (x y : B)
    (hs : x * y + y * x = 1 + 1) (ht : x * y * x = x) : IsUnit x := by
  let p := x * y
  let q := y * x
  have hp : p ^ 2 = p := by
    dsimp [p]
    calc
      (x * y) ^ 2 = (x * y * x) * y := by noncomm_ring
      _ = x * y := by rw [ht]
  have hq : q ^ 2 = q := by
    dsimp [q]
    calc
      (y * x) ^ 2 = y * (x * y * x) := by noncomm_ring
      _ = y * x := by rw [ht]
  have hsum : p + q = 1 + 1 := hs
  have hqeq : q = 1 + 1 - p := by rw [← hsum]; abel
  have hz : (2 : ℂ) • (p - 1) = 0 := by
    calc
      (2 : ℂ) • (p - 1) = (p ^ 2 - p) - (q ^ 2 - q) := by
        rw [hqeq]
        simp only [two_smul]
        noncomm_ring
      _ = 0 := by rw [hp, hq]; simp
  have hp1 : p = 1 := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  have hq1 : q = 1 := by
    have hh : 1 + q = 1 + 1 := by simpa only [hp1] using hsum
    exact add_left_cancel hh
  exact ⟨⟨x, y, hp1, hq1⟩, rfl⟩

private theorem isUnit_map (T : A →ₗ[ℂ] B) (h1 : T 1 = 1)
    (hs : ∀ a : A, T (a ^ 2) = (T a) ^ 2) (a : A) (ha : IsUnit a) : IsUnit (T a) := by
  obtain ⟨u, rfl⟩ := ha
  apply isUnit_of_jordan_inverse (T (u : A)) (T (↑u⁻¹ : A))
  · have h := jordan_product T hs (u : A) (↑u⁻¹ : A)
    simpa only [Units.mul_inv, Units.inv_mul, map_add, h1] using h.symm
  · have h := jordan_triple T hs (u : A) (↑u⁻¹ : A)
    simpa only [Units.mul_inv, one_mul] using h.symm

/-- Algebraic spectrum preservation; no norm, star or completeness is needed. -/
private theorem spectrum_eq (T : A →ₗ[ℂ] B) (h1 : T 1 = 1) (hbij : Function.Bijective T)
    (hs : ∀ a : A, T (a ^ 2) = (T a) ^ 2) (a : A) :
    spectrum ℂ (T a) = spectrum ℂ a := by
  let e : A ≃ₗ[ℂ] B := LinearEquiv.ofBijective T hbij
  have he (b : B) : T (e.symm b) = b := e.apply_symm_apply b
  have h1inv : e.symm 1 = 1 := hbij.1 (by rw [he, h1])
  have hsinv (b : B) : e.symm (b ^ 2) = (e.symm b) ^ 2 := by
    apply hbij.1
    rw [he, hs, he]
  have hunit (c : A) : IsUnit (T c) ↔ IsUnit c := by
    constructor
    · intro hc
      have hi := isUnit_map e.symm.toLinearMap h1inv hsinv (T c) hc
      change IsUnit (e.symm (e c)) at hi
      simpa only [LinearEquiv.symm_apply_apply] using hi
    · exact isUnit_map T h1 hs c
  ext z
  rw [spectrum.mem_iff, spectrum.mem_iff]
  apply not_congr
  have hz : T (algebraMap ℂ A z - a) = algebraMap ℂ B z - T a := by
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h1,
      ← Algebra.algebraMap_eq_smul_one]
  rw [← hz]
  exact hunit (algebraMap ℂ A z - a)

end SpectralIsometry.JordanAlgebra

namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The Jordan spectrum-preservation step used in source line 301. -/
theorem jordan_isomorphism_spectrum (T : A →ₗ[ℂ] B) (h1 : T 1 = 1)
    (hJ : IsJordanIsomorphism T) (a : A) : spectrum ℂ (T a) = spectrum ℂ a :=
  JordanAlgebra.spectrum_eq T h1 hJ.1 hJ.2 a

end SpectralIsometry

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

/-- The norm-holomorphic self-adjoint-valued functions used in the entire-group proof
are constant (source lines292–294 and304). -/
theorem holomorphic_selfadjoint_const (f : ℂ → A) (hf : Differentiable ℂ f)
    (hsa : ∀ z : ℂ, IsSelfAdjoint (f z)) (z w : ℂ) : f z = f w := by
  have hstar : (fun v : ℂ => star (f v)) = f := funext fun v => (hsa v).star_eq
  have hder (v : ℂ) : deriv f v = 0 := by
    let D := fderiv ℂ f v
    have hd : HasFDerivAt f (D.restrictScalars ℝ) v :=
      (hf v).hasFDerivAt.restrictScalars ℝ
    have hsd := hd.star
    rw [hstar] at hsd
    have he := hsd.unique hd
    have hval (c : ℂ) : star (D c) = D c := by
      exact congrArg (fun L : ℂ →L[ℝ] A => L c) he
    have hDI : D Complex.I = Complex.I • D 1 := by
      calc
        D Complex.I = D (Complex.I • (1 : ℂ)) := by simp
        _ = Complex.I • D 1 := D.map_smul _ _
    have hi : -(Complex.I • D 1) = Complex.I • D 1 := by
      simpa [hDI, star_smul, hval 1] using hval Complex.I
    have htwo : (2 : ℂ) • (Complex.I • D 1) = 0 := by
      have hh := congrArg (fun a : A => a + Complex.I • D 1) hi
      simpa only [neg_add_cancel, two_smul] using hh.symm
    have hI0 : Complex.I • D 1 = 0 :=
      (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hD0 : D 1 = 0 := (smul_eq_zero.mp hI0).resolve_left Complex.I_ne_zero
    exact hD0
  exact is_const_of_deriv_eq_zero hf hder z w

end SpectralIsometry

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

/-- Real spectrum forces self-adjointness for a normal element, source line290. -/
theorem normal_real_spectrum_selfadjoint (c : A) [IsStarNormal c]
    (hreal : ∀ z ∈ spectrum ℂ c, z.im = 0) : IsSelfAdjoint c := by
  have hq : QuasispectrumRestricts c Complex.reCLM := by
    refine ⟨?_, Complex.ofReal_re⟩
    intro z hz
    rcases mem_quasispectrum_iff.mp hz with hz | hz
    · simp [hz]
    · apply Complex.ext
      · rfl
      · exact (hreal z hz).symm
  exact hq.isSelfAdjoint c

/-- The spectral test in the entire-group off-diagonal argument, source line305. -/
theorem selfadjoint_of_real_spectrum_shifts (c : A)
    (hreal : ∀ a : A, IsSelfAdjoint a → ∀ z ∈ spectrum ℂ (a + c), z.im = 0) :
    IsSelfAdjoint c := by
  let s : selfAdjoint A := selfAdjointPart ℝ c
  let k : skewAdjoint A := skewAdjointPart ℝ c
  have hsum : (s : A) + (k : A) = c := StarModule.selfAdjointPart_add_skewAdjointPart ℝ c
  have he : -(s : A) + c = (k : A) := by rw [← hsum]; simp
  have hkr : ∀ z ∈ spectrum ℂ (k : A), z.im = 0 := by
    intro z hz
    apply hreal (-(s : A)) s.property.neg z
    rw [he]
    exact hz
  have hk : star (k : A) = -(k : A) := k.property
  letI : IsStarNormal (k : A) := ⟨by
    change star (k : A) * (k : A) = (k : A) * star (k : A)
    rw [hk]
    simp only [neg_mul, mul_neg]⟩
  have hksa : IsSelfAdjoint (k : A) := normal_real_spectrum_selfadjoint _ hkr
  have hkn : (k : A) = -(k : A) := hksa.star_eq.symm.trans hk
  have hzero : (k : A) = 0 := by
    have ht : (2 : ℂ) • (k : A) = 0 := by
      have hh := congrArg (fun x : A => x + (k : A)) hkn
      simpa only [neg_add_cancel, two_smul] using hh
    exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
  have hc : c = (s : A) := by rw [← hsum, hzero, add_zero]
  rw [hc]
  exact s.property

end SpectralIsometry

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

/-- Source normalization: a central element with spectrum on the unit circle is
unitary. This does not establish those hypotheses for T(1). -/
theorem central_spectrum_circle_unitary (u : A) (hcentral : ∀ b : A, Commute u b)
    (hcircle : spectrum ℂ u ⊆ unitary ℂ) : u ∈ unitary A := by
  letI : IsStarNormal u := ⟨(hcentral (star u)).symm⟩
  exact mem_unitary_of_spectrum_subset_unitary hcircle

end SpectralIsometry

namespace SpectralIsometry

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

private theorem spectralRadius_exp_conjugate (y w : E) (z : ℂ) :
    spectralRadius ℂ (NormedSpace.exp (z • y) * w * NormedSpace.exp ((-z) • y)) =
      spectralRadius ℂ w := by
  have hex : z • y ∈ Metric.eball (0 : E) (NormedSpace.expSeries ℂ E).radius := by
    rw [NormedSpace.expSeries_radius_eq_top, Metric.eball_top_eq_univ]
    exact Set.mem_univ _
  letI := NormedSpace.invertibleExpOfMemBall (𝕂 := ℂ) hex
  let u : Eˣ := unitOfInvertible (NormedSpace.exp (z • y))
  have hu : (u : E) = NormedSpace.exp (z • y) := rfl
  have hi : (↑u⁻¹ : E) = NormedSpace.exp ((-z) • y) := by
    change ⅟(NormedSpace.exp (z • y)) = _
    rw [NormedSpace.invOf_exp_of_mem_ball (𝕂 := ℂ) hex, neg_smul]
  have hs := spectrum.units_conjugate (R := ℂ) (a := w) (u := u)
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital]
  rw [hu, hi] at hs
  rw [hs]

/-- Source lines 338–349: the displayed uniform norm-radius bound forces commutativity.
This is an intermediate result whose bound must be established before it is applied.
It includes the zero algebra, and no sign condition on `K` is needed. -/
theorem mul_comm_of_norm_le_spectralRadius (K : ℝ)
    (hK : ∀ a : E, ‖a‖ ≤ K * (spectralRadius ℂ a).toReal) (y w : E) : y * w = w * y := by
  let f : ℂ → E := fun z => NormedSpace.exp (z • y) * w * NormedSpace.exp ((-z) • y)
  have hd : Differentiable ℂ f := by
    apply Differentiable.mul
    · exact (differentiable_exp_smul_const ℂ y).mul_const w
    · simpa only [smul_neg, neg_smul] using (differentiable_exp_smul_const ℂ (-y))
  have hb : Bornology.IsBounded (Set.range f) := by
    apply (isBounded_iff_forall_norm_le).2
    refine ⟨K * (spectralRadius ℂ w).toReal, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa only [f, spectralRadius_exp_conjugate] using hK (f z)
  have heq : f = fun _ => w := by
    funext z
    simpa [f] using hd.apply_eq_apply_of_bounded hb z 0
  have hd0 : HasDerivAt f (y * w - w * y) 0 := by
    have hpos := (hasDerivAt_exp_smul_const y (0 : ℂ)).mul_const w
    have hneg := hasDerivAt_exp_smul_const (-y) (0 : ℂ)
    have hm := hpos.fun_mul hneg
    simpa [f, sub_eq_add_neg, smul_neg, neg_smul] using hm
  have hz : y * w - w * y = 0 := by
    rw [heq] at hd0
    exact hd0.unique (hasDerivAt_const (0 : ℂ) w)
  exact sub_eq_zero.mp hz

/-- The same bound excludes nonzero quasinilpotent elements, as used after
the source's commutativity argument. This does not formalize the Jacobson radical. -/
theorem eq_zero_of_norm_radius_bound (K : ℝ)
    (hK : ∀ a : E, ‖a‖ ≤ K * (spectralRadius ℂ a).toReal) (a : E)
    (ha : spectralRadius ℂ a = 0) : a = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg a)
  simpa only [ha, ENNReal.toReal_zero, mul_zero] using hK a

end SpectralIsometry

namespace SpectralIsometry

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

private theorem exp_clm_apply_cancel (δ : E →L[ℂ] E) (z : ℂ) (a : E) :
    (NormedSpace.exp (z • δ) : E →L[ℂ] E)
      ((NormedSpace.exp ((-z) • δ) : E →L[ℂ] E) a) = a := by
  have hex : z • δ ∈ Metric.eball (0 : E →L[ℂ] E)
      (NormedSpace.expSeries ℂ (E →L[ℂ] E)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top, Metric.eball_top_eq_univ]
    exact Set.mem_univ _
  letI := NormedSpace.invertibleExpOfMemBall (𝕂 := ℂ) hex
  have hm : (NormedSpace.exp (z • δ) : E →L[ℂ] E) * NormedSpace.exp ((-z) • δ) = 1 := by
    rw [neg_smul z δ, ← NormedSpace.invOf_exp_of_mem_ball (𝕂 := ℂ) hex]
    exact mul_invOf_self _
  have he := congrArg (fun L : E →L[ℂ] E => L a) hm
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using he

private theorem hasDerivAt_exp_clm_apply (δ : E →L[ℂ] E) (a : E) (z : ℂ) :
    HasDerivAt (fun t : ℂ => (NormedSpace.exp (t • δ) : E →L[ℂ] E) a)
      (δ ((NormedSpace.exp (z • δ) : E →L[ℂ] E) a)) z := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero] using
    (hasDerivAt_exp_smul_const' δ z).clm_apply (hasDerivAt_const z a)

/-- Source entire-group proposition, final step: a bounded associative derivation
exponentiates to bijective multiplicative maps. The derivation identity is an
explicit hypothesis of this helper; it is not derived from spectral isometry here. -/
theorem exp_derivation_automorphism (δ : E →L[ℂ] E)
    (hδ : ∀ a b : E, δ (a * b) = δ a * b + a * δ b) :
    ∀ z : ℂ, Function.Bijective
      ((NormedSpace.exp (z • δ) : E →L[ℂ] E) : E → E) ∧
      ∀ a b : E, (NormedSpace.exp (z • δ) : E →L[ℂ] E) (a * b) =
        (NormedSpace.exp (z • δ) : E →L[ℂ] E) a *
          (NormedSpace.exp (z • δ) : E →L[ℂ] E) b := by
  intro z
  have hleft : Function.LeftInverse
      (NormedSpace.exp ((-z) • δ) : E →L[ℂ] E)
      (NormedSpace.exp (z • δ) : E →L[ℂ] E) := by
    intro a
    simpa only [neg_neg] using exp_clm_apply_cancel δ (-z) a
  have hright : Function.RightInverse
      (NormedSpace.exp ((-z) • δ) : E →L[ℂ] E)
      (NormedSpace.exp (z • δ) : E →L[ℂ] E) := exp_clm_apply_cancel δ z
  refine ⟨⟨hleft.injective, hright.surjective⟩, ?_⟩
  intro a b
  let S : ℂ → E →L[ℂ] E := fun t => NormedSpace.exp (t • δ)
  let F : ℂ → E := fun t => S (-t) (S t a * S t b)
  have hFderiv (t : ℂ) : HasDerivAt F 0 t := by
    have hminus : HasDerivAt (fun u : ℂ => S (-u)) (S (-t) * (-δ)) t := by
      have hneg (u : ℂ) : (-u) • δ = -(u • δ) := neg_smul u δ
      simpa only [S, smul_neg, hneg] using hasDerivAt_exp_smul_const (-δ) t
    have hp : HasDerivAt (fun u : ℂ => S u a * S u b) (δ (S t a * S t b)) t := by
      exact ((hasDerivAt_exp_clm_apply δ a t).fun_mul
        (hasDerivAt_exp_clm_apply δ b t)).congr_deriv (hδ (S t a) (S t b)).symm
    have he := hminus.clm_apply hp
    simpa only [F, mul_apply_eq_comp, neg_apply, map_neg, neg_add_cancel] using he
  have hconst : F z = F 0 := is_const_of_deriv_eq_zero
    (fun t => (hFderiv t).differentiableAt) (fun t => (hFderiv t).deriv) z 0
  have hFvalue : F z = a * b := by
    simpa only [F, S, neg_zero, zero_smul ℂ δ, NormedSpace.exp_zero,
      one_apply_eq_self] using hconst
  have he := congrArg (fun c : E => S z c) hFvalue
  simpa only [F, S, exp_clm_apply_cancel] using he.symm

/-- The automorphisms above preserve the identity; surjectivity and
multiplicativity suffice to deduce this, including in the zero algebra. -/
theorem exp_derivation_one (δ : E →L[ℂ] E)
    (hδ : ∀ a b : E, δ (a * b) = δ a * b + a * δ b) (z : ℂ) :
    (NormedSpace.exp (z • δ) : E →L[ℂ] E) 1 = 1 := by
  obtain ⟨hb, hm⟩ := exp_derivation_automorphism δ hδ z
  obtain ⟨a, ha⟩ := hb.2 1
  simpa only [one_mul, ha, mul_one] using (hm 1 a).symm

end SpectralIsometry

namespace SpectralIsometry.JordanDerivationAlgebra

variable {A : Type*} [Ring A] [Algebra ℂ A]

def defect (d : A →ₗ[ℂ] A) (a b : A) : A := d (a * b) - d a * b - a * d b

def comm (a b : A) : A := a * b - b * a

private theorem two_smul_cancel {x y : A} (h : (2 : ℂ) • x = (2 : ℂ) • y) : x = y := by
  have hz : (2 : ℂ) • (x - y) = 0 := by rw [smul_sub, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))

theorem jordan_product (d : A →ₗ[ℂ] A)
    (hJ : ∀ a : A, d (a ^ 2) = d a * a + a * d a) (a b : A) :
    d (a * b + b * a) = d a * b + a * d b + d b * a + b * d a := by
  calc
    d (a * b + b * a) = d ((a + b) ^ 2 - a ^ 2 - b ^ 2) := by
      congr 1
      noncomm_ring
    _ = (d (a + b) * (a + b) + (a + b) * d (a + b)) -
        (d a * a + a * d a) - (d b * b + b * d b) := by
      rw [map_sub, map_sub, hJ, hJ, hJ]
    _ = d a * b + a * d b + d b * a + b * d a := by
      rw [map_add]
      noncomm_ring

theorem jordan_triple (d : A →ₗ[ℂ] A)
    (hJ : ∀ a : A, d (a ^ 2) = d a * a + a * d a) (a b : A) :
    d (a * b * a) = d a * b * a + a * d b * a + a * b * d a := by
  apply two_smul_cancel
  have hd : (2 : ℂ) • (a * b * a) =
      (a * (a * b + b * a) + (a * b + b * a) * a) - (a ^ 2 * b + b * a ^ 2) := by
    simp only [two_smul]
    noncomm_ring
  calc
    (2 : ℂ) • d (a * b * a) = d ((2 : ℂ) • (a * b * a)) := (map_smul d _ _).symm
    _ = d ((a * (a * b + b * a) + (a * b + b * a) * a) -
        (a ^ 2 * b + b * a ^ 2)) := by rw [hd]
    _ = (2 : ℂ) • (d a * b * a + a * d b * a + a * b * d a) := by
      rw [map_sub, jordan_product d hJ, jordan_product d hJ,
        jordan_product d hJ, hJ]
      simp only [two_smul]
      noncomm_ring

theorem jordan_triple_polar (d : A →ₗ[ℂ] A)
    (hJ : ∀ a : A, d (a ^ 2) = d a * a + a * d a) (a b c : A) :
    d (a * b * c + c * b * a) =
      d a * b * c + a * d b * c + a * b * d c +
      d c * b * a + c * d b * a + c * b * d a := by
  calc
    d (a * b * c + c * b * a) =
        d ((a + c) * b * (a + c) - a * b * a - c * b * c) := by
      congr 1
      noncomm_ring
    _ = _ := by
      rw [map_sub, map_sub, jordan_triple d hJ, jordan_triple d hJ, jordan_triple d hJ]
      simp only [map_add]
      noncomm_ring

theorem defect_skew (d : A →ₗ[ℂ] A)
    (hJ : ∀ a : A, d (a ^ 2) = d a * a + a * d a) (a b : A) :
    defect d b a = - defect d a b := by
  have h := jordan_product d hJ a b
  rw [map_add] at h
  dsimp [defect]
  linear_combination (norm := noncomm_ring) h

theorem defect_add_left (d : A →ₗ[ℂ] A) (a b c : A) :
    defect d (a + b) c = defect d a c + defect d b c := by
  simp only [defect, add_mul, map_add]
  noncomm_ring

theorem defect_add_right (d : A →ₗ[ℂ] A) (a b c : A) :
    defect d a (b + c) = defect d a b + defect d a c := by
  simp only [defect, mul_add, map_add]
  noncomm_ring

omit [Algebra ℂ A] in
theorem comm_add_left (a b c : A) : comm (a + b) c = comm a c + comm b c := by
  dsimp [comm]
  noncomm_ring

omit [Algebra ℂ A] in
theorem comm_add_right (a b c : A) : comm a (b + c) = comm a b + comm a c := by
  dsimp [comm]
  noncomm_ring

/-- Universal identity preceding the first use of semiprimeness. -/
theorem defect_comm_anticommute (d : A →ₗ[ℂ] A)
    (hJ : ∀ a : A, d (a ^ 2) = d a * a + a * d a) (a b m : A) :
    defect d a b * m * comm a b + comm a b * m * defect d a b = 0 := by
  have hp := jordan_triple_polar d hJ (a * b) m (b * a)
  have hq := jordan_triple d hJ a (b * m * b)
  have hr := jordan_triple d hJ b (a * m * a)
  rw [jordan_triple d hJ b m] at hq
  rw [jordan_triple d hJ a m] at hr
  have hd : (a * b) * m * (b * a) + (b * a) * m * (a * b) =
      a * (b * m * b) * a + b * (a * m * a) * b := by noncomm_ring
  rw [hd, map_add, hq, hr] at hp
  have hba : d (b * a) = - d (a * b) + d a * b + a * d b + d b * a + b * d a := by
    have h := jordan_product d hJ a b
    rw [map_add] at h
    linear_combination (norm := noncomm_ring) h
  rw [hba] at hp
  dsimp [defect, comm]
  linear_combination (norm := noncomm_ring) hp

omit [Algebra ℂ A] in
theorem reverse_zero_products
    (hsemi : ∀ x : A, (∀ r : A, x * r * x = 0) → x = 0)
    (a b : A) (hab : ∀ r : A, a * r * b = 0) (r : A) : b * r * a = 0 := by
  apply hsemi
  intro t
  calc
    (b * r * a) * t * (b * r * a) = b * r * (a * t * b) * r * a := by noncomm_ring
    _ = 0 := by rw [hab t]; simp

theorem anticommute_products_vanish
    (hsemi : ∀ x : A, (∀ r : A, x * r * x = 0) → x = 0)
    (a b : A) (h : ∀ r : A, a * r * b + b * r * a = 0) (r : A) :
    a * r * b = 0 := by
  have hneg (s : A) : a * s * b = -(b * s * a) := eq_neg_of_add_eq_zero_left (h s)
  apply hsemi
  intro t
  have he : (a * r * b) * t * (a * r * b) = -((a * r * b) * t * (a * r * b)) := by
    calc
      (a * r * b) * t * (a * r * b) = (-(b * r * a)) * t * (a * r * b) :=
        congrArg (fun z : A => z * t * (a * r * b)) (hneg r)
      _ = (-(b * (r * a * t) * a)) * r * b := by noncomm_ring
      _ = (a * (r * a * t) * b) * r * b := by rw [← hneg (r * a * t)]
      _ = a * r * (a * t * b) * r * b := by noncomm_ring
      _ = -((a * r * b) * t * (a * r * b)) := by rw [hneg t]; noncomm_ring
  have hz : (2 : ℂ) • ((a * r * b) * t * (a * r * b)) = 0 := by
    simp only [two_smul]
    calc
      (a * r * b) * t * (a * r * b) + (a * r * b) * t * (a * r * b) =
          (a * r * b) * t * (a * r * b) + -((a * r * b) * t * (a * r * b)) :=
        congrArg (fun z : A => (a * r * b) * t * (a * r * b) + z) he
      _ = 0 := add_neg_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Polarization of two mutually annihilating additive families in a semiprime algebra. -/
theorem polarize_zero_pairs
    (hsemi : ∀ x : A, (∀ r : A, x * r * x = 0) → x = 0)
    (f g : A → A) (hf : ∀ a b : A, f (a + b) = f a + f b)
    (hg : ∀ a b : A, g (a + b) = g a + g b)
    (hL : ∀ a r : A, f a * r * g a = 0)
    (hR : ∀ a r : A, g a * r * f a = 0) (a b r : A) : f a * r * g b = 0 := by
  have hm : f a * r * g b + f b * r * g a = 0 := by
    have h := hL (a + b) r
    simpa only [hf, hg, add_mul, mul_add, hL, zero_add, add_zero, add_comm] using h
  have hn : f a * r * g b = -(f b * r * g a) := eq_neg_of_add_eq_zero_left hm
  apply hsemi
  intro t
  calc
    (f a * r * g b) * t * (f a * r * g b) =
        (f a * r * g b) * t * (-(f b * r * g a)) :=
      congrArg (fun z : A => (f a * r * g b) * t * z) hn
    _ = -(f a * r * (g b * t * f b) * r * g a) := by noncomm_ring
    _ = 0 := by rw [hR b t]; simp

theorem defect_comm_vanish
    (hsemi : ∀ x : A, (∀ r : A, x * r * x = 0) → x = 0)
    (d : A →ₗ[ℂ] A) (hJ : ∀ a : A, d (a ^ 2) = d a * a + a * d a)
    (a b x y m : A) : defect d a b * m * comm x y = 0 := by
  have hbase (a b m : A) : defect d a b * m * comm a b = 0 :=
    anticommute_products_vanish hsemi _ _ (defect_comm_anticommute d hJ a b) m
  have hbaseR (a b m : A) : comm a b * m * defect d a b = 0 :=
    reverse_zero_products hsemi _ _ (hbase a b) m
  have hfirst (a b x m : A) : defect d a b * m * comm x b = 0 :=
    polarize_zero_pairs hsemi (fun v => defect d v b) (fun v => comm v b)
      (fun v w => defect_add_left d v w b) (fun v w => comm_add_left v w b)
      (fun v r => hbase v b r) (fun v r => hbaseR v b r) a x m
  have hfirstR (a b x m : A) : comm x b * m * defect d a b = 0 :=
    reverse_zero_products hsemi _ _ (hfirst a b x) m
  exact polarize_zero_pairs hsemi (fun v => defect d a v) (fun v => comm x v)
    (fun v w => defect_add_right d a v w) (fun v w => comm_add_right x v w)
    (fun v r => hfirst a v x r) (fun v r => hfirstR a v x r) b y m

omit [Algebra ℂ A] in
theorem central_cube_zero
    (hsemi : ∀ x : A, (∀ r : A, x * r * x = 0) → x = 0)
    (x : A) (hc : ∀ r : A, x * r = r * x) (h3 : x * x * x = 0) : x = 0 := by
  have h2 : x * x = 0 := by
    apply hsemi
    intro r
    calc
      (x * x) * r * (x * x) = x * (x * r) * x * x := by noncomm_ring
      _ = x * (r * x) * x * x := by rw [hc r]
      _ = (x * r) * (x * x * x) := by noncomm_ring
      _ = 0 := by rw [h3, mul_zero]
  apply hsemi
  intro r
  calc
    x * r * x = (r * x) * x := by rw [hc r]
    _ = r * (x * x) := mul_assoc _ _ _
    _ = 0 := by rw [h2, mul_zero]

/-- Algebraic semiprime proof: every complex-linear Jordan derivation is a derivation. -/
theorem derivation_of_jordan
    (hsemi : ∀ x : A, (∀ r : A, x * r * x = 0) → x = 0)
    (d : A →ₗ[ℂ] A) (hJ : ∀ a : A, d (a ^ 2) = d a * a + a * d a) (a b : A) :
    d (a * b) = d a * b + a * d b := by
  have hL (a b x y m : A) : defect d a b * m * comm x y = 0 :=
    defect_comm_vanish hsemi d hJ a b x y m
  have hR (a b x y m : A) : comm x y * m * defect d a b = 0 :=
    reverse_zero_products hsemi _ _ (fun r => hL a b x y r) m
  have hcentral (a b z : A) : defect d a b * z = z * defect d a b := by
    apply sub_eq_zero.mp
    apply hsemi
    intro r
    calc
      (defect d a b * z - z * defect d a b) * r * (defect d a b * z - z * defect d a b) =
          defect d a b * (z * r) * comm (defect d a b) z -
            z * (defect d a b * r * comm (defect d a b) z) := by
        dsimp [comm]
        noncomm_ring
      _ = 0 := by rw [hL a b _ _ (z * r), hL a b _ _ r]; simp
  let f := defect d a b
  let c := comm a b
  have hc (z : A) : f * z = z * f := hcentral a b z
  have hfc : f * c = 0 := by simpa only [mul_one] using hL a b a b 1
  have hcf : c * f = 0 := by simpa only [mul_one] using hR a b a b 1
  have htwo : (2 : ℂ) • f = d c - comm (d a) b - comm a (d b) := by
    have hp := jordan_product d hJ a b
    rw [map_add] at hp
    dsimp [f, c, defect, comm]
    rw [map_sub]
    simp only [two_smul]
    linear_combination (norm := noncomm_ring) hp
  have htwoSq : (2 : ℂ) • (f * f) = f * d c := by
    calc
      (2 : ℂ) • (f * f) = f * ((2 : ℂ) • f) := by simp only [two_smul]; noncomm_ring
      _ = f * (d c - comm (d a) b - comm a (d b)) := by rw [htwo]
      _ = f * d c := by
        have hz1 : f * comm (d a) b = 0 := by simpa only [mul_one] using hL a b (d a) b 1
        have hz2 : f * comm a (d b) = 0 := by simpa only [mul_one] using hL a b a (d b) 1
        rw [mul_sub, mul_sub, hz1, hz2, sub_zero, sub_zero]
  have hp := jordan_product d hJ f c
  rw [hfc, hcf, zero_add, map_zero] at hp
  have ht1 : (d f * c) * f = 0 := by rw [mul_assoc, hcf, mul_zero]
  have ht2 : (c * d f) * f = 0 := by
    calc
      (c * d f) * f = c * (d f * f) := mul_assoc _ _ _
      _ = c * (f * d f) := by rw [← hc (d f)]
      _ = (c * f) * d f := (mul_assoc _ _ _).symm
      _ = 0 := by rw [hcf, zero_mul]
  have hm := congrArg (fun z : A => z * f) hp
  simp only [zero_mul, add_mul] at hm
  rw [ht1, ht2, ← hc (d c)] at hm
  have hu : (f * d c) * f = 0 := by
    apply two_smul_cancel (y := 0)
    simpa only [two_smul, zero_add, add_zero] using hm.symm
  have h3 : f * f * f = 0 := by
    apply two_smul_cancel (y := 0)
    have hh := congrArg (fun z : A => z * f) htwoSq
    simpa only [smul_mul_assoc, hu, smul_zero] using hh
  have hf : f = 0 := central_cube_zero hsemi f hc h3
  change defect d a b = 0 at hf
  dsimp [defect] at hf
  linear_combination (norm := noncomm_ring) hf

end SpectralIsometry.JordanDerivationAlgebra

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

/-- C*-algebras are algebraically semiprime, including the zero algebra. -/
theorem cstar_semiprime (x : A) (h : ∀ r : A, x * r * x = 0) : x = 0 := by
  have hz : (star x * x) * (star x * x) = 0 := by
    calc
      (star x * x) * (star x * x) = star x * (x * star x * x) := by noncomm_ring
      _ = 0 := by rw [h (star x), mul_zero]
  have hn : ‖star x * x‖ ^ 2 = 0 := by
    rw [← (IsSelfAdjoint.star_mul_self x).norm_mul_self, hz, norm_zero]
  have hzero : star x * x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact (CStarRing.star_mul_self_eq_zero_iff x).mp hzero

/-- Source line 311, proved algebraically with no boundedness or nonzero assumption. -/
theorem jordan_derivation_is_derivation (d : A →ₗ[ℂ] A)
    (hJ : ∀ a : A, d (a ^ 2) = d a * a + a * d a) (a b : A) :
    d (a * b) = d a * b + a * d b :=
  JordanDerivationAlgebra.derivation_of_jordan cstar_semiprime d hJ a b

end SpectralIsometry

namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Source Lemma3.2 (lem:resolvent): image resolvent estimate, with the usual lambda-minus-a
resolvent convention. Norms agree with the source's opposite sign. -/
theorem image_selfadjoint_resolvent_bound (U : A ≃L[ℂ] B)
    (hU : PreservesRadius U.toLinearEquiv.toLinearMap) (h1 : U 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) (z : ℂ) (hz : z.im ≠ 0) :
    IsUnit (algebraMap ℂ B z - U a) ∧
      ‖Ring.inverse (algebraMap ℂ B z - U a)‖ ≤ ‖U.symm.toContinuousLinearMap‖ / |z.im| := by
  let c := algebraMap ℂ B z - U a
  let t := |z.im|
  let K := ‖U.symm.toContinuousLinearMap‖
  have ht : 0 < t := abs_pos.mpr hz
  have hc : IsUnit c := by
    by_contra hn
    have hm : z ∈ spectrum ℂ (U a) := spectrum.mem_iff.mpr hn
    exact hz (selfadjoint_image_real_spectrum U.toLinearEquiv.toLinearMap hU h1 a ha z hm)
  refine ⟨hc, ?_⟩
  rcases subsingleton_or_nontrivial B with hB | hB
  · letI := hB
    have hzero : Ring.inverse c = 0 := Subsingleton.elim _ _
    change ‖Ring.inverse c‖ ≤ K / t
    rw [hzero, norm_zero]
    exact div_nonneg (norm_nonneg _) ht.le
  · letI := hB
    have hA10 : (1 : A) ≠ 0 := by
      intro hzero
      have hB10 : (1 : B) = 0 := by
        rw [← h1, hzero, map_zero]
      exact one_ne_zero hB10
    letI : Nontrivial A := nontrivial_of_ne (1 : A) 0 hA10
    have hInv1 : U.symm 1 = 1 := by
      apply U.injective
      rw [U.apply_symm_apply, h1]
    have hKone : 1 ≤ K := by
      have hh := U.symm.toContinuousLinearMap.le_opNorm (1 : B)
      simpa only [ContinuousLinearEquiv.coe_coe, hInv1, norm_one, mul_one] using hh
    have hK : 0 < K := lt_of_lt_of_le zero_lt_one hKone
    have hd : t / K ≤ Metric.infDist c {b : B | ¬IsUnit b} := by
      apply (Metric.le_infDist ⟨0, not_isUnit_zero⟩).mpr
      intro b hb
      by_contra hfail
      have hnear : dist c b < t / K := lt_of_not_ge hfail
      let h := U.symm (c - b)
      have hh : ‖h‖ ≤ K * dist c b := by
        simpa only [ContinuousLinearEquiv.coe_coe, h, K, dist_eq_norm] using
          U.symm.toContinuousLinearMap.le_opNorm (c - b)
      have hcancel : K * (t / K) = t := by field_simp
      have hsmall : ‖h‖ < t := by
        apply lt_of_le_of_lt hh
        simpa only [hcancel] using mul_lt_mul_of_pos_left hnear hK
      have hUh : U h = c - b := U.apply_symm_apply _
      have hshift : algebraMap ℂ B z - U (a + h) = b := by
        rw [map_add, hUh]
        dsimp [c]
        abel
      have hmem : z ∈ spectrum ℂ (U (a + h)) := by
        rw [spectrum.mem_iff, hshift]
        exact hb
      have hstrip := selfadjoint_image_perturbation_strip
        U.toLinearEquiv.toLinearMap hU h1 a h ha z hmem
      exact (not_le.mpr hsmall) hstrip
    rw [distance_to_nonunits c hc] at hd
    let n := ‖Ring.inverse c‖
    have hnz : Ring.inverse c ≠ 0 := by
      obtain ⟨u, hu⟩ := hc
      rw [← hu, Ring.inverse_unit]
      exact Units.ne_zero _
    have hn : 0 < n := norm_pos_iff.mpr hnz
    change t / K ≤ n⁻¹ at hd
    have hprod := mul_le_mul_of_nonneg_right hd hn.le
    rw [inv_mul_cancel₀ hn.ne'] at hprod
    have hrew : (t / K) * n = (n * t) / K := by ring
    rw [hrew] at hprod
    have hnt : n * t ≤ K := by
      simpa only [one_mul] using (div_le_iff₀ hK).mp hprod
    exact (le_div_iff₀ ht).mpr hnt

end SpectralIsometry

open Filter Topology
open scoped NNReal ENNReal ComplexOrder CStarAlgebra

namespace SpectralIsometry.TraceBound

variable {A : Type*} [CStarAlgebra A]

private theorem exists_norm_pow_lt (c : A) {t : ℝ≥0} (_ht0 : 0 < t)
    (ht : spectralRadius ℂ c < (t : ℝ≥0∞)) :
    ∃ n : ℕ, 0 < n ∧ ‖c ^ n‖ < (t : ℝ) ^ n := by
  have he := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius c).eventually
    (gt_mem_nhds ht)
  obtain ⟨n, hn, hroot⟩ := ((eventually_gt_atTop 0).and he).exists
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : (‖c ^ n‖₊ : ℝ≥0∞) < (t : ℝ≥0∞) ^ (n : ℝ) :=
    (ENNReal.rpow_inv_lt_iff hnR).mp (by simpa only [one_div] using hroot)
  rw [ENNReal.rpow_natCast, ← ENNReal.coe_pow] at hp
  exact ⟨n, hn, by exact_mod_cast hp⟩

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

private def rotaSum (s : A) (n : ℕ) : A :=
  ∑ i ∈ Finset.range n, star (s ^ i) * s ^ i

private theorem rotaSum_succ (s : A) (n : ℕ) :
    rotaSum s (n + 1) = rotaSum s n + star (s ^ n) * s ^ n := by
  simp only [rotaSum, Finset.sum_range_succ]

private theorem rotaSum_shift (s : A) (n : ℕ) :
    star s * rotaSum s n * s = rotaSum s n - 1 + star (s ^ n) * s ^ n := by
  induction n with
  | zero => simp [rotaSum]
  | succ n ih =>
    have hp : star s * (star (s ^ n) * s ^ n) * s =
        star (s ^ (n + 1)) * s ^ (n + 1) := by
      simp only [pow_succ, star_mul, mul_assoc]
    simp only [rotaSum_succ, mul_add, add_mul]
    rw [ih, hp]
    abel

private theorem one_le_rotaSum (s : A) (n : ℕ) (hn : 0 < n) : 1 ≤ rotaSum s n := by
  have h := Finset.single_le_sum
    (fun i (_hi : i ∈ Finset.range n) => star_mul_self_nonneg (s ^ i))
    (Finset.mem_range.mpr hn)
  simpa only [pow_zero, star_one, one_mul, rotaSum] using h

private theorem state_norm_bound (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (a : A) :
    ‖τ a‖ ≤ ‖a‖ := by
  have hcs := PositiveLinearMap.norm_map_star_mul_sq_le τ 1 a
  simp only [star_one, one_mul, h1, norm_one] at hcs
  have hp := τ.norm_apply_le_of_nonneg (star a * a) (star_mul_self_nonneg a)
  rw [h1, norm_one, one_mul, CStarRing.norm_star_mul_self] at hp
  nlinarith [norm_nonneg (τ a), norm_nonneg a]

private theorem trace_norm_le_one_of_power (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a))
    (s : A) (n : ℕ) (hn : 0 < n) (hpow : ‖s ^ n‖ ≤ 1) : ‖τ s‖ ≤ 1 := by
  let h := rotaSum s n
  have hh1 : 1 ≤ h := one_le_rotaSum s n hn
  have hh0 : 0 ≤ h := zero_le_one.trans hh1
  have hhunit : IsUnit h := CStarAlgebra.isUnit_of_le 1 hh1
  have hhpos : IsStrictlyPositive h := hhunit.isStrictlyPositive hh0
  have hlast : star (s ^ n) * s ^ n ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg (s ^ n)]
  have hshift : star s * h * s ≤ h := by
    calc
      star s * h * s = h - 1 + star (s ^ n) * s ^ n := rotaSum_shift s n
      _ ≤ h - 1 + 1 := add_le_add le_rfl hlast
      _ = h := sub_add_cancel h 1
  let p := CFC.sqrt h
  let q := h ^ (-(1 / 2) : ℝ)
  have hp0 : 0 ≤ p := CFC.sqrt_nonneg h
  have hq0 : 0 ≤ q := CFC.rpow_nonneg
  have hpsa : IsSelfAdjoint p := hp0.isSelfAdjoint
  have hqsa : IsSelfAdjoint q := hq0.isSelfAdjoint
  have hp2 : p * p = h := CFC.sqrt_mul_sqrt_self h hh0
  have hqh : q * h * q = 1 := CFC.conjugate_rpow_neg_one_half h hhpos
  have hqp : q * p = 1 := by
    dsimp only [q, p]
    rw [CFC.sqrt_eq_rpow]
    exact CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hhpos
  let y := p * s * q
  have hyy : star y * y ≤ 1 := by
    calc
      star y * y = q * (star s * h * s) * q := by
        dsimp only [y]
        rw [star_mul, star_mul, hqsa.star_eq, hpsa.star_eq, ← hp2]
        noncomm_ring
      _ ≤ q * h * q := hqsa.conjugate_le_conjugate hshift
      _ = 1 := hqh
  have hy : ‖y‖ ≤ 1 := by
    have hny := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg y)).mpr hyy
    rw [CStarRing.norm_star_mul_self] at hny
    nlinarith [norm_nonneg y]
  have htrace : τ y = τ s := by
    calc
      τ y = τ (q * (p * s)) := htr (p * s) q
      _ = τ s := by rw [← mul_assoc, hqp, one_mul]
  rw [← htrace]
  exact (state_norm_bound τ h1 y).trans hy

private theorem ordered_trace_radius_bound (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (c : A) :
    (‖τ c‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ c := by
  by_contra hfail
  obtain ⟨t, hrt, htn⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hfail)
  have ht0 : 0 < t := by
    exact_mod_cast (show (0 : ℝ≥0∞) ≤ spectralRadius ℂ c from zero_le).trans_lt hrt
  have htR : 0 < (t : ℝ) := ht0
  obtain ⟨n, hn, hcn⟩ := exists_norm_pow_lt c ht0 hrt
  let s : A := (t : ℝ)⁻¹ • c
  have hsmall : ‖s ^ n‖ ≤ 1 := by
    calc
      ‖s ^ n‖ = ‖c ^ n‖ / (t : ℝ) ^ n := by
        simp [s, smul_pow, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg t.2, inv_pow, div_eq_mul_inv, mul_comm]
      _ ≤ 1 := (div_le_one (pow_pos htR n)).mpr hcn.le
  have hs := trace_norm_le_one_of_power τ h1 htr s n hn hsmall
  have hscale : ‖τ s‖ = (t : ℝ)⁻¹ * ‖τ c‖ := by
    dsimp only [s]
    rw [τ.map_smul_of_tower, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htR)]
  have hbound : ‖τ c‖ ≤ (t : ℝ) := by
    rw [hscale] at hs
    apply (div_le_one htR).mp
    simpa only [div_eq_mul_inv, mul_comm] using hs
  have he : (‖τ c‖₊ : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by exact_mod_cast hbound
  exact htn.not_ge he

end Ordered

end SpectralIsometry.TraceBound

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

/-- Source tracial spectral-radius bound, lines 211–231. Positivity and
normalization are the defining state properties; no continuity/order instance is
an additional assumption. The finite Rota-sum proof is an alternative argument. -/
theorem tracial_state_spectralRadius_bound (τ : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ τ (star a * a)) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (c : A) :
    ‖τ c‖ ≤ (spectralRadius ℂ c).toReal := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  let ρ : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ τ (fun a ha => by
    have he : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rw [← he]
    exact hpos (CFC.sqrt a))
  have hρc : ρ c = τ c := rfl
  have hb := TraceBound.ordered_trace_radius_bound ρ h1 htr c
  have hrfin : spectralRadius ℂ c ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜 := ℂ) c)
  have hh := ENNReal.toReal_mono hrfin hb
  simpa only [ENNReal.coe_toReal, coe_nnnorm, hρc] using hh

end SpectralIsometry

namespace SpectralIsometry.GenericBanach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def finiteBarycenters (K : Set E) (n : ℕ) : Set E :=
  (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
    ((stdSimplex ℝ (Fin n)) ×ˢ (Set.univ.pi fun _ : Fin n => K))

private theorem isCompact_finiteBarycenters (K : Set E) (hK : IsCompact K) (n : ℕ) :
    IsCompact (finiteBarycenters K n) := by
  apply IsCompact.image
    ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ => hK))
  fun_prop

/-- Compactness of a convex hull in finite dimension, from Carathéodory's theorem. -/
private theorem compact_convexHull [FiniteDimensional ℝ E] (K : Set E) (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  classical
  have heq : convexHull ℝ K =
      ⋃ n : Fin (Module.finrank ℝ E + 2), finiteBarycenters K n.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨ι, inst, z, w, hz, hind, hw, hsum, hbar⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      let := inst
      have hcard := hind.card_le_finrank_succ
      have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      have hn : Fintype.card ι < Module.finrank ℝ E + 2 := by omega
      let n : Fin (Module.finrank ℝ E + 2) := ⟨Fintype.card ι, hn⟩
      let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      refine ⟨(w ∘ e, z ∘ e), ?_, ?_⟩
      · refine ⟨⟨fun i => (hw (e i)).le, ?_⟩, ?_⟩
        · change (∑ i : Fin (Fintype.card ι), w (e i)) = 1
          exact (e.sum_comp w).trans hsum
        · exact fun i _ => hz ⟨e i, rfl⟩
      · change (∑ i : Fin (Fintype.card ι), w (e i) • z (e i)) = x
        exact (e.sum_comp (fun i => w i • z i)).trans hbar
    · intro hx
      obtain ⟨n, ⟨p, hp, rfl⟩⟩ := Set.mem_iUnion.mp hx
      exact mem_convexHull_of_exists_fintype p.1 p.2 hp.1.1 hp.1.2
        (fun i => hp.2 i (Set.mem_univ i)) rfl
  rw [heq]
  exact isCompact_iUnion fun n => isCompact_finiteBarycenters K hK n.val

end SpectralIsometry.GenericBanach

namespace SpectralIsometry.GenericBanach

private theorem real_functional_coordinates (f : ℂ →L[ℝ] ℝ) (z : ℂ) :
    f z = z.re * f 1 + z.im * f Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    f z = f (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg f hz
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

variable {A B : Type*} [NormedRing A] [NormedRing B]
  [NormedAlgebra ℂ A] [NormedAlgebra ℂ B] [CompleteSpace A] [CompleteSpace B]

private theorem translated_radius (T : A →ₗ[ℂ] B)
    (hT : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a)
    (h1 : T 1 = 1) (a : A) (z : ℂ) :
    spectralRadius ℂ (T a - algebraMap ℂ B z) =
      spectralRadius ℂ (a - algebraMap ℂ A z) := by
  have he : T (a - algebraMap ℂ A z) = T a - algebraMap ℂ B z := by
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h1,
      ← Algebra.algebraMap_eq_smul_one]
  rw [← he, hT]

private theorem spectrum_subset_closedHull_of_translated_radius
    [Nontrivial A] [Nontrivial B] (a : A) (b : B)
    (h : ∀ c : ℂ, spectralRadius ℂ (b - algebraMap ℂ B c) =
      spectralRadius ℂ (a - algebraMap ℂ A c)) :
    spectrum ℂ b ⊆ closedConvexHull ℝ (spectrum ℂ a) := by
  intro z hz
  by_contra hout
  obtain ⟨f, u, hfu, huz⟩ := geometric_hahn_banach_closed_point
    (convex_closedConvexHull (𝕜 := ℝ)) isClosed_closedConvexHull hout
  let N : ℝ := ‖a‖ * ‖(1 : A)‖
  let t : ℝ := (N ^ 2 + 1) / (2 * (f z - u))
  have ht : 0 < t := by dsimp [t]; positivity
  let c : ℂ := -(t : ℂ) * ((f 1 : ℂ) + (f Complex.I : ℂ) * Complex.I)
  have hz' : z - c ∈ spectrum ℂ (b - algebraMap ℂ B c) := by
    rw [← spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub hz (Set.mem_singleton c)
  obtain ⟨v, hv, hvr⟩ := spectrum.exists_nnnorm_eq_spectralRadius
    (a - algebraMap ℂ A c)
  have hrad : (‖z - c‖₊ : ENNReal) ≤ (‖v‖₊ : ENNReal) := by
    rw [hvr, ← h c, spectralRadius_eq_of_unital]
    exact le_iSup_of_le (z - c) (le_iSup_of_le hz' le_rfl)
  have hnorm : ‖z - c‖ ≤ ‖v‖ := by exact_mod_cast hrad
  let w : ℂ := v + c
  have hw : w ∈ spectrum ℂ a := by
    rw [← spectrum.sub_singleton_eq] at hv
    obtain ⟨x, hx, y, hy, hxy⟩ := hv
    have hy' : y = c := Set.mem_singleton_iff.mp hy
    subst y
    have hwx : w = x := by dsimp [w]; rw [← hxy]; exact sub_add_cancel x c
    rw [hwx]
    exact hx
  have hnorm' : ‖z - c‖ ^ 2 ≤ ‖w - c‖ ^ 2 := by
    have hvc : w - c = v := add_sub_cancel_right v c
    rw [hvc]
    nlinarith [norm_nonneg (z - c)]
  have hwbound : w.re ^ 2 + w.im ^ 2 ≤ N ^ 2 := by
    have hn := spectrum.norm_le_norm_mul_of_mem hw
    change ‖w‖ ≤ N at hn
    have hn2 : ‖w‖ ^ 2 ≤ N ^ 2 :=
      (sq_le_sq₀ (norm_nonneg w) (by dsimp [N]; positivity)).mpr hn
    rw [Complex.sq_norm, Complex.normSq_apply] at hn2
    nlinarith only [hn2]
  have hfw : f w ≤ u := le_of_lt (hfu w (subset_closedConvexHull hw))
  have htw : 2 * t * f w ≤ 2 * t * u :=
    mul_le_mul_of_nonneg_left hfw (by positivity)
  have hcoords := real_functional_coordinates f z
  have hwcoords := real_functional_coordinates f w
  have hid : 2 * t * (f z - u) = N ^ 2 + 1 := by
    dsimp [t]
    field_simp [ne_of_gt (sub_pos.mpr huz)]
  simp [c, Complex.sq_norm, Complex.normSq_apply] at hnorm'
  rw [hcoords] at hid
  rw [hwcoords] at htw
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- Closed convex hull preservation, a step toward the source convex hull lemma. -/
private theorem closed_spectral_hull (T : A →ₗ[ℂ] B)
    (hT : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a) (h1 : T 1 = 1) (a : A) :
    closedConvexHull ℝ (spectrum ℂ (T a)) = closedConvexHull ℝ (spectrum ℂ a) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · have : Subsingleton A := by
      rcases subsingleton_or_nontrivial A with hA | hA
      · exact hA
      · exfalso
        have h := hT (1 : A)
        have hz : T (1 : A) = 0 := Subsingleton.elim _ _
        rw [hz, spectrum.spectralRadius_zero, spectrum.spectralRadius_one] at h
        exact zero_ne_one h
    simp [spectrum.of_subsingleton, closedConvexHull]
  · have : Nontrivial A := ⟨⟨1, 0, fun h => one_ne_zero (by rw [← h1, h, map_zero])⟩⟩
    have hf := spectrum_subset_closedHull_of_translated_radius a (T a)
      (translated_radius T hT h1 a)
    have hg := spectrum_subset_closedHull_of_translated_radius (T a) a
      (fun c => (translated_radius T hT h1 a c).symm)
    exact Set.Subset.antisymm
      (closedConvexHull_min hf convex_closedConvexHull isClosed_closedConvexHull)
      (closedConvexHull_min hg convex_closedConvexHull isClosed_closedConvexHull)

/-- The full convex-hull equality in the source's Lemma 3.1. -/
theorem spectral_hull (T : A →ₗ[ℂ] B)
    (hT : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a) (h1 : T 1 = 1) (a : A) :
    convexHull ℝ (spectrum ℂ (T a)) = convexHull ℝ (spectrum ℂ a) := by
  have ha := (compact_convexHull (spectrum ℂ a) (spectrum.isCompact a)).isClosed
  have hb := (compact_convexHull (spectrum ℂ (T a)) (spectrum.isCompact (T a))).isClosed
  have h := closed_spectral_hull T hT h1 a
  simpa only [closedConvexHull_eq_closure_convexHull, ha.closure_eq, hb.closure_eq] using h

end SpectralIsometry.GenericBanach

open WeakDual

namespace SpectralIsometry.CommutativeReduction

def realAxis : Set ℂ := {z | z.im = 0}
def positiveAxis : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}

private theorem convex_realAxis : Convex ℝ realAxis :=
  convex_hyperplane (.mk Complex.add_im Complex.smul_im) 0

private theorem convex_positiveAxis : Convex ℝ positiveAxis := by
  simpa only [positiveAxis, realAxis, Set.ofPred_and] using
    convex_realAxis.inter (convex_halfSpace_re_ge 0)

def RealSpec {A : Type*} [Ring A] [Algebra ℂ A] (a : A) : Prop :=
  spectrum ℂ a ⊆ realAxis

def PositiveSpec {A : Type*} [Ring A] [Algebra ℂ A] (a : A) : Prop :=
  spectrum ℂ a ⊆ positiveAxis

section BanachMaps

variable {A B : Type*} [NormedRing A] [NormedRing B]
  [NormedAlgebra ℂ A] [NormedAlgebra ℂ B] [CompleteSpace A] [CompleteSpace B]

private theorem spectrum_subset_transfer (T : A →ₗ[ℂ] B)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a) (h1 : T 1 = 1)
    (K : Set ℂ) (hK : Convex ℝ K) (a : A) (ha : spectrum ℂ a ⊆ K) :
    spectrum ℂ (T a) ⊆ K := by
  intro z hz
  apply convexHull_min ha hK
  rw [← GenericBanach.spectral_hull T hr h1 a]
  exact subset_convexHull ℝ (spectrum ℂ (T a)) hz

private theorem realSpec_transfer (T : A →ₗ[ℂ] B)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a) (h1 : T 1 = 1)
    (a : A) (ha : RealSpec a) : RealSpec (T a) :=
  spectrum_subset_transfer T hr h1 realAxis convex_realAxis a ha

private theorem positiveSpec_transfer (T : A →ₗ[ℂ] B)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a) (h1 : T 1 = 1)
    (a : A) (ha : PositiveSpec a) : PositiveSpec (T a) :=
  spectrum_subset_transfer T hr h1 positiveAxis convex_positiveAxis a ha

end BanachMaps

section CommutativeBanach

variable {A B : Type*} [NormedCommRing A] [NormedCommRing B]
  [NormedAlgebra ℂ A] [NormedAlgebra ℂ B] [CompleteSpace A] [CompleteSpace B]

private theorem positive_character (a : A) (ha : PositiveSpec a)
    (φ : characterSpace ℂ A) : (φ a).im = 0 ∧ 0 ≤ (φ a).re :=
  ha (AlgHom.apply_mem_spectrum φ a)

private theorem positiveSpec_shift_square (a : A) (ha : RealSpec a)
    (r : ℂ) (hr : r.im = 0) : PositiveSpec ((a - r • 1) ^ 2) := by
  intro z hz
  obtain ⟨φ, rfl⟩ := CharacterSpace.mem_spectrum_iff_exists.mp hz
  have hi : (φ a).im = 0 := ha (AlgHom.apply_mem_spectrum φ a)
  change (φ ((a - r • 1) ^ 2)).im = 0 ∧ 0 ≤ (φ ((a - r • 1) ^ 2)).re
  rw [map_pow, map_sub, map_smul, map_one]
  simp only [smul_eq_mul, mul_one, pow_two, Complex.mul_im, Complex.mul_re,
    Complex.sub_im, Complex.sub_re, hi, hr, sub_self, mul_zero, zero_mul,
    zero_add, add_zero, sub_zero]
  exact ⟨True.intro, mul_self_nonneg _⟩

private theorem positiveSpec_square (a : A) (ha : RealSpec a) : PositiveSpec (a ^ 2) := by
  simpa only [zero_smul, sub_zero] using positiveSpec_shift_square a ha 0 rfl

private theorem functional_quadratic (L : A →ₗ[ℂ] B) (h1 : L 1 = 1)
    (φ : characterSpace ℂ B) (a : A) (r : ℂ) :
    φ (L ((a - r • 1) ^ 2)) = φ (L (a ^ 2)) - 2 * r * φ (L a) + r ^ 2 := by
  have hd : (a - r • 1) ^ 2 = a ^ 2 - (2 * r) • a + (r ^ 2) • (1 : A) := by
    simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat, mul_one]
    ring
  rw [hd]
  simp only [map_add, map_sub, map_smul, h1, map_one, smul_eq_mul, mul_one]

/-- Scalar Schwarz from positive spectra, without an order or a star on the Banach codomain. -/
private theorem scalar_schwarz (L : A →ₗ[ℂ] B) (h1 : L 1 = 1)
    (hpos : ∀ x : A, PositiveSpec x → PositiveSpec (L x))
    (a : A) (ha : RealSpec a) (hLa : RealSpec (L a)) (φ : characterSpace ℂ B) :
    (φ (L a)).re ^ 2 ≤ (φ (L (a ^ 2))).re := by
  let r := φ (L a)
  have hr : r.im = 0 := hLa (AlgHom.apply_mem_spectrum φ (L a))
  have hp := positive_character _ (hpos _ (positiveSpec_shift_square a ha r hr)) φ
  have he : φ (L ((a - r • 1) ^ 2)) = φ (L (a ^ 2)) - r ^ 2 := by
    rw [functional_quadratic L h1 φ a r]
    dsimp [r]
    ring
  have hn := hp.2
  rw [he, Complex.sub_re] at hn
  simp only [pow_two, Complex.mul_re, hr, mul_zero, sub_zero] at hn
  dsimp [r] at hn
  simpa only [pow_two] using sub_nonneg.mp hn

end CommutativeBanach

section CStarSource

variable {A E : Type*} [CommCStarAlgebra A] [NormedCommRing E]
  [NormedAlgebra ℂ E] [CompleteSpace E]

private theorem injective_radius_map (T : A →ₗ[ℂ] E)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a) : Function.Injective T := by
  intro a b hab
  have hz : T (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hrad : spectralRadius ℂ (a - b) = 0 := by rw [← hr, hz, spectrum.spectralRadius_zero]
  have hn := IsStarNormal.spectralRadius_eq_nnnorm (a - b)
  rw [hrad] at hn
  have hzNorm : ‖a - b‖₊ = 0 := by exact_mod_cast hn.symm
  exact sub_eq_zero.mp (nnnorm_eq_zero.mp hzNorm)

/-- The self-adjoint-square step in the source's commutative reduction. -/
theorem commutative_selfadjoint_squares (T : A →ₗ[ℂ] E)
    (honto : Function.Surjective T) (h1 : T 1 = 1)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a)
    (h : A) (hsa : IsSelfAdjoint h) : T (h ^ 2) = (T h) ^ 2 := by
  let e : A ≃ₗ[ℂ] E := LinearEquiv.ofBijective T ⟨injective_radius_map T hr, honto⟩
  let S : E →ₗ[ℂ] A := e.symm.toLinearMap
  have hST (a : A) : S (T a) = a := e.symm_apply_apply a
  have hTS (b : E) : T (S b) = b := e.apply_symm_apply b
  have hS1 : S 1 = 1 := (injective_radius_map T hr) (by rw [hTS, h1])
  have hrS (b : E) : spectralRadius ℂ (S b) = spectralRadius ℂ b := by
    rw [← hr (S b), hTS]
  have posT (a : A) (ha : PositiveSpec a) : PositiveSpec (T a) :=
    positiveSpec_transfer T hr h1 a ha
  have posS (b : E) (hb : PositiveSpec b) : PositiveSpec (S b) :=
    positiveSpec_transfer S hrS hS1 b hb
  have hreal : RealSpec h := fun z hz => hsa.im_eq_zero_of_mem_spectrum hz
  let b := T h
  have hbReal : RealSpec b := realSpec_transfer T hr h1 h hreal
  have hSb : S b = h := hST h
  have hSbReal : RealSpec (S b) := by rw [hSb]; exact hreal
  let p := T (h ^ 2) - b ^ 2
  have hp : PositiveSpec p := by
    intro z hz
    obtain ⟨φ, rfl⟩ := CharacterSpace.mem_spectrum_iff_exists.mp hz
    have hTi := positive_character _ (posT _ (positiveSpec_square h hreal)) φ
    simp only [pow_two] at hTi
    have hbi : (φ b).im = 0 := hbReal (AlgHom.apply_mem_spectrum φ b)
    have hsch := scalar_schwarz T h1 posT h hreal hbReal φ
    change (φ b).re ^ 2 ≤ (φ (T (h ^ 2))).re at hsch
    change (φ (T (h ^ 2) - b ^ 2)).im = 0 ∧ 0 ≤ (φ (T (h ^ 2) - b ^ 2)).re
    simp only [map_sub, map_pow φ]
    constructor
    · simp only [Complex.sub_im, pow_two, Complex.mul_im, hTi.1, hbi,
        mul_zero, zero_mul, zero_add, sub_zero]
    · simpa only [Complex.sub_re, pow_two, Complex.mul_re, hbi, mul_zero, sub_zero] using
        sub_nonneg.mpr hsch
  have hpA : PositiveSpec (S p) := posS p hp
  have hsp : S p = h ^ 2 - S (b ^ 2) := by change S (T (h ^ 2) - b ^ 2) = _; rw [map_sub, hST]
  have hsqPos : PositiveSpec (S (b ^ 2)) := posS _ (positiveSpec_square b hbReal)
  have heq : S (b ^ 2) = h ^ 2 := by
    apply (gelfandTransform_isometry A).injective
    ext χ
    change χ (S (b ^ 2)) = χ (h ^ 2)
    have hchi : (χ h).im = 0 := hreal (AlgHom.apply_mem_spectrum χ h)
    have hle := scalar_schwarz S hS1 posS b hbReal hSbReal χ
    rw [hSb] at hle
    have hge := (positive_character _ hpA χ).2
    rw [hsp, map_sub, map_pow χ, Complex.sub_re] at hge
    simp only [pow_two, Complex.mul_re, hchi, mul_zero, sub_zero] at hge
    have hi := (positive_character _ hsqPos χ).1
    have hre : (χ (S (b ^ 2))).re = (χ h).re ^ 2 := by
      simp only [pow_two] at hle ⊢
      nlinarith [hge]
    apply Complex.ext
    · simpa only [map_pow χ, pow_two, map_mul χ, Complex.mul_re, hchi, mul_zero, sub_zero] using hre
    · simpa only [map_pow χ, pow_two, map_mul χ, Complex.mul_im, hchi, mul_zero, zero_mul, zero_add] using hi
  apply e.symm.injective
  change S (T (h ^ 2)) = S (b ^ 2)
  rw [hST, heq]

private theorem jordan_product_from_selfadjoint (T : A →ₗ[ℂ] E)
    (hs : ∀ h : A, IsSelfAdjoint h → T (h ^ 2) = (T h) ^ 2)
    (h k : A) (hh : IsSelfAdjoint h) (hk : IsSelfAdjoint k) :
    T (h * k + k * h) = T h * T k + T k * T h := by
  calc
    T (h * k + k * h) = T ((h + k) ^ 2 - h ^ 2 - k ^ 2) := by
      congr 1
      noncomm_ring
    _ = (T (h + k)) ^ 2 - (T h) ^ 2 - (T k) ^ 2 := by
      rw [map_sub, map_sub, hs (h + k) (hh.add hk), hs h hh, hs k hk]
    _ = T h * T k + T k * T h := by rw [map_add]; noncomm_ring

private theorem all_squares_from_selfadjoint (T : A →ₗ[ℂ] E)
    (hs : ∀ h : A, IsSelfAdjoint h → T (h ^ 2) = (T h) ^ 2) :
    ∀ a : A, T (a ^ 2) = (T a) ^ 2 := by
  intro a
  let h : A := (realPart a : A)
  let k : A := (imaginaryPart a : A)
  have hh : IsSelfAdjoint h := (realPart a).property
  have hk : IsSelfAdjoint k := (imaginaryPart a).property
  have ha : a = h + Complex.I • k := (realPart_add_I_smul_imaginaryPart a).symm
  have hexp (x y : A) : (x + Complex.I • y) ^ 2 =
      x ^ 2 - y ^ 2 + Complex.I • (x * y + y * x) := by
    simp [pow_two, mul_add, add_mul, smul_add,
      smul_smul, Complex.I_mul_I, sub_eq_add_neg]
    abel
  have hexpE (x y : E) : (x + Complex.I • y) ^ 2 =
      x ^ 2 - y ^ 2 + Complex.I • (x * y + y * x) := by
    simp [pow_two, mul_add, add_mul, smul_add,
      smul_smul, Complex.I_mul_I, sub_eq_add_neg]
    abel
  rw [ha, hexp, map_add, map_sub, map_smul, hs h hh, hs k hk,
    jordan_product_from_selfadjoint T hs h k hh hk, map_add, map_smul, hexpE]

/-- The precise C*-source instance of Nagasawa needed in the manuscript, with no
continuity, star-closedness or norm-radius-bound assumption on the input map. -/
theorem commutative_squares (T : A →ₗ[ℂ] E)
    (honto : Function.Surjective T) (h1 : T 1 = 1)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a) :
    ∀ a : A, T (a ^ 2) = (T a) ^ 2 :=
  all_squares_from_selfadjoint T (commutative_selfadjoint_squares T honto h1 hr)

/-- Multiplicativity in the source's commutative reduction. The codomain carries
only its original commutative Banach-algebra structure. -/
theorem commutative_multiplicative (T : A →ₗ[ℂ] E)
    (honto : Function.Surjective T) (h1 : T 1 = 1)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a)
    (a b : A) : T (a * b) = T a * T b := by
  have hs := commutative_squares T honto h1 hr
  have hp : T (a * b + b * a) = T a * T b + T b * T a := by
    have hh := hs (a + b)
    have hd : (a + b) ^ 2 = a ^ 2 + (a * b + b * a) + b ^ 2 := by noncomm_ring
    have hc : (T a + T b) ^ 2 = (T a) ^ 2 + (T a * T b + T b * T a) + (T b) ^ 2 := by
      noncomm_ring
    rw [hd, map_add, map_add, hs a, hs b] at hh
    conv_rhs at hh => rw [map_add, hc]
    exact add_left_cancel (add_right_cancel hh)
  rw [mul_comm b a, map_add, mul_comm (T b) (T a)] at hp
  have he : (2 : ℂ) • T (a * b) = (2 : ℂ) • (T a * T b) := by
    simpa only [two_smul] using hp
  have hz : (2 : ℂ) • (T (a * b) - T a * T b) = 0 := by
    rw [smul_sub, he, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))

end CStarSource

end SpectralIsometry.CommutativeReduction

open scoped NNReal ENNReal ComplexOrder CStarAlgebra

namespace SpectralIsometry.TraceMoments

variable {A : Type*} [CStarAlgebra A]

private theorem continuous_of_square_positive (τ : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ τ (star a * a)) : Continuous (τ : A → ℂ) := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  let ρ : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ τ (fun a ha => by
    have he : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rw [← he]
    exact hpos (CFC.sqrt a))
  have heq : (ρ : A → ℂ) = (τ : A → ℂ) := by funext a; rfl
  rw [← heq]
  exact map_continuous ρ

private theorem radius_pow_le [Nontrivial A] (a : A) (n : ℕ) :
    spectralRadius ℂ (a ^ n) ≤ (spectralRadius ℂ a) ^ n := by
  rw [spectralRadius_eq_of_unital, spectrum.map_pow]
  refine iSup₂_le fun z hz => ?_
  obtain ⟨w, hw, rfl⟩ := hz
  have hb : (‖w‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ a := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup_of_le w (le_iSup_of_le hw le_rfl)
  simp only [nnnorm_pow, ENNReal.coe_pow]
  exact pow_le_pow_left' hb n

private theorem radius_pow_eq [Nontrivial A] (a : A) (n : ℕ) :
    spectralRadius ℂ (a ^ n) = (spectralRadius ℂ a) ^ n :=
  le_antisymm (radius_pow_le a n) (spectrum.spectralRadius_pow_le' (𝕜 := ℂ) a n)

end SpectralIsometry.TraceMoments

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

/-- The original-algebra tracial moments in source lines 245–251. The argument
works for every natural power, including the required powers two and three.
No bidual, normality, multiplicativity or Jordan hypothesis is used. -/
theorem trace_entire_group_moments (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ a : A, 0 ≤ τ (star a * a)) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (b : A) (n : ℕ) (z : ℂ) :
    τ (((NormedSpace.exp (z • δ) : A →L[ℂ] A) b) ^ n) = τ (b ^ n) := by
  have : Nontrivial A := ⟨⟨1, 0, fun ha => (one_ne_zero : (1 : ℂ) ≠ 0)
    (by rw [← h1, ha, map_zero])⟩⟩
  let σ : A →L[ℂ] ℂ := { τ with cont := TraceMoments.continuous_of_square_positive τ hpos }
  have hσ (a : A) : σ a = τ a := rfl
  let U : ℂ → A := fun t => (NormedSpace.exp (t • δ) : A →L[ℂ] A) b
  have hU : Differentiable ℂ U := by
    intro t
    exact ((hasDerivAt_exp_smul_const' δ t).clm_apply
      (hasDerivAt_const t b)).differentiableAt
  have hp (m : ℕ) : Differentiable ℂ (fun t => (U t) ^ m) := by
    induction m with
    | zero => simpa only [pow_zero] using (differentiable_const (c := (1 : A)))
    | succ m ih => simpa only [pow_succ] using ih.fun_mul hU
  let f : ℂ → ℂ := fun t => σ ((U t) ^ n)
  have hf : Differentiable ℂ f := σ.differentiable.comp (hp n)
  have hbound (t : ℂ) : ‖f t‖ ≤ (spectralRadius ℂ b).toReal ^ n := by
    have hpw := TraceMoments.radius_pow_eq (U t) n
    have hr : spectralRadius ℂ (U t) = spectralRadius ℂ b := hRad t b
    rw [hr] at hpw
    calc
      ‖f t‖ = ‖τ ((U t) ^ n)‖ := by simp only [f, hσ]
      _ ≤ (spectralRadius ℂ ((U t) ^ n)).toReal :=
        tracial_state_spectralRadius_bound τ hpos h1 htr ((U t) ^ n)
      _ = (spectralRadius ℂ b).toReal ^ n := by rw [hpw, ENNReal.toReal_pow]
  have hb : Bornology.IsBounded (Set.range f) := by
    apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨(spectralRadius ℂ b).toReal ^ n, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hbound t
  have heq := hf.apply_eq_apply_of_bounded hb z 0
  simpa only [f, U, zero_smul ℂ δ, NormedSpace.exp_zero, one_apply_eq_self, hσ] using heq

end SpectralIsometry

section CheckedAddition61_0

open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology

namespace SpectralIsometry.CircleLp

private theorem analytic_nonzero_codiscrete (g : ℂ → ℂ) {c : ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall c |R|)) (hgc : g c ≠ 0) :
    ∀ᶠ z in codiscreteWithin (sphere c |R|), g z ≠ 0 := by
  have hc : c ∈ closedBall c |R| := by simp
  have hcon : IsConnected (closedBall c |R|) :=
    ⟨⟨c, hc⟩, (convex_closedBall c |R|).isPreconnected⟩
  exact codiscreteWithin_mono sphere_subset_closedBall
    (hg.preimage_zero_mem_codiscreteWithin hgc hc hcon)

/-- Boundary zeros are null for the actual angular averaging measure. -/
theorem analytic_circle_ae_ne_zero (g : ℂ → ℂ) {c : ℂ} {R : ℝ}
    (hR : R ≠ 0) (hg : AnalyticOnNhd ℂ g (closedBall c |R|)) (hgc : g c ≠ 0) :
    ∀ᵐ θ ∂volume.restrict (uIoc 0 (2 * Real.pi)), g (circleMap c R θ) ≠ 0 := by
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  exact codiscreteWithin_mono (by tauto)
    (circleMap_preimage_codiscrete hR (analytic_nonzero_codiscrete g hg hgc))

private theorem log_circle_submean (g : ℂ → ℂ) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall c |R|)) (hgc : g c ≠ 0) :
    Real.log ‖g c‖ ≤ Real.circleAverage (fun z => Real.log ‖g z‖) c R := by
  have hj := hg.circleAverage_log_norm hR.ne' hgc
  have hcenter : divisor g (closedBall c |R|) c = 0 := by
    rw [hg.divisor_apply (by simp), (hg c (by simp)).analyticOrderAt_eq_zero.mpr hgc]
    simp
  have hsum : 0 ≤ ∑ᶠ u, (divisor g (closedBall c |R|) u : ℝ) *
      Real.log (R * ‖c - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall c |R|
    · by_cases huc : u = c
      · subst u
        rw [hcenter]
        simp
      · have hd : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
        have hb : ‖c - u‖ ≤ R := by
          simpa only [mem_closedBall, dist_eq_norm', abs_of_pos hR] using hu
        have hratio : 1 ≤ R * ‖c - u‖⁻¹ := by
          rw [← div_eq_mul_inv]
          exact (one_le_div hd).mpr hb
        exact mul_nonneg (by exact_mod_cast hg.divisor_nonneg u) (Real.log_nonneg hratio)
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  linarith

private theorem exp_circleAverage_le (f : ℂ → ℝ) {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (he : CircleIntegrable (fun z => Real.exp (f z)) c R) :
    Real.exp (Real.circleAverage f c R) ≤
      Real.circleAverage (fun z => Real.exp (f z)) c R := by
  have h0 : volume (uIoc (0 : ℝ) (2 * Real.pi)) ≠ 0 := by
    simp [Real.volume_uIoc, abs_of_pos Real.two_pi_pos, Real.pi_pos]
  have hfin : volume (uIoc (0 : ℝ) (2 * Real.pi)) ≠ ⊤ := by
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hj := ConvexOn.map_set_average_le convexOn_exp Real.continuous_exp.continuousOn
    isClosed_univ h0 hfin (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    (intervalIntegrable_iff.mp hf) (intervalIntegrable_iff.mp he)
  simpa only [Real.circleAverage_eq_intervalAverage, Function.comp_apply] using hj

end SpectralIsometry.CircleLp

namespace SpectralIsometry

/-- Integrability is derived from analyticity and p>0, including boundary zeros. -/
theorem scalar_circle_rpow_integrable (g : ℂ → ℂ) {c : ℂ} {R p : ℝ}
    (hR : 0 < R) (hp : 0 < p) (hg : AnalyticOnNhd ℂ g (closedBall c R)) :
    CircleIntegrable (fun z => ‖g z‖ ^ p) c R := by
  apply ContinuousOn.circleIntegrable hR.le
  exact (hg.continuousOn.mono sphere_subset_closedBall).norm.rpow_const
    (fun _ _ => Or.inr hp.le)

/-- Scalar Lp circle submean, proved from Jensen's formula and convex Jensen.
No integrability, zero-freeness, or submean hypothesis is added. -/
theorem scalar_circle_rpow_mean (g : ℂ → ℂ) {c : ℂ} {R p : ℝ}
    (hR : 0 < R) (hp : 0 < p) (hg : AnalyticOnNhd ℂ g (closedBall c R)) :
    ‖g c‖ ^ p ≤ Real.circleAverage (fun z => ‖g z‖ ^ p) c R := by
  by_cases hgc : g c = 0
  · rw [hgc, norm_zero, Real.zero_rpow hp.ne']
    exact Real.circleAverage_nonneg_of_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg (g z)) p)
  have hgAbs : AnalyticOnNhd ℂ g (closedBall c |R|) := by
    simpa only [abs_of_pos hR] using hg
  have hlog : CircleIntegrable (fun z => Real.log ‖g z‖) c R :=
    (hgAbs.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hpLog : CircleIntegrable (fun z => p * Real.log ‖g z‖) c R := by
    simpa only [smul_eq_mul] using (CircleIntegrable.const_fun_smul (a := p) hlog)
  have heq : (fun z : ℂ => ‖g z‖ ^ p) =ᶠ[codiscreteWithin (sphere c |R|)]
      (fun z => Real.exp (p * Real.log ‖g z‖)) := by
    filter_upwards [CircleLp.analytic_nonzero_codiscrete g hgAbs hgc] with z hz
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
    congr 1
    exact mul_comm _ _
  have hpInt := scalar_circle_rpow_integrable g hR hp hg
  have heInt : CircleIntegrable (fun z => Real.exp (p * Real.log ‖g z‖)) c R :=
    CircleIntegrable.congr_codiscreteWithin heq hpInt
  have hscale : Real.circleAverage (fun z => p * Real.log ‖g z‖) c R =
      p * Real.circleAverage (fun z => Real.log ‖g z‖) c R := by
    simpa only [smul_eq_mul] using
      (Real.circleAverage_fun_smul (a := p) (f := fun z => Real.log ‖g z‖) (c := c) (R := R))
  calc
    ‖g c‖ ^ p = Real.exp (p * Real.log ‖g c‖) := by
      rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hgc)]
      congr 1
      exact mul_comm _ _
    _ ≤ Real.exp (p * Real.circleAverage (fun z => Real.log ‖g z‖) c R) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (CircleLp.log_circle_submean g hR hgAbs hgc) hp.le)
    _ = Real.exp (Real.circleAverage (fun z => p * Real.log ‖g z‖) c R) := by rw [hscale]
    _ ≤ Real.circleAverage (fun z => Real.exp (p * Real.log ‖g z‖)) c R :=
      CircleLp.exp_circleAverage_le _ hpLog heInt
    _ = Real.circleAverage (fun z => ‖g z‖ ^ p) c R :=
      (Real.circleAverage_congr_codiscreteWithin heq hR.ne').symm

end SpectralIsometry

end CheckedAddition61_0

section CheckedAddition61_1

open Filter Topology
open scoped NNReal ENNReal

namespace SpectralIsometry.AutomaticContinuity

variable {B : Type*} [CStarAlgebra B]

theorem spectralRadius_ne_top (b : B) : spectralRadius ℂ b ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜 := ℂ) b)

theorem spectralRadius_neg (b : B) : spectralRadius ℂ (-b) = spectralRadius ℂ b := by
  apply tendsto_nhds_unique
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (-b))
  simpa only [nnnorm_neg_pow] using
    spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius b

/-- A power-root infimum proof of upper semicontinuity; no normality assumption. -/
theorem upperSemicontinuous_spectralRadius :
    UpperSemicontinuous (spectralRadius ℂ : B → ℝ≥0∞) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · letI := hB
    have heq : (spectralRadius ℂ : B → ℝ≥0∞) = fun _ => 0 := by
      funext b
      rw [Subsingleton.elim b 0, spectrum.spectralRadius_zero]
    rw [heq]
    exact upperSemicontinuous_const
  · letI := hB
    have hroot (b : B) (n : ℕ) : spectralRadius ℂ b ≤
        (‖b ^ (n + 1)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ) := by
      simpa only [nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow, mul_one] using
        spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ b n
    have heq (b : B) : spectralRadius ℂ b =
        ⨅ n : ℕ, (‖b ^ (n + 1)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ) := by
      apply le_antisymm (le_iInf (hroot b))
      have hl := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius b).comp
        (tendsto_add_atTop_nat 1)
      have hl' : Tendsto (fun n : ℕ =>
          (‖b ^ (n + 1)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ)) atTop
          (𝓝 (spectralRadius ℂ b)) := by
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hl
      exact ge_of_tendsto hl' (Eventually.of_forall fun n => iInf_le _ n)
    have hf : (spectralRadius ℂ : B → ℝ≥0∞) = fun b =>
        ⨅ n : ℕ, (‖b ^ (n + 1)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ) := by
      funext b
      exact heq b
    rw [hf]
    apply upperSemicontinuous_iInf
    intro n
    have hc : Continuous (fun b : B =>
        (‖b ^ (n + 1)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ)) := by fun_prop
    exact hc.upperSemicontinuous

theorem upperSemicontinuous_radiusReal :
    UpperSemicontinuous (fun b : B => (spectralRadius ℂ b).toReal) := by
  intro b t ht
  have ht0 : 0 < t := lt_of_le_of_lt ENNReal.toReal_nonneg ht
  have hb : spectralRadius ℂ b < ENNReal.ofReal t := by
    apply (ENNReal.toReal_lt_toReal (spectralRadius_ne_top b) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal ht0.le] using ht
  filter_upwards [upperSemicontinuous_spectralRadius b (ENNReal.ofReal t) hb] with c hc
  have h := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top hc
  simpa only [ENNReal.toReal_ofReal ht0.le] using h

/-- The C*-part of the separating-space argument, after its spectral estimate.
This is a radius-translation rigidity lemma, not the missing Aupetit estimate. -/
theorem eq_zero_of_radius_translation_lower (c : B)
    (h : ∀ b : B, spectralRadius ℂ b ≤ spectralRadius ℂ (b + c)) : c = 0 := by
  have hc : spectralRadius ℂ c = 0 := by
    have hh := h (-c)
    rw [neg_add_cancel, spectrum.spectralRadius_zero, spectralRadius_neg] at hh
    exact le_zero_iff.mp hh
  have hs : IsSelfAdjoint (c + star c) := IsSelfAdjoint.add_star_self c
  have hp : spectralRadius ℂ (c + star c) = 0 := by
    have he : -(c + star c) + c = -(star c) := by abel
    have hh := h (-(c + star c))
    rw [spectralRadius_neg, he, spectralRadius_neg, SpectralIsometry.radius_star, hc] at hh
    exact le_zero_iff.mp hh
  have hsum : c + star c = 0 := by
    apply norm_eq_zero.mp
    simpa only [hp, ENNReal.toReal_zero] using hs.toReal_spectralRadius_complex_eq_norm.symm
  have hstar : star c = -c := by
    calc
      star c = -c + (c + star c) := by abel
      _ = -c := by rw [hsum, add_zero]
  have : IsStarNormal c := ⟨by simp [hstar, Commute, SemiconjBy]⟩
  have hn : ‖c‖ = 0 := by
    have hh := IsStarNormal.spectralRadius_eq_nnnorm c
    rw [hc] at hh
    simpa using congrArg ENNReal.toReal hh.symm
  exact norm_eq_zero.mp hn

end SpectralIsometry.AutomaticContinuity

namespace SpectralIsometry.AutomaticContinuity

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def IsSeparatingLimit (T : A →ₗ[ℂ] B) (b : B) : Prop :=
  ∃ u : ℕ → A, Tendsto u atTop (𝓝 0) ∧ Tendsto (fun n => T (u n)) atTop (𝓝 b)

/-- Standard closed-graph reduction. It does not establish its separating-limit premise. -/
theorem continuous_of_zero_separating_limits (T : A →ₗ[ℂ] B)
    (hzero : ∀ b : B, IsSeparatingLimit T b → b = 0) : Continuous T := by
  apply T.continuous_of_seq_closed_graph
  intro u x y hu hTu
  have hu0 : Tendsto (fun n => u n - x) atTop (𝓝 0) := by
    simpa only [sub_self] using hu.sub (tendsto_const_nhds (x := x))
  have hTy : Tendsto (fun n => T (u n - x)) atTop (𝓝 (y - T x)) := by
    simpa only [map_sub, Function.comp_apply] using
      hTu.sub (tendsto_const_nhds (x := T x))
  exact sub_eq_zero.mp (hzero (y - T x) ⟨fun n => u n - x, hu0, hTy⟩)

end SpectralIsometry.AutomaticContinuity

end CheckedAddition61_1

section CheckedAddition61_2

open Filter Topology
open scoped NNReal ENNReal

namespace SpectralIsometry.AutomaticContinuity

section BanachSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem banach_circle_rpow_mean (G : ℂ → E) (hG : Differentiable ℂ G)
    {c : ℂ} {R p : ℝ} (hR : 0 < R) (hp : 0 < p) :
    ‖G c‖ ^ p ≤ Real.circleAverage (fun z => ‖G z‖ ^ p) c R := by
  obtain ⟨φ, hφ, hvalue⟩ := exists_dual_vector'' ℂ (G c)
  have hn : ‖φ (G c)‖ = ‖G c‖ := by
    rw [hvalue]
    simp only [norm_algebraMap', norm_norm]
  have hd : Differentiable ℂ (fun z => φ (G z)) := φ.differentiable.comp hG
  have ha : AnalyticOnNhd ℂ (fun z => φ (G z)) (Metric.closedBall c R) :=
    fun z _ => hd.analyticAt z
  have hm := SpectralIsometry.scalar_circle_rpow_mean (fun z => φ (G z)) hR hp ha
  rw [hn] at hm
  have hcont : Continuous (fun z => ‖G z‖ ^ p) :=
    hG.continuous.norm.rpow_const (fun _ => Or.inr hp.le)
  have hcontφ : Continuous (fun z => ‖φ (G z)‖ ^ p) :=
    hd.continuous.norm.rpow_const (fun _ => Or.inr hp.le)
  apply hm.trans
  apply Real.circleAverage_mono
    (ContinuousOn.circleIntegrable hR.le hcontφ.continuousOn)
    (ContinuousOn.circleIntegrable hR.le hcont.continuousOn)
  intro z _
  apply Real.rpow_le_rpow (norm_nonneg _) _ hp.le
  calc
    ‖φ (G z)‖ ≤ ‖φ‖ * ‖G z‖ := φ.le_opNorm _
    _ ≤ 1 * ‖G z‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
    _ = ‖G z‖ := one_mul _

end BanachSpace

section RadiusMean

variable {E : Type*} [CStarAlgebra E]

theorem power_root_le_norm (a : E) (n : ℕ) :
    ‖a ^ (n + 1)‖ ^ (1 / (n + 1) : ℝ) ≤ ‖a‖ := by
  calc
    ‖a ^ (n + 1)‖ ^ (1 / (n + 1) : ℝ) ≤
        (‖a‖ ^ (n + 1)) ^ (1 / (n + 1) : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_pow_le' a (Nat.succ_pos n))
        (by positivity)
    _ = ‖a‖ := by
      simpa only [Nat.succ_eq_add_one, one_div, Nat.cast_add, Nat.cast_one] using
        Real.pow_rpow_inv_natCast (norm_nonneg a) (Nat.succ_ne_zero n)

theorem power_root_tendsto_radiusReal (a : E) :
    Tendsto (fun n : ℕ => ‖a ^ (n + 1)‖ ^ (1 / (n + 1) : ℝ)) atTop
      (𝓝 (spectralRadius ℂ a).toReal) := by
  have ht := (ENNReal.tendsto_toReal (spectralRadius_ne_top a)).comp
    ((spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).comp
      (tendsto_add_atTop_nat 1))
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (norm_nonneg _) _)] using ht

theorem radiusReal_le_norm (a : E) : (spectralRadius ℂ a).toReal ≤ ‖a‖ := by
  simpa only [ENNReal.coe_toReal, coe_nnnorm] using
    ENNReal.toReal_mono ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜 := ℂ) a)

theorem spectralRadius_circleIntegrable (F : ℂ → E) (hF : Continuous F)
    (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    CircleIntegrable (fun z => (spectralRadius ℂ (F z)).toReal) c R := by
  have hn : CircleIntegrable (fun z => ‖F z‖) c R :=
    ContinuousOn.circleIntegrable hR hF.norm.continuousOn
  have hr : Measurable (fun θ => (spectralRadius ℂ (F (circleMap c R θ))).toReal) :=
    (upperSemicontinuous_radiusReal.comp (hF.comp (continuous_circleMap c R))).measurable
  apply hn.mono_fun' hr.aestronglyMeasurable
  exact MeasureTheory.ae_of_all _ fun θ => by
    change ‖(spectralRadius ℂ (F (circleMap c R θ))).toReal‖ ≤ ‖F (circleMap c R θ)‖
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact radiusReal_le_norm _

/-- The radius submean needed below. The power roots are dominated by the norm,
so ordinary Gelfand convergence and dominated convergence suffice. -/
theorem spectralRadius_circle_mean (F : ℂ → E) (hF : Differentiable ℂ F)
    {c : ℂ} {R : ℝ} (hR : 0 < R) :
    (spectralRadius ℂ (F c)).toReal ≤
      Real.circleAverage (fun z => (spectralRadius ℂ (F z)).toReal) c R := by
  let g : ℕ → ℂ → ℝ := fun n z => ‖F z ^ (n + 1)‖ ^ (1 / (n + 1) : ℝ)
  have hpow (m : ℕ) : Differentiable ℂ (fun z => F z ^ m) := by
    induction m with
    | zero => simpa only [pow_zero] using (differentiable_const (c := (1 : E)))
    | succ m ih => simpa only [pow_succ] using ih.fun_mul hF
  have hgcont (n : ℕ) : Continuous (g n) :=
    (hpow (n + 1)).continuous.norm.rpow_const (fun _ => Or.inr (by positivity))
  have hgi (n : ℕ) : CircleIntegrable (g n) c R :=
    ContinuousOn.circleIntegrable hR.le (hgcont n).continuousOn
  have hm (n : ℕ) : g n c ≤ Real.circleAverage (g n) c R :=
    banach_circle_rpow_mean (fun z => F z ^ (n + 1)) (hpow (n + 1)) hR (by positivity)
  have hlimint := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume) (l := atTop)
    (F := fun n θ => g n (circleMap c R θ))
    (f := fun θ => (spectralRadius ℂ (F (circleMap c R θ))).toReal)
    (fun θ => ‖F (circleMap c R θ)‖)
    (Eventually.of_forall fun n => (hgi n).aestronglyMeasurable_restrict_uIoc)
    (Eventually.of_forall fun n => MeasureTheory.ae_of_all _ fun θ _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact power_root_le_norm _ n)
    (ContinuousOn.circleIntegrable hR.le hF.continuous.norm.continuousOn)
    (MeasureTheory.ae_of_all _ fun θ _ => power_root_tendsto_radiusReal _)
  have hlimavg : Tendsto (fun n => Real.circleAverage (g n) c R) atTop
      (𝓝 (Real.circleAverage (fun z => (spectralRadius ℂ (F z)).toReal) c R)) :=
    tendsto_const_nhds.smul hlimint
  exact le_of_tendsto_of_tendsto (power_root_tendsto_radiusReal (F c)) hlimavg
    (Eventually.of_forall hm)

/-- The same checked mean inequality in nonnegative extended-real integral form,
matching Mathlib's reverse Fatou interface. -/
theorem spectralRadius_circle_lintegral (F : ℂ → E) (hF : Differentiable ℂ F)
    {c : ℂ} {R : ℝ} (hR : 0 < R) :
    spectralRadius ℂ (F c) * MeasureTheory.volume (Set.Ioc 0 (2 * Real.pi)) ≤
      ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), spectralRadius ℂ (F (circleMap c R θ)) := by
  have hk : 0 < 2 * Real.pi := by positivity
  have hm := mul_le_mul_of_nonneg_left (spectralRadius_circle_mean F hF (c := c) hR) hk.le
  have hm' : (2 * Real.pi) * (spectralRadius ℂ (F c)).toReal ≤
      ∫ θ in 0..2 * Real.pi, (spectralRadius ℂ (F (circleMap c R θ))).toReal := by
    simpa only [Real.circleAverage_def, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hk.ne', one_mul] using hm
  have he := ENNReal.ofReal_le_ofReal hm'
  rw [ENNReal.ofReal_mul hk.le,
    ENNReal.ofReal_toReal (spectralRadius_ne_top (F c)),
    intervalIntegral.integral_of_le hk.le] at he
  have hi := (spectralRadius_circleIntegrable F hF.continuous c hR.le).1
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi
    (MeasureTheory.ae_of_all _ fun _ => ENNReal.toReal_nonneg)] at he
  have heq : (fun θ => ENNReal.ofReal (spectralRadius ℂ (F (circleMap c R θ))).toReal) =
      (fun θ => spectralRadius ℂ (F (circleMap c R θ))) := by
    funext θ
    exact ENNReal.ofReal_toReal (spectralRadius_ne_top _)
  rw [heq] at he
  simpa only [Real.volume_Ioc, sub_zero, mul_comm] using he

end RadiusMean

end SpectralIsometry.AutomaticContinuity

end CheckedAddition61_2

section CheckedAddition61_3

open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SpectralIsometry.AutomaticContinuity

/-- Reverse Fatou forces equality almost everywhere when all means are at least
the same constant and the pointwise upper limit is at most that constant. -/
theorem limsup_ae_eq_const_of_mean_lower
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (F : ℕ → X → ℝ≥0∞) (N M : ℝ≥0∞)
    (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n, F n ≤ᵐ[μ] fun _ => N)
    (hNfin : N * μ univ ≠ ∞)
    (hupper : ∀ x, limsup (fun n => F n x) atTop ≤ M)
    (hmean : ∀ n, M * μ univ ≤ ∫⁻ x, F n x ∂μ) :
    (fun x => limsup (fun n => F n x) atTop) =ᵐ[μ] fun _ => M := by
  have hMfin : M * μ univ ≠ ∞ := by
    apply ne_top_of_le_ne_top hNfin
    calc
      M * μ univ ≤ ∫⁻ x, F 0 x ∂μ := hmean 0
      _ ≤ ∫⁻ _x, N ∂μ := lintegral_mono_ae (hbound 0)
      _ = N * μ univ := lintegral_const N
  have hlow : M * μ univ ≤ ∫⁻ x, limsup (fun n => F n x) atTop ∂μ := by
    calc
      M * μ univ ≤ liminf (fun n => ∫⁻ x, F n x ∂μ) atTop :=
        le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hmean)
      _ ≤ limsup (fun n => ∫⁻ x, F n x ∂μ) atTop := liminf_le_limsup
      _ ≤ ∫⁻ x, limsup (fun n => F n x) atTop ∂μ :=
        limsup_lintegral_le (fun _ => N) hF hbound (by simpa using hNfin)
  have hu : (fun x => limsup (fun n => F n x) atTop) ≤ᵐ[μ] fun _ => M :=
    ae_of_all μ hupper
  have hfin : (∫⁻ x, limsup (fun n => F n x) atTop ∂μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top hMfin
    simpa only [lintegral_const] using lintegral_mono_ae hu
  apply ae_eq_of_ae_le_of_lintegral_le hu hfin measurable_const.aemeasurable
  simpa only [lintegral_const] using hlow

/-- Upper semicontinuity extends an almost-everywhere lower bound on an interval
to each interior point. -/
theorem lower_of_ae_lower_of_upperSemicontinuous
    (f : ℝ → ℝ≥0∞) (hf : UpperSemicontinuous f) {a b x : ℝ} {M : ℝ≥0∞}
    (hx : x ∈ Ioo a b)
    (hae : ∀ᵐ t ∂volume.restrict (Ioc a b), M ≤ f t) : M ≤ f x := by
  by_contra h
  have hfx : f x < M := lt_of_not_ge h
  let s : Set ℝ := Ioo a b ∩ {t | f t < M}
  have hs : IsOpen s := isOpen_Ioo.inter (hf.isOpen_preimage M)
  have hne : s.Nonempty := ⟨x, hx, hfx⟩
  apply (hs.measure_ne_zero volume hne)
  have hae' : ∀ᵐ t ∂volume, t ∈ Ioc a b → M ≤ f t :=
    (ae_restrict_iff' measurableSet_Ioc).mp hae
  have hn : ∀ᵐ t ∂volume, t ∉ s := by
    filter_upwards [hae'] with t ht hts
    exact (not_lt_of_ge (ht ⟨hts.1.1, hts.1.2.le⟩)) hts.2
  simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hn

end SpectralIsometry.AutomaticContinuity

end CheckedAddition61_3

section CheckedAddition61_4

open Filter Topology MeasureTheory Set
open scoped NNReal ENNReal

namespace SpectralIsometry.AutomaticContinuity

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem spectralRadius_limsup_le {u : ℕ → B} {a : B}
    (hu : Tendsto u atTop (𝓝 a)) :
    limsup (fun n => spectralRadius ℂ (u n)) atTop ≤ spectralRadius ℂ a := by
  apply (limsup_le_iff (f := atTop) (u := fun n => spectralRadius ℂ (u n))
    (by isBoundedDefault) (by isBoundedDefault)).2
  intro r hr
  exact hu.eventually (upperSemicontinuous_spectralRadius a r hr)

/-- The separating-space radius estimate, with the original ordinary linear map.
The circle-mean and reverse-Fatou arguments prove this estimate; it is not an
extra premise of the automatic-continuity conclusion. -/
theorem separating_radius_translation_lower (T : A →ₗ[ℂ] B)
    (hr : PreservesRadius T) {u : ℕ → A} {b : B}
    (hu : Tendsto u atTop (𝓝 0))
    (hTu : Tendsto (fun n => T (u n)) atTop (𝓝 b)) (a : A) :
    spectralRadius ℂ (T a) ≤ spectralRadius ℂ (T a + b) := by
  let F : ℕ → ℂ → B := fun n z => T a - z • T (u n)
  let G : ℝ → ℝ≥0∞ := fun θ => spectralRadius ℂ (T a - circleMap 0 1 θ • b)
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let M := spectralRadius ℂ (T a)
  have hF (n : ℕ) : Differentiable ℂ (F n) :=
    (differentiable_id.smul_const (T (u n))).const_sub (T a)
  obtain ⟨K, hK⟩ := (isBounded_iff_forall_norm_le).mp
    (Metric.isBounded_range_of_tendsto (fun n => T (u n)) hTu)
  have hKn (n : ℕ) : ‖T (u n)‖ ≤ K := hK _ ⟨n, rfl⟩
  let N := ENNReal.ofReal (‖T a‖ + K)
  have hmeas (n : ℕ) : Measurable (fun θ => spectralRadius ℂ (F n (circleMap 0 1 θ))) :=
    (upperSemicontinuous_spectralRadius.comp
      ((hF n).continuous.comp (continuous_circleMap 0 1))).measurable
  have hbound (n : ℕ) : (fun θ => spectralRadius ℂ (F n (circleMap 0 1 θ))) ≤ᵐ[μ]
      fun _ => N := by
    apply ae_of_all
    intro θ
    have hn : ‖F n (circleMap 0 1 θ)‖ ≤ ‖T a‖ + K := by
      calc
        ‖F n (circleMap 0 1 θ)‖ ≤ ‖T a‖ + ‖circleMap 0 1 θ • T (u n)‖ := norm_sub_le _ _
        _ = ‖T a‖ + ‖T (u n)‖ := by simp only [norm_smul, norm_circleMap_zero, abs_one, one_mul]
        _ ≤ ‖T a‖ + K := add_le_add le_rfl (hKn n)
    exact (spectralRadius_le_nnnorm (𝕜 := ℂ) _).trans
      (by simpa only [ENNReal.coe_nnreal_eq, coe_nnnorm] using ENNReal.ofReal_le_ofReal hn)
  have hNfin : N * μ univ ≠ ∞ := by
    simp only [N, μ, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hupper (θ : ℝ) :
      limsup (fun n => spectralRadius ℂ (F n (circleMap 0 1 θ))) atTop ≤ M := by
    have hs : Tendsto (fun n => a - circleMap 0 1 θ • u n) atTop (𝓝 a) := by
      simpa only [smul_zero, sub_zero] using
        (tendsto_const_nhds (x := a)).sub
          ((tendsto_const_nhds (x := circleMap 0 1 θ)).smul hu)
    have heq (n : ℕ) : spectralRadius ℂ (F n (circleMap 0 1 θ)) =
        spectralRadius ℂ (a - circleMap 0 1 θ • u n) := by
      simpa only [F, map_sub, map_smul] using hr (a - circleMap 0 1 θ • u n)
    dsimp only [M]
    rw [hr a]
    simpa only [heq] using spectralRadius_limsup_le hs
  have hmean (n : ℕ) : M * μ univ ≤
      ∫⁻ θ, spectralRadius ℂ (F n (circleMap 0 1 θ)) ∂μ := by
    have hm := spectralRadius_circle_lintegral (F n) (hF n)
      (c := (0 : ℂ)) (R := (1 : ℝ)) (by positivity)
    simpa only [μ, Measure.restrict_apply_univ, F, M, zero_smul, sub_zero] using hm
  have heqae := limsup_ae_eq_const_of_mean_lower
    (fun n θ => spectralRadius ℂ (F n (circleMap 0 1 θ))) N M hmeas hbound hNfin hupper hmean
  have htarget (θ : ℝ) :
      limsup (fun n => spectralRadius ℂ (F n (circleMap 0 1 θ))) atTop ≤ G θ := by
    apply spectralRadius_limsup_le
    exact tendsto_const_nhds.sub (tendsto_const_nhds.smul hTu)
  have hae : ∀ᵐ θ ∂μ, M ≤ G θ := by
    filter_upwards [heqae] with θ hθ
    rw [← hθ]
    exact htarget θ
  have hG : UpperSemicontinuous G := upperSemicontinuous_spectralRadius.comp
    (continuous_const.sub ((continuous_circleMap 0 1).smul continuous_const))
  have hmπ : M ≤ G Real.pi := lower_of_ae_lower_of_upperSemicontinuous G hG
    (by constructor <;> linarith [Real.pi_pos]) hae
  have hπ : circleMap 0 1 Real.pi = (-1 : ℂ) := by
    simp only [circleMap, Complex.ofReal_one, one_mul, zero_add, Complex.exp_pi_mul_I]
  simpa only [G, M, hπ, neg_one_smul, sub_neg_eq_add] using hmπ

/-- Automatic continuity with exactly the source's original hypotheses. -/
theorem continuous_of_surjective_preservesRadius (T : A →ₗ[ℂ] B)
    (honto : Function.Surjective T) (hr : PreservesRadius T) : Continuous T := by
  apply continuous_of_zero_separating_limits T
  rintro b ⟨u, hu, hTu⟩
  apply eq_zero_of_radius_translation_lower b
  intro c
  obtain ⟨a, rfl⟩ := honto c
  exact separating_radius_translation_lower T hr hu hTu a

/-- The bounded inverse used in the source is obtained after proving continuity;
it is not an additional hypothesis on the original input map. -/
theorem exists_continuousLinearEquiv_of_surjective_preservesRadius (T : A →ₗ[ℂ] B)
    (honto : Function.Surjective T) (hr : PreservesRadius T) :
    ∃ U : A ≃L[ℂ] B, U.toLinearEquiv.toLinearMap = T := by
  let e : A ≃ₗ[ℂ] B := LinearEquiv.ofBijective T ⟨injective_of_preservesRadius T hr, honto⟩
  exact ⟨e.toContinuousLinearEquivOfContinuous
    (continuous_of_surjective_preservesRadius T honto hr), rfl⟩

end SpectralIsometry.AutomaticContinuity

end CheckedAddition61_4

section CheckedAddition61_5

open Filter Topology
open scoped NNReal ENNReal CStarAlgebra

namespace SpectralIsometry.TraceSeries

variable {A : Type*} [CStarAlgebra A]

def term (s : A) (n : ℕ) : A := star (s ^ n) * s ^ n

def rotaSeries (c : A) (t : ℝ) : A := ∑' n : ℕ, term (t⁻¹ • c) n

/-- Termwise identification with t^(-2n) (c*)^n c^n in the manuscript. -/
theorem term_eq_literal (c : A) (t : ℝ) (n : ℕ) :
    term (t⁻¹ • c) n = (t⁻¹) ^ (2 * n) • ((star c) ^ n * c ^ n) := by
  simp only [term, smul_pow, star_smul, star_trivial, star_pow,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← pow_add, ← two_mul n]

private theorem eventual_norm_pow_lt (c : A) {u : ℝ}
    (hu : (spectralRadius ℂ c).toReal < u) :
    ∀ᶠ n : ℕ in atTop, ‖c ^ n‖ < u ^ n := by
  have hu0 : 0 < u := ENNReal.toReal_nonneg.trans_lt hu
  have hrfin : spectralRadius ℂ c ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜 := ℂ) c)
  have hrv : spectralRadius ℂ c < ENNReal.ofReal u :=
    (ENNReal.lt_ofReal_iff_toReal_lt hrfin).mpr hu
  have he := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius c).eventually
    (gt_mem_nhds hrv)
  filter_upwards [eventually_gt_atTop 0, he] with n hn hroot
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : (‖c ^ n‖₊ : ℝ≥0∞) < (ENNReal.ofReal u) ^ (n : ℝ) :=
    (ENNReal.rpow_inv_lt_iff hnR).mp (by simpa only [one_div] using hroot)
  rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hu0.le] at hp
  simpa only [coe_nnnorm] using (ENNReal.coe_lt_ofReal.mp hp)

/-- Norm convergence under the manuscript's spectral-radius hypothesis. -/
theorem summable_rota_series (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    Summable (fun n : ℕ => term (t⁻¹ • c) n) := by
  have ht0 : 0 < t := ENNReal.toReal_nonneg.trans_lt ht
  obtain ⟨u, hru, hut⟩ := exists_between ht
  have hu0 : 0 < u := ENNReal.toReal_nonneg.trans_lt hru
  have hq0 : 0 ≤ u / t := (div_pos hu0 ht0).le
  have hq1 : u / t < 1 := (div_lt_one ht0).mpr hut
  have hsq : (u / t) ^ 2 < 1 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1.le)]
  have hgeom : Summable (fun n : ℕ => ((u / t) ^ 2) ^ n) :=
    summable_geometric_of_lt_one (sq_nonneg _) hsq
  apply hgeom.of_norm_bounded_eventually_nat
  filter_upwards [eventual_norm_pow_lt c hru] with n hn
  have hs : ‖(t⁻¹ • c : A) ^ n‖ = ‖c ^ n‖ / t ^ n := by
    simp [smul_pow, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
      inv_pow, div_eq_mul_inv, mul_comm]
  calc
    ‖term (t⁻¹ • c : A) n‖ = (‖c ^ n‖ / t ^ n) ^ 2 := by
      rw [term, CStarRing.norm_star_mul_self, hs, pow_two]
    _ ≤ (u ^ n / t ^ n) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (pow_nonneg ht0.le _))
        (div_le_div_of_nonneg_right hn.le (pow_nonneg ht0.le n)) 2
    _ = ((u / t) ^ 2) ^ n := by
      rw [← div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n 2]

theorem summable_literal_rota_series (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    Summable (fun n : ℕ => (t⁻¹) ^ (2 * n) • ((star c) ^ n * c ^ n)) := by
  simpa only [term_eq_literal] using summable_rota_series c ht

theorem rota_series_eq_literal_tsum (c : A) (t : ℝ) :
    rotaSeries c t = ∑' n : ℕ, (t⁻¹) ^ (2 * n) • ((star c) ^ n * c ^ n) :=
  tsum_congr (fun n => term_eq_literal c t n)

private theorem term_shift (s : A) (n : ℕ) :
    star s * term s n * s = term s (n + 1) := by
  simp only [term, pow_succ, star_mul, mul_assoc]

private theorem shift_of_summable (s : A) (hs : Summable (term s)) :
    star s * (∑' n : ℕ, term s n) * s = (∑' n : ℕ, term s n) - 1 := by
  rw [← hs.tsum_mul_left (star s), ← (hs.mul_left (star s)).tsum_mul_right s]
  rw [tsum_congr (fun n => term_shift s n)]
  apply eq_sub_iff_add_eq.mpr
  have he := hs.tsum_eq_zero_add
  simpa only [term, pow_zero, star_one, one_mul, add_comm] using he.symm

/-- Exact scaled identity for the norm-convergent Rota series. -/
theorem rota_series_shift (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    star (t⁻¹ • c) * rotaSeries c t * (t⁻¹ • c) = rotaSeries c t - 1 :=
  shift_of_summable _ (summable_rota_series c ht)

/-- The series is at least 1 in the canonical Cstar order, installed internally. -/
theorem one_le_rota_series (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    (CStarAlgebra.spectralOrder A).le (1 : A) (rotaSeries c t) := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  have he := (summable_rota_series c ht).le_tsum 0
    (fun j _ => star_mul_self_nonneg ((t⁻¹ • c : A) ^ j))
  simpa only [term, pow_zero, star_one, one_mul, rotaSeries] using he

theorem rota_series_nonneg (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    (CStarAlgebra.spectralOrder A).le (0 : A) (rotaSeries c t) := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  exact zero_le_one.trans (one_le_rota_series c ht)

/-- Positivity, rather than an added invertibility assumption, supplies the unit. -/
theorem isUnit_rota_series (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) : IsUnit (rotaSeries c t) := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  exact CStarAlgebra.isUnit_of_le 1 (one_le_rota_series c ht)

/-- Original unscaled identity c* h c = t^2 (h-1). -/
theorem rota_series_identity (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    star c * rotaSeries c t * c = t ^ 2 • (rotaSeries c t - 1) := by
  have ht0 : 0 < t := ENNReal.toReal_nonneg.trans_lt ht
  have hc : t • (t⁻¹ • c) = c := by
    rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  calc
    star c * rotaSeries c t * c =
        star (t • (t⁻¹ • c)) * rotaSeries c t * (t • (t⁻¹ • c)) := by rw [hc]
    _ = t ^ 2 • (star (t⁻¹ • c) * rotaSeries c t * (t⁻¹ • c)) := by
      simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
      congr 1 <;> ring
    _ = t ^ 2 • (rotaSeries c t - 1) := by rw [rota_series_shift c ht]

end SpectralIsometry.TraceSeries

end CheckedAddition61_5

section CheckedAddition61_6

open scoped NNReal ENNReal ComplexOrder CStarAlgebra

namespace SpectralIsometry.TraceSeries

variable {A : Type*} [CStarAlgebra A]

/-- Positive square root p of the literal sum and inverse q, including the
manuscript's exact conjugation identity, upper bound, and norm estimate. -/
theorem rota_similarity (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    ∃ p q : A,
      (CStarAlgebra.spectralOrder A).le 0 p ∧
      (CStarAlgebra.spectralOrder A).le 0 q ∧
      p * p = rotaSeries c t ∧ p * q = 1 ∧ q * p = 1 ∧
      (q * q) * rotaSeries c t = 1 ∧ rotaSeries c t * (q * q) = 1 ∧
      star (p * c * q) * (p * c * q) = t ^ 2 • (1 - q * q) ∧
      (CStarAlgebra.spectralOrder A).le
        (star (p * c * q) * (p * c * q)) (t ^ 2 • (1 : A)) ∧
      ‖p * c * q‖ ≤ t := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  let h : A := rotaSeries c t
  have hh1 : 1 ≤ h := one_le_rota_series c ht
  have hh0 : 0 ≤ h := zero_le_one.trans hh1
  have hhunit : IsUnit h := isUnit_rota_series c ht
  have hhpos : IsStrictlyPositive h := hhunit.isStrictlyPositive hh0
  have ht0 : 0 < t := ENNReal.toReal_nonneg.trans_lt ht
  let s : A := t⁻¹ • c
  let p : A := CFC.sqrt h
  let q : A := h ^ (-(1 / 2) : ℝ)
  have hp0 : 0 ≤ p := CFC.sqrt_nonneg h
  have hq0 : 0 ≤ q := CFC.rpow_nonneg
  have hpsa : IsSelfAdjoint p := hp0.isSelfAdjoint
  have hqsa : IsSelfAdjoint q := hq0.isSelfAdjoint
  have hp2 : p * p = h := CFC.sqrt_mul_sqrt_self h hh0
  have hqh : q * h * q = 1 := CFC.conjugate_rpow_neg_one_half h hhpos
  have hqp : q * p = 1 := by
    dsimp only [q, p]
    rw [CFC.sqrt_eq_rpow]
    exact CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hhpos
  have hpq : p * q = 1 := by
    have he := congrArg star hqp
    simpa only [star_mul, hpsa.star_eq, hqsa.star_eq, star_one] using he
  have hleft : (q * q) * h = 1 := by
    calc
      (q * q) * h = (q * q) * (p * p) := by rw [hp2]
      _ = q * ((q * p) * p) := by simp only [mul_assoc]
      _ = 1 := by rw [hqp, one_mul, hqp]
  have hright : h * (q * q) = 1 := by
    calc
      h * (q * q) = (p * p) * (q * q) := by rw [hp2]
      _ = p * ((p * q) * q) := by simp only [mul_assoc]
      _ = 1 := by rw [hpq, one_mul, hpq]
  have hidentity : star c * h * c = t ^ 2 • (h - 1) := rota_series_identity c ht
  have hId : star (p * c * q) * (p * c * q) = t ^ 2 • (1 - q * q) := by
    calc
      star (p * c * q) * (p * c * q) = q * (star c * h * c) * q := by
        rw [star_mul, star_mul, hqsa.star_eq, hpsa.star_eq, ← hp2]
        noncomm_ring
      _ = t ^ 2 • (q * h * q - q * q) := by
        rw [hidentity]
        simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one]
      _ = t ^ 2 • (1 - q * q) := by rw [hqh]
  have hq2 : 0 ≤ q * q := by
    simpa only [hqsa.star_eq] using star_mul_self_nonneg q
  have hsmall : (1 : A) - q * q ≤ 1 := sub_le_self 1 hq2
  have hscalar : IsSelfAdjoint (t • (1 : A)) := by
    change star (t • (1 : A)) = t • (1 : A)
    simp only [star_smul, star_trivial, star_one]
  have hupper : star (p * c * q) * (p * c * q) ≤ t ^ 2 • (1 : A) := by
    rw [hId]
    simpa only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, pow_two] using
      hscalar.conjugate_le_conjugate hsmall
  have hshift : star s * h * s ≤ h := by
    rw [rota_series_shift c ht]
    exact sub_le_self h zero_le_one
  let ys : A := p * s * q
  have hys : star ys * ys ≤ 1 := by
    calc
      star ys * ys = q * (star s * h * s) * q := by
        dsimp only [ys]
        rw [star_mul, star_mul, hqsa.star_eq, hpsa.star_eq, ← hp2]
        noncomm_ring
      _ ≤ q * h * q := hqsa.conjugate_le_conjugate hshift
      _ = 1 := hqh
  have hnys : ‖ys‖ ≤ 1 := by
    have he := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg ys)).mpr hys
    rw [CStarRing.norm_star_mul_self] at he
    nlinarith [norm_nonneg ys]
  have hscale : p * c * q = t • ys := by
    dsimp only [ys, s]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul,
      mul_inv_cancel₀ ht0.ne', one_smul]
  have hn : ‖p * c * q‖ ≤ t := by
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hnys ht0.le
  exact ⟨p, q, hp0, hq0, hp2, hpq, hqp, hleft, hright, hId, hupper, hn⟩

section OrderedStateBound

variable [PartialOrder A] [StarOrderedRing A]

/- This is the separately checked elementary positive-state bound used by the
finite proof, reused here independently of its Rota-sum construction. -/
private theorem state_norm_bound (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (a : A) :
    ‖τ a‖ ≤ ‖a‖ := by
  have hcs := PositiveLinearMap.norm_map_star_mul_sq_le τ 1 a
  simp only [star_one, one_mul, h1, norm_one] at hcs
  have hp := τ.norm_apply_le_of_nonneg (star a * a) (star_mul_self_nonneg a)
  rw [h1, norm_one, one_mul, CStarRing.norm_star_mul_self] at hp
  nlinarith [norm_nonneg (τ a), norm_nonneg a]

end OrderedStateBound

/-- The original tracial bound, now derived by the literal infinite-series route.
Only square positivity, normalization, and cyclicity are hypotheses on τ. -/
theorem tracial_state_radius_bound_via_series (τ : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ τ (star a * a)) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (c : A) :
    ‖τ c‖ ≤ (spectralRadius ℂ c).toReal := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  let ρ : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ τ (fun a ha => by
    have he : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rw [← he]
    exact hpos (CFC.sqrt a))
  have hbound (t : ℝ) (ht : (spectralRadius ℂ c).toReal < t) : ‖τ c‖ ≤ t := by
    obtain ⟨p, q, hp0, hq0, hp2, hpq, hqp, hleft, hright, hId, hupper, hn⟩ :=
      rota_similarity c ht
    have htrace : τ (p * c * q) = τ c := by
      calc
        τ (p * c * q) = τ (q * (p * c)) := htr (p * c) q
        _ = τ c := by rw [← mul_assoc, hqp, one_mul]
    rw [← htrace]
    exact (state_norm_bound ρ h1 (p * c * q)).trans hn
  by_contra hfail
  obtain ⟨t, hrt, htn⟩ := exists_between (lt_of_not_ge hfail)
  exact htn.not_ge (hbound t hrt)

end SpectralIsometry.TraceSeries

end CheckedAddition61_6

section CheckedAddition61_7

namespace SpectralIsometry.JordanExponential

variable {A : Type*} [CStarAlgebra A]

private theorem exp_apply_hasDerivAt_zero (δ : A →L[ℂ] A) (a : A) :
    HasDerivAt (fun z : ℂ => (NormedSpace.exp (z • δ) : A →L[ℂ] A) a) (δ a) 0 := by
  have hzero : (NormedSpace.exp ((0 : ℂ) • δ) : A →L[ℂ] A) = 1 := by
    rw [zero_smul ℂ δ, NormedSpace.exp_zero]
  have hh := (hasDerivAt_exp_smul_const' δ (0 : ℂ)).clm_apply (hasDerivAt_const 0 a)
  convert hh using 1 <;> simp [hzero, one_apply_eq_self]

end SpectralIsometry.JordanExponential

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

/-- Full equivalence for bounded generators, including zero algebras. It does
not derive the left-hand side from the spectral hypotheses of entire_group. -/
theorem exp_squares_iff_derivation (δ : A →L[ℂ] A) :
    (∀ (z : ℂ) (a : A),
      (NormedSpace.exp (z • δ) : A →L[ℂ] A) (a ^ 2) =
        ((NormedSpace.exp (z • δ) : A →L[ℂ] A) a) ^ 2) ↔
    ∀ a b : A, δ (a * b) = δ a * b + a * δ b := by
  constructor
  · intro h
    have hJ (a : A) : δ (a ^ 2) = δ a * a + a * δ a := by
      have hf := JordanExponential.exp_apply_hasDerivAt_zero δ (a ^ 2)
      have ha := JordanExponential.exp_apply_hasDerivAt_zero δ a
      have hp : HasDerivAt
          (fun z : ℂ => ((NormedSpace.exp (z • δ) : A →L[ℂ] A) a) *
            ((NormedSpace.exp (z • δ) : A →L[ℂ] A) a))
          (δ a * a + a * δ a) 0 := by
        have hzero : (NormedSpace.exp ((0 : ℂ) • δ) : A →L[ℂ] A) = 1 := by
          rw [zero_smul ℂ δ, NormedSpace.exp_zero]
        convert ha.mul ha using 1 <;> simp [hzero, one_apply_eq_self, Pi.mul_apply]
      have heq :
          (fun z : ℂ => ((NormedSpace.exp (z • δ) : A →L[ℂ] A) a) *
            ((NormedSpace.exp (z • δ) : A →L[ℂ] A) a)) =
          (fun z : ℂ => (NormedSpace.exp (z • δ) : A →L[ℂ] A) (a ^ 2)) := by
        funext z
        simpa only [pow_two] using (h z a).symm
      rw [heq] at hp
      exact hf.unique hp
    exact jordan_derivation_is_derivation δ.toLinearMap hJ
  · intro h z a
    simpa only [pow_two] using (exp_derivation_automorphism δ h z).2 a a

end SpectralIsometry

end CheckedAddition61_7
