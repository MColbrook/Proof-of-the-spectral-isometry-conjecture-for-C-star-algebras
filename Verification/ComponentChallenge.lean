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
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# Component Challenge

Supporting statements for the optional extended Comparator configuration.
-/

@[expose] public section
noncomputable section

namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def PreservesRadius (T : A →ₗ[ℂ] B) : Prop :=
  ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a

def IsJordanIsomorphism (T : A →ₗ[ℂ] B) : Prop :=
  Function.Bijective T ∧ ∀ a : A, T (a ^ 2) = (T a) ^ 2

theorem radius_star (a : A) : spectralRadius ℂ (star a) = spectralRadius ℂ a := by
  sorry

theorem injective_of_preservesRadius (T : A →ₗ[ℂ] B) (hT : PreservesRadius T) :
    Function.Injective T := by
  sorry

theorem translated_radius (T : A →ₗ[ℂ] B) (hT : PreservesRadius T)
    (h1 : T 1 = 1) (a : A) (z : ℂ) :
    spectralRadius ℂ (T a - algebraMap ℂ B z) =
      spectralRadius ℂ (a - algebraMap ℂ A z) := by
  sorry

theorem square_zero_sandwich (e f y : A) (hfe : f * e = 0) :
    (e * y * f) ^ 2 = 0 := by
  sorry

theorem square_zero_support_product (n : A) (hn : n ^ 2 = 0) :
    (star n * n) * (n * star n) = 0 := by
  sorry

theorem square_zero_constant_ge_one (N K : ℝ) (hN : 0 ≤ N) (hK : 1 ≤ K) :
    1 ≤ 2 * N * K + K ^ 2 := by
  sorry

theorem square_zero_perturbation_bound (N K e h : ℝ)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hh0 : 0 ≤ h) (hh : h ≤ K * e) :
    2 * N * h + h ^ 2 ≤ (2 * N * K + K ^ 2) * e := by
  sorry

theorem selfadjoint_jordan_product (T : A →ₗ[ℂ] B)
    (hs : ∀ h : A, IsSelfAdjoint h → T (h ^ 2) = (T h) ^ 2)
    (h k : A) (hh : IsSelfAdjoint h) (hk : IsSelfAdjoint k) :
    T (h * k + k * h) = T h * T k + T k * T h := by
  sorry

/-- This conditional step does not establish its self-adjoint-square hypothesis. -/
theorem squares_of_selfadjoint_squares (T : A →ₗ[ℂ] B)
    (hs : ∀ h : A, IsSelfAdjoint h → T (h ^ 2) = (T h) ^ 2) :
    ∀ a : A, T (a ^ 2) = (T a) ^ 2 := by
  sorry

theorem derivation_kernel_mul (δ : B →ₗ[ℂ] B)
    (hδ : ∀ x y : B, δ (x * y) = δ x * y + x * δ y)
    (a b : B) (ha : δ a = 0) (hb : δ b = 0) : δ (a * b) = 0 := by
  sorry

/-- Conditional algebraic trace step, not existence or analytic moment identities. -/
theorem square_preserving_of_trace_pairings (K : A →ₗ[ℂ] B)
    (honto : Function.Surjective K) (traces : Set (B →ₗ[ℂ] ℂ))
    (hsep : ∀ d : B, (∀ τ ∈ traces, τ (star d * d) = 0) → d = 0)
    (hpair : ∀ τ ∈ traces, ∀ a b : A,
      τ (K a * K (b ^ 2)) = τ (K a * (K b) ^ 2)) :
    ∀ b : A, K (b ^ 2) = (K b) ^ 2 := by
  sorry

theorem trace_quadratic_polarization (K : A →ₗ[ℂ] B)
    (σ : A →ₗ[ℂ] ℂ) (τ : B →ₗ[ℂ] ℂ)
    (hσ : ∀ a b : A, σ (a * b) = σ (b * a))
    (hτ : ∀ a b : B, τ (a * b) = τ (b * a))
    (hmoment : ∀ a : A, τ ((K a) ^ 2) = σ (a ^ 2)) :
    ∀ a b : A, τ (K a * K b) = σ (a * b) := by
  sorry

theorem trace_cubic_polarization (K : A →ₗ[ℂ] B)
    (σ : A →ₗ[ℂ] ℂ) (τ : B →ₗ[ℂ] ℂ)
    (hσ : ∀ a b : A, σ (a * b) = σ (b * a))
    (hτ : ∀ a b : B, τ (a * b) = τ (b * a))
    (hmoment : ∀ a : A, τ ((K a) ^ 3) = σ (a ^ 3)) :
    ∀ a b : A, τ (K a * (K b) ^ 2) = σ (a * b ^ 2) := by
  sorry

/-- Source Lemma 3.1 consequence, without additional map hypotheses. -/
theorem selfadjoint_image_real_spectrum (T : A →ₗ[ℂ] B)
    (hT : PreservesRadius T) (h1 : T 1 = 1) (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z ∈ spectrum ℂ (T a)) : z.im = 0 := by
  sorry

/-- Source Lemma 3.1: the full ordinary convex-hull equality. -/
theorem spectral_hull (T : A →ₗ[ℂ] B)
    (hT : PreservesRadius T) (h1 : T 1 = 1) (a : A) :
    convexHull ℝ (spectrum ℂ (T a)) = convexHull ℝ (spectrum ℂ a) := by
  sorry

/-- Self-adjoint perturbation strip used in source line 146. -/
theorem selfadjoint_perturbation_spectral_strip (a h : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z ∈ spectrum ℂ (a + h)) : |z.im| ≤ ‖h‖ := by
  sorry

/-- Transfer of the perturbation strip through the source's unital spectral isometry. -/
theorem selfadjoint_image_perturbation_strip (T : A →ₗ[ℂ] B)
    (hT : PreservesRadius T) (h1 : T 1 = 1) (a h : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z ∈ spectrum ℂ (T (a + h))) : |z.im| ≤ ‖h‖ := by
  sorry

/-- Theorem 1.1, full strength: statement-only comparison target. -/
theorem main_result (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (h1 : T 1 = 1) (hr : PreservesRadius T) : IsJordanIsomorphism T := by
  sorry

/-- Proposition 4.2: full complex-parameter entire-group comparison target. -/
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

/-- Corollary 5.1, full strength: statement-only comparison target.
Centrality is expressed by commuting with every element of B.
Unitary membership uses Mathlib's unitary submonoid (whose subtype is a group).
-/
theorem normalization (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) :
    T 1 ∈ unitary B ∧ (∀ b : B, T 1 * b = b * T 1) ∧
      ∃ J : A →ₗ[ℂ] B, J 1 = 1 ∧ IsJordanIsomorphism J ∧
        ∀ a : A, T a = T 1 * J a := by
  sorry

end SpectralIsometry

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- Source Lemma 2.2, within the source's nonzero-algebra context. -/
theorem distance_to_nonunits (c : A) (hc : IsUnit c) :
    Metric.infDist c {b : A | ¬IsUnit b} = ‖Ring.inverse c‖⁻¹ := by
  sorry

end SpectralIsometry

namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The Jordan spectrum-preservation step used in source line 301. -/
theorem jordan_isomorphism_spectrum (T : A →ₗ[ℂ] B) (h1 : T 1 = 1)
    (hJ : IsJordanIsomorphism T) (a : A) : spectrum ℂ (T a) = spectrum ℂ a := by
  sorry

end SpectralIsometry

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

theorem holomorphic_selfadjoint_const (f : ℂ → A) (hf : Differentiable ℂ f)
    (hsa : ∀ z : ℂ, IsSelfAdjoint (f z)) (z w : ℂ) : f z = f w := by
  sorry

theorem normal_real_spectrum_selfadjoint (c : A) [IsStarNormal c]
    (hreal : ∀ z ∈ spectrum ℂ c, z.im = 0) : IsSelfAdjoint c := by
  sorry

theorem selfadjoint_of_real_spectrum_shifts (c : A)
    (hreal : ∀ a : A, IsSelfAdjoint a → ∀ z ∈ spectrum ℂ (a + c), z.im = 0) :
    IsSelfAdjoint c := by
  sorry

theorem central_spectrum_circle_unitary (u : A) (hcentral : ∀ b : A, Commute u b)
    (hcircle : spectrum ℂ u ⊆ unitary ℂ) : u ∈ unitary A := by
  sorry

end SpectralIsometry

namespace SpectralIsometry

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

theorem mul_comm_of_norm_le_spectralRadius (K : ℝ)
    (hK : ∀ a : E, ‖a‖ ≤ K * (spectralRadius ℂ a).toReal) (y w : E) : y * w = w * y := by
  sorry

theorem eq_zero_of_norm_radius_bound (K : ℝ)
    (hK : ∀ a : E, ‖a‖ ≤ K * (spectralRadius ℂ a).toReal) (a : E)
    (ha : spectralRadius ℂ a = 0) : a = 0 := by
  sorry

end SpectralIsometry

namespace SpectralIsometry

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

theorem exp_derivation_automorphism (δ : E →L[ℂ] E)
    (hδ : ∀ a b : E, δ (a * b) = δ a * b + a * δ b) :
    ∀ z : ℂ, Function.Bijective
      ((NormedSpace.exp (z • δ) : E →L[ℂ] E) : E → E) ∧
      ∀ a b : E, (NormedSpace.exp (z • δ) : E →L[ℂ] E) (a * b) =
        (NormedSpace.exp (z • δ) : E →L[ℂ] E) a *
          (NormedSpace.exp (z • δ) : E →L[ℂ] E) b := by
  sorry

theorem exp_derivation_one (δ : E →L[ℂ] E)
    (hδ : ∀ a b : E, δ (a * b) = δ a * b + a * δ b) (z : ℂ) :
    (NormedSpace.exp (z • δ) : E →L[ℂ] E) 1 = 1 := by
  sorry

end SpectralIsometry

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

theorem jordan_derivation_is_derivation (d : A →ₗ[ℂ] A)
    (hJ : ∀ a : A, d (a ^ 2) = d a * a + a * d a) (a b : A) :
    d (a * b) = d a * b + a * d b := by
  sorry

end SpectralIsometry

namespace SpectralIsometry

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem image_selfadjoint_resolvent_bound (U : A ≃L[ℂ] B)
    (hU : PreservesRadius U.toLinearEquiv.toLinearMap) (h1 : U 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) (z : ℂ) (hz : z.im ≠ 0) :
    IsUnit (algebraMap ℂ B z - U a) ∧
      ‖Ring.inverse (algebraMap ℂ B z - U a)‖ ≤ ‖U.symm.toContinuousLinearMap‖ / |z.im| := by
  sorry

end SpectralIsometry

namespace SpectralIsometry

open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A]

theorem tracial_state_spectralRadius_bound (τ : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ τ (star a * a)) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (c : A) :
    ‖τ c‖ ≤ (spectralRadius ℂ c).toReal := by
  sorry

end SpectralIsometry

namespace SpectralIsometry.GenericBanach

variable {A B : Type*} [NormedRing A] [NormedRing B]
  [NormedAlgebra ℂ A] [NormedAlgebra ℂ B] [CompleteSpace A] [CompleteSpace B]

theorem spectral_hull (T : A →ₗ[ℂ] B)
    (hT : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a) (h1 : T 1 = 1) (a : A) :
    convexHull ℝ (spectrum ℂ (T a)) = convexHull ℝ (spectrum ℂ a) := by
  sorry

end SpectralIsometry.GenericBanach

namespace SpectralIsometry.CommutativeReduction

variable {A E : Type*} [CommCStarAlgebra A] [NormedCommRing E]
  [NormedAlgebra ℂ E] [CompleteSpace E]

theorem commutative_selfadjoint_squares (T : A →ₗ[ℂ] E)
    (honto : Function.Surjective T) (h1 : T 1 = 1)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a)
    (h : A) (hsa : IsSelfAdjoint h) : T (h ^ 2) = (T h) ^ 2 := by
  sorry

theorem commutative_squares (T : A →ₗ[ℂ] E)
    (honto : Function.Surjective T) (h1 : T 1 = 1)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a) :
    ∀ a : A, T (a ^ 2) = (T a) ^ 2 := by
  sorry

theorem commutative_multiplicative (T : A →ₗ[ℂ] E)
    (honto : Function.Surjective T) (h1 : T 1 = 1)
    (hr : ∀ a : A, spectralRadius ℂ (T a) = spectralRadius ℂ a)
    (a b : A) : T (a * b) = T a * T b := by
  sorry

end SpectralIsometry.CommutativeReduction

namespace SpectralIsometry

open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A]

theorem trace_entire_group_moments (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ a : A, 0 ≤ τ (star a * a)) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (b : A) (n : ℕ) (z : ℂ) :
    τ (((NormedSpace.exp (z • δ) : A →L[ℂ] A) b) ^ n) = τ (b ^ n) := by
  sorry

end SpectralIsometry

section ChallengeAddition61_0
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry.CircleLp

theorem analytic_circle_ae_ne_zero (g : ℂ → ℂ) {c : ℂ} {R : ℝ}
    (hR : R ≠ 0) (hg : AnalyticOnNhd ℂ g (closedBall c |R|)) (hgc : g c ≠ 0) :
    ∀ᵐ θ ∂volume.restrict (uIoc 0 (2 * Real.pi)), g (circleMap c R θ) ≠ 0 := by
  sorry

end SpectralIsometry.CircleLp
end ChallengeAddition61_0

section ChallengeAddition61_1
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry

theorem scalar_circle_rpow_integrable (g : ℂ → ℂ) {c : ℂ} {R p : ℝ}
    (hR : 0 < R) (hp : 0 < p) (hg : AnalyticOnNhd ℂ g (closedBall c R)) :
    CircleIntegrable (fun z => ‖g z‖ ^ p) c R := by
  sorry

theorem scalar_circle_rpow_mean (g : ℂ → ℂ) {c : ℂ} {R p : ℝ}
    (hR : 0 < R) (hp : 0 < p) (hg : AnalyticOnNhd ℂ g (closedBall c R)) :
    ‖g c‖ ^ p ≤ Real.circleAverage (fun z => ‖g z‖ ^ p) c R := by
  sorry

end SpectralIsometry
end ChallengeAddition61_1

section ChallengeAddition61_2
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry.AutomaticContinuity

variable {B : Type*} [CStarAlgebra B]

theorem upperSemicontinuous_spectralRadius :
    UpperSemicontinuous (spectralRadius ℂ : B → ℝ≥0∞) := by
  sorry

theorem upperSemicontinuous_radiusReal :
    UpperSemicontinuous (fun b : B => (spectralRadius ℂ b).toReal) := by
  sorry

theorem eq_zero_of_radius_translation_lower (c : B)
    (h : ∀ b : B, spectralRadius ℂ b ≤ spectralRadius ℂ (b + c)) : c = 0 := by
  sorry

end SpectralIsometry.AutomaticContinuity
end ChallengeAddition61_2

section ChallengeAddition61_3
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry.AutomaticContinuity

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def IsSeparatingLimit (T : A →ₗ[ℂ] B) (b : B) : Prop :=
  ∃ u : ℕ → A, Tendsto u atTop (𝓝 0) ∧ Tendsto (fun n => T (u n)) atTop (𝓝 b)

theorem continuous_of_zero_separating_limits (T : A →ₗ[ℂ] B)
    (hzero : ∀ b : B, IsSeparatingLimit T b → b = 0) : Continuous T := by
  sorry

end SpectralIsometry.AutomaticContinuity
end ChallengeAddition61_3

section ChallengeAddition61_4
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry.AutomaticContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem banach_circle_rpow_mean (G : ℂ → E) (hG : Differentiable ℂ G)
    {c : ℂ} {R p : ℝ} (hR : 0 < R) (hp : 0 < p) :
    ‖G c‖ ^ p ≤ Real.circleAverage (fun z => ‖G z‖ ^ p) c R := by
  sorry

end SpectralIsometry.AutomaticContinuity
end ChallengeAddition61_4

section ChallengeAddition61_5
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry.AutomaticContinuity

variable {E : Type*} [CStarAlgebra E]

theorem spectralRadius_circle_mean (F : ℂ → E) (hF : Differentiable ℂ F)
    {c : ℂ} {R : ℝ} (hR : 0 < R) :
    (spectralRadius ℂ (F c)).toReal ≤
      Real.circleAverage (fun z => (spectralRadius ℂ (F z)).toReal) c R := by
  sorry

theorem spectralRadius_circle_lintegral (F : ℂ → E) (hF : Differentiable ℂ F)
    {c : ℂ} {R : ℝ} (hR : 0 < R) :
    spectralRadius ℂ (F c) * MeasureTheory.volume (Set.Ioc 0 (2 * Real.pi)) ≤
      ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), spectralRadius ℂ (F (circleMap c R θ)) := by
  sorry

end SpectralIsometry.AutomaticContinuity
end ChallengeAddition61_5

section ChallengeAddition61_6
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry.AutomaticContinuity

theorem limsup_ae_eq_const_of_mean_lower
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (F : ℕ → X → ℝ≥0∞) (N M : ℝ≥0∞)
    (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n, F n ≤ᵐ[μ] fun _ => N)
    (hNfin : N * μ univ ≠ ∞)
    (hupper : ∀ x, limsup (fun n => F n x) atTop ≤ M)
    (hmean : ∀ n, M * μ univ ≤ ∫⁻ x, F n x ∂μ) :
    (fun x => limsup (fun n => F n x) atTop) =ᵐ[μ] fun _ => M := by
  sorry

theorem lower_of_ae_lower_of_upperSemicontinuous
    (f : ℝ → ℝ≥0∞) (hf : UpperSemicontinuous f) {a b x : ℝ} {M : ℝ≥0∞}
    (hx : x ∈ Ioo a b)
    (hae : ∀ᵐ t ∂volume.restrict (Ioc a b), M ≤ f t) : M ≤ f x := by
  sorry

end SpectralIsometry.AutomaticContinuity
end ChallengeAddition61_6

section ChallengeAddition61_7
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry.AutomaticContinuity

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem separating_radius_translation_lower (T : A →ₗ[ℂ] B)
    (hr : PreservesRadius T) {u : ℕ → A} {b : B}
    (hu : Tendsto u atTop (𝓝 0))
    (hTu : Tendsto (fun n => T (u n)) atTop (𝓝 b)) (a : A) :
    spectralRadius ℂ (T a) ≤ spectralRadius ℂ (T a + b) := by
  sorry

theorem continuous_of_surjective_preservesRadius (T : A →ₗ[ℂ] B)
    (honto : Function.Surjective T) (hr : PreservesRadius T) : Continuous T := by
  sorry

theorem exists_continuousLinearEquiv_of_surjective_preservesRadius (T : A →ₗ[ℂ] B)
    (honto : Function.Surjective T) (hr : PreservesRadius T) :
    ∃ U : A ≃L[ℂ] B, U.toLinearEquiv.toLinearMap = T := by
  sorry

end SpectralIsometry.AutomaticContinuity
end ChallengeAddition61_7

section ChallengeAddition61_8
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry.TraceSeries

variable {A : Type*} [CStarAlgebra A]

def term (s : A) (n : ℕ) : A := star (s ^ n) * s ^ n

def rotaSeries (c : A) (t : ℝ) : A := ∑' n : ℕ, term (t⁻¹ • c) n

theorem summable_rota_series (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    Summable (fun n : ℕ => term (t⁻¹ • c) n) := by
  sorry

theorem summable_literal_rota_series (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    Summable (fun n : ℕ => (t⁻¹) ^ (2 * n) • ((star c) ^ n * c ^ n)) := by
  sorry

theorem rota_series_eq_literal_tsum (c : A) (t : ℝ) :
    rotaSeries c t = ∑' n : ℕ, (t⁻¹) ^ (2 * n) • ((star c) ^ n * c ^ n) := by
  sorry

theorem one_le_rota_series (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    (CStarAlgebra.spectralOrder A).le (1 : A) (rotaSeries c t) := by
  sorry

theorem rota_series_nonneg (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    (CStarAlgebra.spectralOrder A).le (0 : A) (rotaSeries c t) := by
  sorry

theorem isUnit_rota_series (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) : IsUnit (rotaSeries c t) := by
  sorry

theorem rota_series_shift (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    star (t⁻¹ • c) * rotaSeries c t * (t⁻¹ • c) = rotaSeries c t - 1 := by
  sorry

theorem rota_series_identity (c : A) {t : ℝ}
    (ht : (spectralRadius ℂ c).toReal < t) :
    star c * rotaSeries c t * c = t ^ 2 • (rotaSeries c t - 1) := by
  sorry

end SpectralIsometry.TraceSeries
end ChallengeAddition61_8

section ChallengeAddition61_9
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry.TraceSeries

variable {A : Type*} [CStarAlgebra A]

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
  sorry

theorem tracial_state_radius_bound_via_series (τ : A →ₗ[ℂ] ℂ)
    (hpos : ∀ a : A, 0 ≤ τ (star a * a)) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (c : A) :
    ‖τ c‖ ≤ (spectralRadius ℂ c).toReal := by
  sorry

end SpectralIsometry.TraceSeries
end ChallengeAddition61_9

section ChallengeAddition61_10
open Complex Filter Function MeasureTheory MeromorphicOn Metric Set
open scoped Interval Topology NNReal ENNReal ComplexOrder CStarAlgebra
namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

theorem exp_squares_iff_derivation (δ : A →L[ℂ] A) :
    (∀ (z : ℂ) (a : A),
      (NormedSpace.exp (z • δ) : A →L[ℂ] A) (a ^ 2) =
        ((NormedSpace.exp (z • δ) : A →L[ℂ] A) a) ^ 2) ↔
    ∀ a b : A, δ (a * b) = δ a * b + a * δ b := by
  sorry

end SpectralIsometry
end ChallengeAddition61_10

/- Additional source statements for a separately reviewed final Challenge.
Deliberate Challenge placeholders; never imported by the solution. -/

namespace SpectralIsometry.SourceClaims

open Complex Filter Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
local instance orderedA : PartialOrder A := CStarAlgebra.spectralOrder A
local instance starOrderedA : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem square_zero_preservation (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (h1 : T 1=1) (hr : PreservesRadius T) (n : A) (hn : n^2=0) : (T n)^2=0 := by
  sorry

theorem square_zero_contour (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (h1 : T 1=1) (hr : PreservesRadius T) (n : A) (hn : n^2=0)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    (T n)^2=(2*(Real.pi:ℂ)*I)⁻¹ •
      (∮ z in C(0,ε), z^2 • Ring.inverse (algebraMap ℂ B z-T n)) := by
  sorry

theorem angular_support_limit (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) (θ : ℝ) :
    Tendsto (fun t : ℝ => sSup ((fun w : ℂ => ‖w-(-(t:ℂ)*exp ((θ:ℂ)*I))‖) '' K)-t)
      atTop (𝓝 (sSup ((fun w : ℂ => (exp (-((θ:ℂ)*I))*w).re) '' K))) := by
  sorry

theorem polar_nearest_nonunit [Nontrivial A] (c : A) (hc : IsUnit c) :
    ∃ v : A, v ∈ unitary A ∧ c=v*CFC.abs c ∧
      IsLeast (spectrum ℝ (CFC.abs c)) ‖Ring.inverse c‖⁻¹ ∧
      ¬IsUnit (c-‖Ring.inverse c‖⁻¹ • v) ∧
      ‖c-(c-‖Ring.inverse c‖⁻¹ • v)‖=‖Ring.inverse c‖⁻¹ := by
  sorry

end SpectralIsometry.SourceClaims
