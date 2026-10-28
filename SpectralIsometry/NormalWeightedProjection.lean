module

public import SpectralIsometry.NormalProjectionApproximation
public import SpectralIsometry.WeightedSquareZeroProjection

/-!
# Normal Weighted Projection

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ComplexOrder CStarAlgebra
open OAI.HochschildComparison
open OAI.BoundedHochschild.KadisonRingrose
open SpectralIsometry.StrongStarApproximation
open SpectralIsometry.BidualFoundation.CoefficientPredual

namespace SpectralIsometry.SquareZeroPreserver

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance weightedComplexNormedSpaceSelf : NormedSpace ℂ ℂ := NormedField.toNormedSpace
local instance weightedCoefficientNormedGroup (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (coefficientPredual M) :=
  SpectralIsometry.BidualFoundation.CoefficientPredual.coefficientNormedGroup M
local instance weightedCoefficientNormedSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (coefficientPredual M) :=
  SpectralIsometry.BidualFoundation.CoefficientPredual.coefficientNormedSpace M

theorem all_weighted_projection_relations_of_bounded_strongStar_continuity
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (R : M →L[ℂ] N)
    (hR : PreservesSquareZero R.toLinearMap)
    (v w : M) (hv : star v * v = 1) (hw : star w * w = 1) (hvw : star v * w = 0)
    (hseq : ∀ (a : ℕ → M) (b : M), (∀ n, ‖a n‖ ≤ 1) →
      StrongStarTendsto (fun n => (a n : H →L[ℂ] H)) atTop (b : H →L[ℂ] H) →
      StrongStarTendsto (fun n => (R (a n) : K →L[ℂ] K)) atTop (R b : K →L[ℂ] K)) :
    ∀ p : M, IsStarProjection p → WeightedProjectionRelation (R 1) (R p) := by
  intro p hp
  obtain ⟨t,ht,htlim⟩ := exists_properlyInfinite_complement_projection_approximation M v w hv hw hvw p hp
  have htnorm (n : ℕ) : ‖t n‖ ≤ 1 := (ht n).1.norm_le _
  have hRlim := hseq t p htnorm htlim
  have hRnorm (n : ℕ) : ‖(R (t n) : K →L[ℂ] K)‖ ≤ ‖R‖ :=
    (R.le_opNorm (t n)).trans (mul_le_of_le_one_right (norm_nonneg R) (htnorm n))
  let u : K →L[ℂ] K := R 1
  let b : K →L[ℂ] K := R p
  have hu : StrongTendsto (fun _ : ℕ => u) atTop u := fun ξ => tendsto_const_nhds
  have hulim := strongTendsto_mul_of_left_norm_bound hu hRlim.1
    (Eventually.of_forall fun _ => le_refl ‖u‖)
  have hrlim := strongTendsto_mul_of_left_norm_bound hRlim.1 hu (Eventually.of_forall hRnorm)
  have hsquare := strongTendsto_mul_of_left_norm_bound hRlim.1 hRlim.1
    (Eventually.of_forall hRnorm)
  have hweights (n : ℕ) : WeightedProjectionRelation (R 1) (R (t n)) :=
    weightedProjectionRelation_of_properlyInfinite_complements (concretePredualIsometry M)
      R hR (ht n).1 (ht n).2.1 (ht n).2.2
  have hop : u * b + b * u = b * b + b * b := by
    ext ξ
    have hleft := (hulim ξ).add (hrlim ξ)
    have hright := (hsquare ξ).add (hsquare ξ)
    have heq : (fun n => (u * (R (t n) : K →L[ℂ] K)) ξ +
        ((R (t n) : K →L[ℂ] K) * u) ξ) =
        (fun n => ((R (t n) : K →L[ℂ] K) * (R (t n) : K →L[ℂ] K)) ξ +
          ((R (t n) : K →L[ℂ] K) * (R (t n) : K →L[ℂ] K)) ξ) := by
      funext n
      have hh := hweights n
      change R 1 * R (t n) + R (t n) * R 1 = 2 * (R (t n)) ^ 2 at hh
      rw [two_mul,pow_two] at hh
      have hh' := congrArg (fun a : N => (a : K →L[ℂ] K) ξ) hh
      change ((R 1 : K →L[ℂ] K) * (R (t n) : K →L[ℂ] K)) ξ +
        ((R (t n) : K →L[ℂ] K) * (R 1 : K →L[ℂ] K)) ξ =
        ((R (t n) : K →L[ℂ] K) * (R (t n) : K →L[ℂ] K)) ξ +
        ((R (t n) : K →L[ℂ] K) * (R (t n) : K →L[ℂ] K)) ξ at hh'
      exact hh'
    rw [heq] at hleft
    exact tendsto_nhds_unique hleft hright
  change R 1 * R p + R p * R 1 = 2 * (R p) ^ 2
  rw [two_mul,pow_two]
  apply Subtype.ext
  change u * b + b * u = b * b + b * b
  exact hop

theorem central_weight_of_bounded_strongStar_continuity
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (R : M →L[ℂ] N)
    (hR : PreservesSquareZero R.toLinearMap) (honto : Function.Surjective R)
    (v w : M) (hv : star v * v = 1) (hw : star w * w = 1) (hvw : star v * w = 0)
    (hseq : ∀ (a : ℕ → M) (b : M), (∀ n, ‖a n‖ ≤ 1) →
      StrongStarTendsto (fun n => (a n : H →L[ℂ] H)) atTop (b : H →L[ℂ] H) →
      StrongStarTendsto (fun n => (R (a n) : K →L[ℂ] K)) atTop (R b : K →L[ℂ] K)) :
    ∀ b : N, Commute (R 1) b :=
  central_weight_of_all_projection_relations (concretePredualIsometry M) R honto
    (all_weighted_projection_relations_of_bounded_strongStar_continuity M N R hR v w hv hw hvw hseq)

end SpectralIsometry.SquareZeroPreserver

