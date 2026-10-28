module

public import SpectralIsometry.WeightedSquareZeroProjection
import Mathlib.Tactic.NormNum

/-!
# Unital Projection Jordan

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped ComplexOrder CStarAlgebra

namespace SpectralIsometry.SquareZeroPreserver

universe u v
variable {M X : Type u} {B : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] [CStarAlgebra B]

theorem square_preserving_of_unital_projection_relations
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (R : M →L[ℂ] B) (h1 : R 1 = 1)
    (hproj : ∀ p : M, IsStarProjection p → WeightedProjectionRelation (R 1) (R p)) :
    ∀ a : M, R (a ^ 2) = (R a) ^ 2 := by
  have hidem (p : M) (hp : IsStarProjection p) : R p * R p = R p := by
    have hh := hproj p hp
    change R 1 * R p + R p * R 1 = 2 * (R p)^2 at hh
    rw [h1,one_mul,mul_one,two_mul,pow_two] at hh
    have hz : (2 : ℂ) • (R p - R p * R p) = 0 := by
      rw [two_smul,sub_add_sub_comm,hh,sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))).symm
  let ν : M →L[ℂ] M →L[ℂ] M := ContinuousLinearMap.mul ℂ M + (ContinuousLinearMap.mul ℂ M).flip
  let γ : M →L[ℂ] M →L[ℂ] B := (ContinuousLinearMap.compL ℂ M M B R).comp ν
  let μ : M →L[ℂ] M →L[ℂ] B := (ContinuousLinearMap.mul ℂ B).bilinearComp R R
  let β : M →L[ℂ] M →L[ℂ] B := γ - (μ + μ.flip)
  have hs (a b : M) : β a b = β b a := by
    change R (a*b+b*a) - (R a*R b+R b*R a) = R (b*a+a*b) - (R b*R a+R a*R b)
    rw [add_comm (a*b) (b*a),add_comm (R a*R b) (R b*R a)]
  have hpβ (p : M) (hp : IsStarProjection p) : β p p = 0 := by
    change R (p*p+p*p) - (R p*R p+R p*R p) = 0
    rw [hp.isIdempotentElem.eq,map_add,hidem p hp,sub_self]
  have hβ := SpectralIsometry.QuadraticProjection.bilinear_eq_zero_of_projection_diagonal_zero e β hs hpβ
  intro a
  have hh : β a a = 0 := congrArg (fun K : M →L[ℂ] M →L[ℂ] B => K a a) hβ
  change R (a*a+a*a) - (R a*R a+R a*R a) = 0 at hh
  rw [map_add] at hh
  have hz : (2 : ℂ) • (R (a*a) - R a*R a) = 0 := by
    rw [two_smul,sub_add_sub_comm]
    exact hh
  simpa only [pow_two] using (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num)))

end SpectralIsometry.SquareZeroPreserver

