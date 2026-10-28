module

public import SpectralIsometry.SquareZeroProperInfiniteCorner
public import SpectralIsometry.SquareZeroProjectionAlgebra
public import SpectralIsometry.QuadraticProjection
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Weighted Square Zero Projection

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped ComplexOrder CStarAlgebra
open OAI.HochschildCorners OAI.HochschildComparison
open OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.SquareZeroPreserver

universe u v
variable {M X : Type u} {B : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] [CStarAlgebra B]

theorem weightedProjectionRelation_of_properlyInfinite_complements
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (R : M →L[ℂ] B)
    (hR : PreservesSquareZero R.toLinearMap)
    {p : M} (hp : IsStarProjection p)
    (hpp : ProperlyInfiniteProjection p) (hpq : ProperlyInfiniteProjection (1 - p)) :
    WeightedProjectionRelation (R 1) (R p) := by
  have hqp : (1 - p) * p = 0 := by rw [sub_mul,one_mul,hp.isIdempotentElem.eq,sub_self]
  have hanti := anticommute_images_of_orthogonal_properlyInfinite_corners e R hR
    hp hp.one_sub hp.mul_one_sub_self hqp hpp hpq
    (self_mem_corner hp) (self_mem_corner hp.one_sub)
  rw [map_sub] at hanti
  apply sub_eq_zero.mp
  calc
    R 1 * R p + R p * R 1 - 2 * (R p) ^ 2 =
        R p * (R 1 - R p) + (R 1 - R p) * R p := by noncomm_ring
    _ = 0 := hanti

theorem central_weight_of_all_projection_relations
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (R : M →L[ℂ] B) (honto : Function.Surjective R)
    (hproj : ∀ p : M, IsStarProjection p → WeightedProjectionRelation (R 1) (R p)) :
    ∀ b : B, Commute (R 1) b := by
  let D : B →L[ℂ] B := ContinuousLinearMap.mul ℂ B (R 1) -
    (ContinuousLinearMap.mul ℂ B).flip (R 1)
  let μ : M →L[ℂ] M →L[ℂ] B := (ContinuousLinearMap.mul ℂ B).bilinearComp R R
  let β : M →L[ℂ] M →L[ℂ] B :=
    (ContinuousLinearMap.compL ℂ M B B D).comp (μ + μ.flip)
  have hs (a b : M) : β a b = β b a := by
    change D (R a * R b + R b * R a) = D (R b * R a + R a * R b)
    rw [add_comm (R a * R b) (R b * R a)]
  have hpβ (p : M) (hp : IsStarProjection p) : β p p = 0 := by
    have hc := commute_square_of_weightedProjectionRelation (R 1) (R p) (hproj p hp)
    have hz : D (R p * R p) = 0 := by
      change R 1 * (R p * R p) - (R p * R p) * R 1 = 0
      exact sub_eq_zero.mpr (by simpa only [pow_two] using hc.eq)
    change D (R p * R p + R p * R p) = 0
    rw [map_add,hz,zero_add]
  have hβ := SpectralIsometry.QuadraticProjection.bilinear_eq_zero_of_projection_diagonal_zero e β hs hpβ
  have hall (a : M) : Commute (R 1) ((R a)^2) := by
    have hz : β a a = 0 := congrArg (fun K : M →L[ℂ] M →L[ℂ] B => K a a) hβ
    change D (R a * R a + R a * R a) = 0 at hz
    rw [map_add,←two_smul ℂ] at hz
    have hzero : D (R a * R a) = 0 :=
      (smul_eq_zero.mp hz).resolve_left (by norm_num)
    change R 1 * (R a * R a) - (R a * R a) * R 1 = 0 at hzero
    change R 1 * (R a)^2 = (R a)^2 * R 1
    exact sub_eq_zero.mp (by simpa only [pow_two] using hzero)
  apply central_of_commutes_squares
  intro b
  obtain ⟨a,rfl⟩ := honto b
  exact hall a

end SpectralIsometry.SquareZeroPreserver

