module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Square Zero Preserver

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

namespace SpectralIsometry.SquareZeroPreserver

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]

def PreservesSquareZero (R : A →ₗ[ℂ] B) : Prop :=
  ∀ a : A, a ^ 2 = 0 → (R a) ^ 2 = 0

theorem anticommute_images_of_squareZero (R : A →ₗ[ℂ] B)
    (hR : PreservesSquareZero R) (a b : A)
    (ha : a ^ 2 = 0) (hb : b ^ 2 = 0) (hab : a * b + b * a = 0) :
    R a * R b + R b * R a = 0 := by
  have hsum : (a + b) ^ 2 = 0 := by
    calc
      (a + b) ^ 2 = a ^ 2 + (a * b + b * a) + b ^ 2 := by noncomm_ring
      _ = 0 := by rw [ha, hb, hab]; simp
  have he := hR (a + b) hsum
  have hexp : (R a + R b) ^ 2 = (R a) ^ 2 + (R a * R b + R b * R a) + (R b) ^ 2 := by
    noncomm_ring
  rw [map_add, hexp, hR a ha, hR b hb, zero_add, add_zero] at he
  exact he

def cornerSquareZero (p : A) : Set A :=
  {a | a ^ 2 = 0 ∧ p * a = a ∧ a * p = a}

theorem anticommute_images_of_orthogonal_corners (R : A →ₗ[ℂ] B)
    (hR : PreservesSquareZero R) (p q a b : A)
    (hpq : p * q = 0) (hqp : q * p = 0)
    (ha : a ∈ cornerSquareZero p) (hb : b ∈ cornerSquareZero q) :
    R a * R b + R b * R a = 0 := by
  have hab : a * b = 0 := by
    calc
      a * b = (a * p) * (q * b) := by rw [ha.2.2, hb.2.1]
      _ = a * (p * q) * b := by noncomm_ring
      _ = 0 := by rw [hpq, mul_zero, zero_mul]
  have hba : b * a = 0 := by
    calc
      b * a = (b * q) * (p * a) := by rw [hb.2.2, ha.2.1]
      _ = b * (q * p) * a := by noncomm_ring
      _ = 0 := by rw [hqp, mul_zero, zero_mul]
  exact anticommute_images_of_squareZero R hR a b ha.1 hb.1 (by rw [hab, hba, zero_add])

def jordanPair (R : A →ₗ[ℂ] B) (b : A) : A →ₗ[ℂ] B :=
  (((LinearMap.mul ℂ B).flip (R b)) + LinearMap.mul ℂ B (R b)).comp R

@[simp] theorem jordanPair_apply (R : A →ₗ[ℂ] B) (a b : A) :
    jordanPair R b a = R a * R b + R b * R a := rfl

theorem jordanPair_symm (R : A →ₗ[ℂ] B) (a b : A) :
    jordanPair R b a = jordanPair R a b := add_comm _ _

theorem anticommute_images_of_mem_spans (R : A →ₗ[ℂ] B) (S T : Set A)
    (hST : ∀ a ∈ S, ∀ b ∈ T, R a * R b + R b * R a = 0)
    (a b : A) (ha : a ∈ Submodule.span ℂ S) (hb : b ∈ Submodule.span ℂ T) :
    R a * R b + R b * R a = 0 := by
  have hT (x : A) (hx : x ∈ S) : Submodule.span ℂ T ≤ (jordanPair R x).ker := by
    apply Submodule.span_le.mpr
    intro y hy
    change jordanPair R x y = 0
    simpa only [jordanPair_apply, add_comm] using hST x hx y hy
  have hS : Submodule.span ℂ S ≤ (jordanPair R b).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    change jordanPair R b x = 0
    rw [jordanPair_symm]
    exact hT x hx hb
  exact hS ha

/-- The algebraic step once actual corner elements have been expressed as finite
linear combinations of supported square-zero elements. This does not assert
that every corner has this spanning property. -/
theorem anticommute_images_of_corner_spans (R : A →ₗ[ℂ] B)
    (hR : PreservesSquareZero R) (p q a b : A)
    (hpq : p * q = 0) (hqp : q * p = 0)
    (ha : a ∈ Submodule.span ℂ (cornerSquareZero p))
    (hb : b ∈ Submodule.span ℂ (cornerSquareZero q)) :
    R a * R b + R b * R a = 0 :=
  anticommute_images_of_mem_spans R _ _
    (fun x hx y hy => anticommute_images_of_orthogonal_corners R hR p q x y hpq hqp hx hy)
    a b ha hb

end SpectralIsometry.SquareZeroPreserver

