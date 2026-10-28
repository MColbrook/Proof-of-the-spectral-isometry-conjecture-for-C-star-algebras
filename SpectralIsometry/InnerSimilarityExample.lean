module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Inner Similarity Example

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace SpectralIsometry.InnerSimilarityExample

abbrev M := Matrix (Fin 2) (Fin 2) ℂ

def conjugation (u : Mˣ) : M →ₗ[ℂ] M where
  toFun a := (u : M)*a*(↑u⁻¹ : M)
  map_add' a b := by simp only [mul_add,add_mul]
  map_smul' z a := by simp only [RingHom.id_apply,mul_smul_comm,smul_mul_assoc]

theorem conjugation_one (u : Mˣ) : conjugation u 1=1 := by
  simp [conjugation]

theorem conjugation_mul (u : Mˣ) (a b : M) :
    conjugation u (a*b)=conjugation u a*conjugation u b := by
  simp [conjugation,mul_assoc]

theorem conjugation_surjective (u : Mˣ) : Function.Surjective (conjugation u) := by
  intro b
  refine ⟨(↑u⁻¹ : M)*b*(u : M),?_⟩
  simp [conjugation,mul_assoc]

theorem conjugation_radius (u : Mˣ) (a : M) :
    spectralRadius ℂ (conjugation u a)=spectralRadius ℂ a := by
  have hs : spectrum ℂ (conjugation u a)=spectrum ℂ a :=
    spectrum.units_conjugate (R:=ℂ) (a:=a) (u:=u)
  rw [spectralRadius_eq_of_unital,spectralRadius_eq_of_unital]
  rw [hs]

def diagonalUnit : Mˣ where
  val := !![2,0;0,1]
  inv := !![(2:ℂ)⁻¹,0;0,1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]

def offDiagonal : M := !![0,1;0,0]

theorem diagonal_similarity_not_star :
    conjugation diagonalUnit (star offDiagonal) ≠
      star (conjugation diagonalUnit offDiagonal) := by
  intro h
  have hs : star offDiagonal = !![0,0;1,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [offDiagonal,Matrix.star_apply]
  rw [hs] at h
  have he := congrArg (fun a : M => a 1 0) h
  norm_num [conjugation,diagonalUnit,offDiagonal,Matrix.star_apply,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.vecMul,dotProduct] at he

theorem exists_radius_preserving_nonstar_similarity :
    ∃ T : M →ₗ[ℂ] M, T 1=1 ∧ Function.Surjective T ∧
      (∀ a b : M, T (a*b)=T a*T b) ∧
      (∀ a : M, spectralRadius ℂ (T a)=spectralRadius ℂ a) ∧
      ∃ a : M, T (star a) ≠ star (T a) :=
  ⟨conjugation diagonalUnit,conjugation_one _,conjugation_surjective _,
    conjugation_mul _,conjugation_radius _,offDiagonal,diagonal_similarity_not_star⟩

end SpectralIsometry.InnerSimilarityExample

