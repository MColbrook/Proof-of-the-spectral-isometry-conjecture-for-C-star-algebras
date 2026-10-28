module

public import SpectralIsometry.SquareZeroPreservation
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Module

/-!
# Square Zero Contour

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Complex Metric

namespace SpectralIsometry.SquareZeroContour

variable {B : Type*} [CStarAlgebra B]

theorem resolvent_polynomial (b : B) (hb : b^2=0) (z : ℂ) (hz : z≠0) :
    z^2 • Ring.inverse (algebraMap ℂ B z-b)=z • (1:B)+b := by
  let y : B := z⁻¹ • (1:B)+(z⁻¹)^2 • b
  have hxy : (algebraMap ℂ B z-b)*y=1 := by
    dsimp only [y]
    simp only [Algebra.algebraMap_eq_smul_one,sub_mul,mul_add,mul_smul_comm,
      smul_mul_assoc,one_mul,mul_one,smul_smul]
    rw [←pow_two b,hb]
    simp only [smul_sub,smul_smul,sub_zero]
    have hz1 : z⁻¹*z=1 := inv_mul_cancel₀ hz
    have hz2 : (z⁻¹)^2*z=z⁻¹ := by field_simp
    rw [hz1,hz2,one_smul]
    module
  have hyx : y*(algebraMap ℂ B z-b)=1 := by
    dsimp only [y]
    simp only [Algebra.algebraMap_eq_smul_one,mul_sub,add_mul,mul_smul_comm,
      smul_mul_assoc,one_mul,mul_one,smul_smul]
    rw [←pow_two b,hb,smul_zero]
    simp only [smul_add,smul_smul,add_zero]
    have hz1 : z*z⁻¹=1 := mul_inv_cancel₀ hz
    have hz2 : z*(z⁻¹)^2=z⁻¹ := by field_simp
    rw [hz1,hz2,one_smul]
    module
  have hu : IsUnit (algebraMap ℂ B z-b) := ⟨⟨_,y,hxy,hyx⟩,rfl⟩
  have hi : Ring.inverse (algebraMap ℂ B z-b)=y := by
    calc
      Ring.inverse (algebraMap ℂ B z-b)=
          Ring.inverse (algebraMap ℂ B z-b)*((algebraMap ℂ B z-b)*y) := by rw [hxy,mul_one]
      _=y := Ring.inverse_mul_cancel_left _ _ hu
  rw [hi]
  dsimp only [y]
  rw [smul_add,smul_smul,smul_smul]
  have hz1 : z^2*z⁻¹=z := by field_simp
  have hz2 : z^2*(z⁻¹)^2=1 := by field_simp
  rw [hz1,hz2,one_smul]

theorem square_zero_contour (b : B) (hb : b^2=0) (ε : ℝ) (hε : 0<ε) :
    b^2=(2*(Real.pi:ℂ)*I)⁻¹ •
      (∮ z in C(0,ε), z^2 • Ring.inverse (algebraMap ℂ B z-b)) := by
  have heq : (∮ z in C(0,ε), z^2 • Ring.inverse (algebraMap ℂ B z-b))=
      ∮ z in C(0,ε), z • (1:B)+b := by
    apply circleIntegral.integral_congr hε.le
    intro z hz
    apply resolvent_polynomial b hb z
    have hnorm : ‖z‖=ε := by simpa only [mem_sphere_iff_norm,sub_zero] using hz
    exact norm_pos_iff.mp (hnorm.symm ▸ hε)
  have hzero : (∮ z in C(0,ε), z • (1:B)+b)=0 := by
    apply (Differentiable.diffContOnCl
      ((differentiable_id.smul_const (1:B)).add_const b)).circleIntegral_eq_zero hε.le
  rw [heq,hzero,smul_zero,hb]

theorem image_contour {A : Type*} [CStarAlgebra A] (U : A ≃L[ℂ] B)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (h1 : U 1=1)
    (n : A) (hn : n^2=0) (ε : ℝ) (hε : 0<ε) (_hε1 : ε≤1) :
    (U n)^2=(2*(Real.pi:ℂ)*I)⁻¹ •
      (∮ z in C(0,ε), z^2 • Ring.inverse (algebraMap ℂ B z-U n)) :=
  square_zero_contour (U n) (SquareZeroPreservation.image_square_zero U hr h1 n hn) ε hε

end SpectralIsometry.SquareZeroContour

