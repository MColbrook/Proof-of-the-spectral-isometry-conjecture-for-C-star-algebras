module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Square Zero Growth

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open Filter Topology

namespace SpectralIsometry.SquareZeroGrowth

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

/-- Linear growth of the entire inverse at infinity forces the square of the
quasinilpotent coefficient to vanish. Includes the zero Banach algebra. -/
theorem square_zero_of_inverse_linear_growth (b : E)
    (hr : spectralRadius ℂ b=0) (H : ℝ)
    (hbound : ∀ z : ℂ, 1≤‖z‖ → ‖Ring.inverse (1-z • b)‖≤H*‖z‖) : b^2=0 := by
  let f : ℂ → E := fun z => Ring.inverse (1-z • b)
  let g : ℂ → E := fun z => f z*b^2
  have hu (z : ℂ) : IsUnit (1-z • b) :=
    spectrum.isUnit_one_sub_smul_of_lt_inv_radius (by simp [hr])
  have hf : Differentiable ℂ f := by
    intro z
    exact (((differentiable_const (1:E)).sub (differentiable_id.smul_const b)).differentiableAt).inverse (hu z)
  have hg : Differentiable ℂ g := hf.mul_const (b^2)
  have he (z : ℂ) : (z^2) • g z = f z-1-z • b := by
    have h1 : f z-z • (f z*b)=1 := by
      simpa only [f,mul_sub,mul_one,mul_smul_comm] using
        Ring.inverse_mul_cancel (1-z • b) (hu z)
    have h2 : f z*b-z • (f z*b^2)=b := by
      simpa only [sub_mul,smul_mul_assoc,mul_assoc,pow_two,one_mul] using
        congrArg (fun x : E => x*b) h1
    have h1' : z • (f z*b)=f z-1 := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp h1).symm
    have h2' : z • (f z*b^2)=f z*b-b := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp h2).symm
    calc (z^2) • g z = z • (z • (f z*b^2)) := by rw [smul_smul,pow_two]
         _ = z • (f z*b-b) := by rw [h2']
         _ = f z-1-z • b := by rw [smul_sub,h1']
  have hnorm (z : ℂ) : ‖z‖^2*‖g z‖ ≤ ‖f z‖+‖(1:E)‖+‖z‖*‖b‖ := by
    calc ‖z‖^2*‖g z‖ = ‖(z^2) • g z‖ := by rw [norm_smul,norm_pow]
         _ = ‖f z-1-z • b‖ := congrArg norm (he z)
         _ ≤ ‖f z-1‖+‖z • b‖ := norm_sub_le _ _
         _ ≤ (‖f z‖+‖(1:E)‖)+‖z‖*‖b‖ := by
           rw [norm_smul]
           linarith [norm_sub_le (f z) (1:E)]
  have hsmall : ∀ z : ℂ, 1≤‖z‖ → ‖g z‖≤(H+‖(1:E)‖+‖b‖)/‖z‖ := by
    intro z hz
    have hz0 : 0<‖z‖ := lt_of_lt_of_le zero_lt_one hz
    have hh : ‖z‖^2*‖g z‖≤H*‖z‖+‖(1:E)‖+‖z‖*‖b‖ := by
      have hh := hnorm z
      have hb : ‖f z‖≤H*‖z‖ := hbound z hz
      linarith
    apply (le_div_iff₀ hz0).mpr
    have hmul : ‖z‖*(‖g z‖*‖z‖) ≤ (H+‖(1:E)‖+‖b‖)*‖z‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hz (norm_nonneg (1:E))]
    exact (mul_le_mul_iff_right₀ hz0).mp (by nlinarith [hmul])
  have ht : Tendsto (fun z : ℂ => (H+‖(1:E)‖+‖b‖)/‖z‖) (cocompact ℂ) (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using
      (tendsto_norm_cocompact_atTop (E:=ℂ)).inv_tendsto_atTop.const_mul (H+‖(1:E)‖+‖b‖)
  have hgt : Tendsto g (cocompact ℂ) (𝓝 0) := by
    apply squeeze_zero_norm' _ ht
    filter_upwards [(tendsto_norm_cocompact_atTop (E:=ℂ)).eventually_ge_atTop 1] with z hz
    exact hsmall z hz
  have hh := hg.apply_eq_of_tendsto_cocompact 0 hgt
  simpa only [g,f,zero_smul,sub_zero,Ring.inverse_one,one_mul] using hh

/-- Convert the manuscript's quadratic small-resolvent estimate into the linear
growth hypothesis used above; no norm-smallness assumption on b is introduced. -/
theorem inverse_linear_growth_of_quadratic_resolvent_growth (b : E) (H : ℝ)
    (hbound : ∀ z : ℂ, 0<‖z‖ → ‖z‖≤1 →
      ‖Ring.inverse (algebraMap ℂ E z-b)‖≤H/‖z‖^2) :
    ∀ z : ℂ, 1≤‖z‖ → ‖Ring.inverse (1-z • b)‖≤H*‖z‖ := by
  intro z hz
  have hz0 : 0<‖z‖ := lt_of_lt_of_le zero_lt_one hz
  have hzne : z≠0 := norm_pos_iff.mp hz0
  have hinv : ‖z⁻¹‖≤1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hz
  have hh := hbound z⁻¹ (by simpa only [norm_inv] using inv_pos.mpr hz0) hinv
  have hscale : z⁻¹ • Ring.inverse (algebraMap ℂ E z⁻¹-b)=Ring.inverse (1-z • b) := by
    simpa only [resolvent,Units.smul_def,Units.val_mk0,Units.val_inv_eq_inv_val,
      inv_inv,map_one] using
      (spectrum.units_smul_resolvent_self (r:=Units.mk0 z⁻¹ (inv_ne_zero hzne)) (a:=b))
  rw [←hscale,norm_smul,norm_inv]
  calc ‖z‖⁻¹*‖Ring.inverse (algebraMap ℂ E z⁻¹-b)‖ ≤ ‖z‖⁻¹*(H/(‖z‖⁻¹)^2) :=
        mul_le_mul_of_nonneg_left (by simpa only [norm_inv] using hh) (inv_nonneg.mpr hz0.le)
       _ = H*‖z‖ := by field_simp [hz0.ne']

end SpectralIsometry.SquareZeroGrowth

