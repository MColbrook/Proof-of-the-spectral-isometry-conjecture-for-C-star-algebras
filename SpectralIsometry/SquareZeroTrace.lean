module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Square Zero Trace

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

namespace SpectralIsometry.SquareZeroPreserver

variable {A : Type*} [NonUnitalCStarAlgebra A]

def twoCopyHom (p r s : A) (hp : ∀ a : A, p * a = a ∧ a * p = a)
    (hr : star r * r = p) (hs : star s * s = p) (hrs : star r * s = 0) :
    A →⋆ₙₐ[ℂ] A where
  toFun a := r * a * star r + s * a * star s
  map_zero' := by simp
  map_add' a b := by noncomm_ring
  map_smul' c a := by
    change r * (c • a) * star r + s * (c • a) * star s =
      c • (r * a * star r + s * a * star s)
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  map_star' a := by simp only [star_add, star_mul, star_star, mul_assoc]
  map_mul' a b := by
    symm
    have hsr : star s * r = 0 := by simpa only [star_mul, star_star, star_zero] using congrArg star hrs
    calc
      (r * a * star r + s * a * star s) * (r * b * star r + s * b * star s) =
          r * (a * (star r * r) * b) * star r +
          r * (a * (star r * s) * b) * star s +
          s * (a * (star s * r) * b) * star r +
          s * (a * (star s * s) * b) * star s := by noncomm_ring
      _ = r * (a * b) * star r + s * (a * b) * star s := by
        rw [hr, hs, hrs, hsr, (hp a).2]
        simp

theorem twoCopyHom_injective (p r s : A) (hp : ∀ a : A, p * a = a ∧ a * p = a)
    (hr : star r * r = p) (hs : star s * s = p) (hrs : star r * s = 0) :
    Function.Injective (twoCopyHom p r s hp hr hs hrs) := by
  have hsr : star s * r = 0 := by simpa only [star_mul, star_star, star_zero] using congrArg star hrs
  have hinv (a : A) : star r * twoCopyHom p r s hp hr hs hrs a * r = a := by
    change star r * (r * a * star r + s * a * star s) * r = a
    calc
      star r * (r * a * star r + s * a * star s) * r =
          (star r * r) * a * (star r * r) + (star r * s) * a * (star s * r) := by noncomm_ring
      _ = a := by rw [hr, hrs, hsr, (hp a).1, (hp a).2]; simp
  intro a b hab
  exact (hinv a).symm.trans ((congrArg (fun x => star r * x * r) hab).trans (hinv b))

def twoCopyCLM (p r s : A) (hp : ∀ a : A, p * a = a ∧ a * p = a)
    (hr : star r * r = p) (hs : star s * s = p) (hrs : star r * s = 0) : A →L[ℂ] A :=
  ({ toFun := twoCopyHom p r s hp hr hs hrs
     map_add' := map_add (twoCopyHom p r s hp hr hs hrs)
     map_smul' := map_smul (twoCopyHom p r s hp hr hs hrs) } : A →ₗ[ℂ] A).mkContinuous 1
    (fun a => by
      change ‖twoCopyHom p r s hp hr hs hrs a‖ ≤ 1 * ‖a‖
      rw [one_mul, NonUnitalStarAlgHom.norm_map (twoCopyHom p r s hp hr hs hrs)
        (twoCopyHom_injective p r s hp hr hs hrs)])

set_option maxHeartbeats 800000 in
theorem bounded_trace_zero_of_two_copies (p r s : A)
    (hp : ∀ a : A, p * a = a ∧ a * p = a)
    (hr : star r * r = p) (hs : star s * s = p) (hrs : star r * s = 0)
    (F : StrongDual ℂ A) (htrace : ∀ a b : A, F (a * b) = F (b * a)) : F = 0 := by
  let Φ := twoCopyCLM p r s hp hr hs hrs
  have hΦnorm : ‖Φ‖ ≤ 1 := by
    apply Φ.opNorm_le_bound (by norm_num)
    intro a
    change ‖twoCopyHom p r s hp hr hs hrs a‖ ≤ 1 * ‖a‖
    rw [one_mul, NonUnitalStarAlgHom.norm_map (twoCopyHom p r s hp hr hs hrs)
      (twoCopyHom_injective p r s hp hr hs hrs)]
  have hFr (a : A) : F (r * a * star r) = F a := by
    rw [htrace (r * a) (star r), ← mul_assoc, hr, (hp a).1]
  have hFs (a : A) : F (s * a * star s) = F a := by
    rw [htrace (s * a) (star s), ← mul_assoc, hs, (hp a).1]
  have heq : F.comp Φ = (2 : ℂ) • F := by
    ext a
    change F (r * a * star r + s * a * star s) = (2 : ℂ) • F a
    rw [map_add, hFr, hFs, two_smul]
  have hnorm : (2 : ℝ) * ‖F‖ ≤ ‖F‖ := by
    calc
      (2 : ℝ) * ‖F‖ = ‖(2 : ℂ) • F‖ := by simp only [norm_smul]; norm_num
      _ = ‖F.comp Φ‖ := congrArg norm heq.symm
      _ ≤ ‖F‖ * ‖Φ‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖F‖ := mul_le_of_le_one_right (norm_nonneg F) hΦnorm
  apply norm_eq_zero.mp
  have := norm_nonneg F
  linarith

end SpectralIsometry.SquareZeroPreserver

