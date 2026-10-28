module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weak Hilbert Bounds

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace SpectralIsometry.WeakHilbertBounds

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The exact squared-norm lower bound follows from scalar weak limits; no
completeness or countable/separable topology is used. The nonbottom premise
is necessary for a bound on the limit, and is proved for our approximation nets. -/
theorem norm_sq_le_of_weak_limit {l : Filter ι} [l.NeBot]
    (a : ι → E) (v : E) (r : ι → ℝ) (R : ℝ)
    (ha : ∀ η : E, Tendsto (fun i => ⟪η,a i⟫_ℂ) l (𝓝 ⟪η,v⟫_ℂ))
    (hr : Tendsto r l (𝓝 R)) (hb : ∀ᶠ i in l, ‖a i‖^2≤r i) :
    ‖v‖^2≤R := by
  have hR : 0≤R := le_of_tendsto_of_tendsto tendsto_const_nhds hr
    (hb.mono fun i hi => (sq_nonneg ‖a i‖).trans hi)
  by_cases hv : v=0
  · simpa only [hv,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using hR
  have hlim : Tendsto (fun i => ‖⟪v,a i⟫_ℂ‖^2) l (𝓝 ((‖v‖^2)^2)) := by
    have hh := ((ha v).norm).pow 2
    simpa only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg v)] using hh
  have hright : Tendsto (fun i => ‖v‖^2*r i) l (𝓝 (‖v‖^2*R)) := hr.const_mul _
  have hbound : ∀ᶠ i in l, ‖⟪v,a i⟫_ℂ‖^2≤‖v‖^2*r i := by
    filter_upwards [hb] with i hi
    have hc : ‖⟪v,a i⟫_ℂ‖≤‖v‖*‖a i‖ := norm_inner_le_norm v (a i)
    have hcsq : ‖⟪v,a i⟫_ℂ‖^2≤‖v‖^2*‖a i‖^2 := by
      have hs := pow_le_pow_left₀ (norm_nonneg ⟪v,a i⟫_ℂ) hc 2
      simpa only [mul_pow] using hs
    exact hcsq.trans (mul_le_mul_of_nonneg_left hi (sq_nonneg ‖v‖))
  have hh : (‖v‖^2)^2≤‖v‖^2*R := le_of_tendsto_of_tendsto hlim hright hbound
  have hvp : 0<‖v‖^2 := pow_pos (norm_pos_iff.mpr hv) 2
  have hh' : ‖v‖^2*‖v‖^2≤R*‖v‖^2 := by
    calc ‖v‖^2*‖v‖^2 = (‖v‖^2)^2 := (pow_two _).symm
         _ ≤ ‖v‖^2*R := hh
         _ = R*‖v‖^2 := mul_comm _ _
  exact (mul_le_mul_iff_left₀ hvp).mp hh'

/-- Vanishing positive scalar control of squared norm gives actual norm
convergence, for any filter including the bottom filter. -/
theorem tendsto_zero_of_norm_sq_bound {l : Filter ι} (a : ι → E) (r : ι → ℝ)
    (hr : Tendsto r l (𝓝 0)) (hb : ∀ᶠ i in l, ‖a i‖^2≤r i) :
    Tendsto a l (𝓝 0) := by
  have hsq : Tendsto (fun i => ‖a i‖^2) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i => sq_nonneg ‖a i‖) hb hr
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hn' : Tendsto (fun i => ‖a i‖) l (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
      Real.sqrt_zero] using hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn'

end SpectralIsometry.WeakHilbertBounds

