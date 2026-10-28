module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Support Function Limit

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology Complex

namespace SpectralIsometry.SupportFunctionLimit

def farthestDistance (K : Set ℂ) (c : ℂ) : ℝ := sSup ((fun w => ‖w-c‖) '' K)
def support (K : Set ℂ) (r : ℂ) : ℝ := sSup ((fun w => (r*w).re) '' K)

private theorem maximum_eq_sSup (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (f : ℂ → ℝ) (hf : Continuous f) :
    ∃ w∈K, sSup (f '' K)=f w ∧ ∀ v∈K, f v≤f w := by
  obtain ⟨w,hw,hm⟩ := hK.exists_isMaxOn hne hf.continuousOn
  refine ⟨w,hw,?_,hm⟩
  apply le_antisymm
  · apply csSup_le (hne.image f)
    rintro _ ⟨v,hv,rfl⟩
    exact hm hv
  · apply le_csSup
    · exact ⟨f w,by rintro _ ⟨v,hv,rfl⟩; exact hm hv⟩
    · exact ⟨w,hw,rfl⟩

theorem norm_remainder_bound (w : ℂ) (M t : ℝ) (hM : 0≤M)
    (hw : ‖w‖≤M) (ht : 0<t) (htM : 2*M≤t) :
    0≤‖(t:ℂ)+w‖-t-w.re ∧ ‖(t:ℂ)+w‖-t-w.re≤M^2/t := by
  have hre : |w.re|≤M := (abs_re_le_norm w).trans hw
  have hrlo : -M≤w.re := (abs_le.mp hre).1
  have hn : t+w.re≤‖(t:ℂ)+w‖ := by
    simpa only [add_re,ofReal_re] using re_le_norm ((t:ℂ)+w)
  have hsq : ‖(t:ℂ)+w‖^2=(t+w.re)^2+w.im^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [add_re,add_im,ofReal_re,ofReal_im,zero_add,pow_two]
  have hw2 : w.re^2+w.im^2≤M^2 := by
    have hh : ‖w‖^2≤M^2 := by nlinarith [norm_nonneg w]
    rw [Complex.sq_norm,Complex.normSq_apply] at hh
    nlinarith only [hh]
  have hd : 0≤‖(t:ℂ)+w‖-t-w.re := by linarith
  have hs : t≤‖(t:ℂ)+w‖+t+w.re := by linarith
  refine ⟨hd,(le_div_iff₀ ht).mpr ?_⟩
  have hm := mul_le_mul_of_nonneg_left hs hd
  nlinarith [sq_nonneg w.re]

private theorem rotated_norm (u r w : ℂ) (hu : ‖r‖=1) (hru : r*u=1) (t : ℝ) :
    ‖w-(-(t:ℂ)*u)‖=‖(t:ℂ)+r*w‖ := by
  calc
    ‖w-(-(t:ℂ)*u)‖=‖r*(w-(-(t:ℂ)*u))‖ := by rw [norm_mul,hu,one_mul]
    _=‖(t:ℂ)+r*w‖ := by
      congr 1
      calc r*(w-(-(t:ℂ)*u))=r*w+(t:ℂ)*(r*u) := by ring
           _=(t:ℂ)+r*w := by rw [hru,mul_one,add_comm]

theorem farthestDistance_support_limit (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (u r : ℂ) (hr : ‖r‖=1) (hru : r*u=1) :
    Tendsto (fun t : ℝ => farthestDistance K (-(t:ℂ)*u)-t) atTop (𝓝 (support K r)) := by
  obtain ⟨M0,hM0⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let M : ℝ := max M0 0
  have hM : 0≤M := le_max_right _ _
  have hw (w : ℂ) (hw : w∈K) : ‖r*w‖≤M := by
    rw [norm_mul,hr,one_mul]
    exact (hM0 w hw).trans (le_max_left _ _)
  obtain ⟨v,hv,hs,hmax⟩ := maximum_eq_sSup K hK hne (fun w => (r*w).re) (by fun_prop)
  change sSup ((fun w => (r*w).re) '' K)=(r*v).re at hs
  have hs' : support K r=(r*v).re := hs
  have hb : ∀ᶠ t : ℝ in atTop,
      support K r≤farthestDistance K (-(t:ℂ)*u)-t ∧
      farthestDistance K (-(t:ℂ)*u)-t≤support K r+M^2/t := by
    filter_upwards [eventually_ge_atTop (max 1 (2*M))] with t ht
    have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans ht)
    have htM : 2*M≤t := (le_max_right _ _).trans ht
    obtain ⟨w,hwK,hd,hdmax⟩ := maximum_eq_sSup K hK hne
      (fun w => ‖w-(-(t:ℂ)*u)‖) (by fun_prop)
    change farthestDistance K (-(t:ℂ)*u)=‖w-(-(t:ℂ)*u)‖ at hd
    have hnv := norm_remainder_bound (r*v) M t hM (hw v hv) ht0 htM
    have hnw := norm_remainder_bound (r*w) M t hM (hw w hwK) ht0 htM
    have hvw := hdmax v hv
    rw [rotated_norm u r v hr hru t,rotated_norm u r w hr hru t] at hvw
    have hws := hmax w hwK
    rw [hd,rotated_norm u r w hr hru t,hs']
    constructor <;> linarith
  have hlim : Tendsto (fun t : ℝ => support K r+M^2/t) atTop (𝓝 (support K r)) := by
    simpa only [div_eq_mul_inv,mul_zero,add_zero] using
      (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul (M^2)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

theorem angular_support_limit (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) (θ : ℝ) :
    Tendsto (fun t : ℝ => farthestDistance K (-(t:ℂ)*exp ((θ:ℂ)*I))-t) atTop
      (𝓝 (support K (exp (-((θ:ℂ)*I))))) := by
  apply farthestDistance_support_limit K hK hne
  · simpa only [neg_mul,ofReal_neg] using norm_exp_ofReal_mul_I (-θ)
  · rw [←exp_add,neg_add_cancel,exp_zero]

end SpectralIsometry.SupportFunctionLimit

