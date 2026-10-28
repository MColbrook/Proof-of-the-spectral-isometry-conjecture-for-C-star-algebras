module

public import SpectralIsometry.Basic
public import SpectralIsometry.SquareZeroGrowth
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Square Zero Preservation

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open scoped NNReal ENNReal

namespace SpectralIsometry.SquareZeroPreservation

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

private theorem radius_finite (a : A) : spectralRadius ℂ a≠⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜:=ℂ) a)

private theorem radiusReal_le_norm (a : A) : (spectralRadius ℂ a).toReal≤‖a‖ := by
  have hh := ENNReal.toReal_mono ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜:=ℂ) a)
  simpa using hh

private theorem radius_square_le_norm (a : A) :
    (spectralRadius ℂ a).toReal^2 ≤ ‖a^2‖ := by
  have hh := ENNReal.toReal_mono (radius_finite (a^2))
    (spectrum.spectralRadius_pow_le (𝕜:=ℂ) a 2 (by decide))
  rw [ENNReal.toReal_pow] at hh
  exact hh.trans (radiusReal_le_norm (a^2))

private theorem radius_zero_of_square_zero (n : A) (hn : n^2=0) :
    spectralRadius ℂ n=0 := by
  have hh : (spectralRadius ℂ n)^2≤0 := by
    simpa only [hn,spectrum.spectralRadius_zero] using
      spectrum.spectralRadius_pow_le (𝕜:=ℂ) n 2 (by decide)
  exact (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (le_zero_iff.mp hh)

private theorem unit_of_radiusReal_lt (v : B) (z : ℂ)
    (hh : (spectralRadius ℂ v).toReal<‖z‖) : IsUnit (algebraMap ℂ B z-v) := by
  by_contra hn
  have hm : z∈spectrum ℂ v := spectrum.mem_iff.mpr hn
  have hb : (‖z‖₊:ℝ≥0∞)≤spectralRadius ℂ v := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup_of_le z (le_iSup_of_le hm le_rfl)
  have ht := ENNReal.toReal_mono (radius_finite v) hb
  have ht' : ‖z‖≤(spectralRadius ℂ v).toReal := by simpa using ht
  exact (not_le.mpr hh) ht'

private theorem norm_square_perturbation (n h : A) (hn : n^2=0) :
    ‖(n+h)^2‖ ≤ 2*‖n‖*‖h‖+‖h‖^2 := by
  have he : (n+h)^2=n*h+h*n+h^2 := by
    calc (n+h)^2=n^2+n*h+h*n+h^2 := by noncomm_ring
         _ = n*h+h*n+h^2 := by rw [hn,zero_add]
  rw [he]
  have ha := norm_add_le (n*h+h*n) (h^2)
  have hb := norm_add_le (n*h) (h*n)
  have hpow : ‖h^2‖≤‖h‖^2 := by simpa only [pow_two] using norm_mul_le h h
  nlinarith [norm_mul_le n h,norm_mul_le h n]

/-- Original square-zero conclusion, with zero algebras included and with the
manuscript's constant rather than an assumed resolvent estimate. -/
theorem image_square_zero (U : A ≃L[ℂ] B)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (h1 : U 1=1)
    (n : A) (hn : n^2=0) : (U n)^2=0 := by
  rcases subsingleton_or_nontrivial B with hB|hB
  · letI := hB
    exact Subsingleton.elim _ _
  · letI := hB
    have hA10 : (1:A)≠0 := by
      intro hh
      have : (1:B)=0 := by rw [←h1,hh,map_zero]
      exact one_ne_zero this
    letI : Nontrivial A := nontrivial_of_ne (1:A) 0 hA10
    let b : B := U n
    let K : ℝ := ‖U.symm.toContinuousLinearMap‖
    let H : ℝ := 2*‖n‖*K+K^2
    have hInv1 : U.symm 1=1 := by
      apply U.injective
      rw [U.apply_symm_apply,h1]
    have hK1 : 1≤K := by
      simpa only [K,ContinuousLinearEquiv.coe_coe,hInv1,norm_one,mul_one] using
        U.symm.toContinuousLinearMap.le_opNorm (1:B)
    have hH1 : 1≤H := square_zero_constant_ge_one ‖n‖ K (norm_nonneg _) hK1
    have hH : 0<H := lt_of_lt_of_le zero_lt_one hH1
    have hb0 : spectralRadius ℂ b=0 := by
      calc spectralRadius ℂ (U n) = spectralRadius ℂ n := hr n
           _ = 0 := radius_zero_of_square_zero n hn
    have hpert (e : B) (he : ‖e‖≤1) :
        (spectralRadius ℂ (b+e)).toReal^2≤H*‖e‖ := by
      let h : A := U.symm e
      have hh : ‖h‖≤K*‖e‖ := U.symm.toContinuousLinearMap.le_opNorm e
      have heq : U (n+h)=b+e := by
        dsimp [b,h]
        rw [map_add,U.apply_symm_apply]
      have hrad : spectralRadius ℂ (b+e)=spectralRadius ℂ (n+h) := by
        rw [←heq]
        exact hr (n+h)
      rw [hrad]
      exact ((radius_square_le_norm (n+h)).trans (norm_square_perturbation n h hn)).trans
        (square_zero_perturbation_bound ‖n‖ K ‖e‖ ‖h‖ (norm_nonneg _) (norm_nonneg _)
          (norm_nonneg _) he (norm_nonneg _) hh)
    have hres (z : ℂ) (hz0 : 0<‖z‖) (hz1 : ‖z‖≤1) :
        ‖Ring.inverse (algebraMap ℂ B z-b)‖≤H/‖z‖^2 := by
      let c : B := algebraMap ℂ B z-b
      have hc : IsUnit c := unit_of_radiusReal_lt b z (by simpa only [hb0,ENNReal.toReal_zero] using hz0)
      have hzsq : 0<‖z‖^2 := pow_pos hz0 2
      have hd : ‖z‖^2/H≤Metric.infDist c {v : B|¬IsUnit v} := by
        apply (Metric.le_infDist ⟨0,not_isUnit_zero⟩).mpr
        intro v hv
        by_contra hfail
        have hnear : dist c v<‖z‖^2/H := lt_of_not_ge hfail
        let e : B := c-v
        have hen : ‖e‖<‖z‖^2/H := by simpa only [e,dist_eq_norm] using hnear
        have hd1 : ‖z‖^2/H≤1 := (div_le_one hH).mpr (by nlinarith [norm_nonneg z])
        have he1 : ‖e‖≤1 := hen.le.trans hd1
        have hsmall : H*‖e‖<‖z‖^2 := by
          calc H*‖e‖ < H*(‖z‖^2/H) := mul_lt_mul_of_pos_left hen hH
               _ = ‖z‖^2 := by field_simp [hH.ne']
        have hrr : (spectralRadius ℂ (b+e)).toReal<‖z‖ := by
          have hrr0 : 0≤(spectralRadius ℂ (b+e)).toReal := ENNReal.toReal_nonneg
          nlinarith [hpert e he1]
        have hunit := unit_of_radiusReal_lt (b+e) z hrr
        have hshift : algebraMap ℂ B z-(b+e)=v := by dsimp [c,e]; abel
        rw [hshift] at hunit
        exact hv hunit
      rw [distance_to_nonunits c hc] at hd
      have hInvnz : Ring.inverse c≠0 := by
        obtain ⟨u,hu⟩ := hc
        rw [←hu,Ring.inverse_unit]
        exact Units.ne_zero _
      have hInvpos : 0<‖Ring.inverse c‖ := norm_pos_iff.mpr hInvnz
      have hm := mul_le_mul_of_nonneg_right hd hInvpos.le
      rw [inv_mul_cancel₀ hInvpos.ne'] at hm
      have heq : (‖z‖^2/H)*‖Ring.inverse c‖=(‖Ring.inverse c‖*‖z‖^2)/H := by ring
      rw [heq] at hm
      apply (le_div_iff₀ hzsq).mpr
      simpa only [one_mul] using (div_le_iff₀ hH).mp hm
    exact SquareZeroGrowth.square_zero_of_inverse_linear_growth b hb0 H
      (SquareZeroGrowth.inverse_linear_growth_of_quadratic_resolvent_growth b H hres)

end SpectralIsometry.SquareZeroPreservation

