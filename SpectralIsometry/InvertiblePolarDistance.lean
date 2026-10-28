module

public import SpectralIsometry.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Invertible Polar Distance

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.InvertiblePolarDistance

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
local instance orderedA : PartialOrder A := CStarAlgebra.spectralOrder A
local instance starOrderedA : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance complexOrder : PartialOrder ℂ := Complex.partialOrder

def polarFactor (c : A) : A := c*Ring.inverse (CFC.abs c)

theorem modulus_isUnit (c : A) (hc : IsUnit c) : IsUnit (CFC.abs c) :=
  (CFC.isUnit_sqrt_iff (star c*c) (star_mul_self_nonneg c)).mpr (hc.star.mul hc)

theorem polarFactor_mem_unitary (c : A) (hc : IsUnit c) : polarFactor c ∈ unitary A := by
  have ha := modulus_isUnit c hc
  have hsa := (CFC.abs_nonneg c).isSelfAdjoint.ringInverse
  apply (hc.mul ha.ringInverse).mem_unitary_of_star_mul_self
  change star (c*Ring.inverse (CFC.abs c))*(c*Ring.inverse (CFC.abs c))=1
  rw [star_mul,hsa.star_eq]
  calc
    (Ring.inverse (CFC.abs c)*star c)*(c*Ring.inverse (CFC.abs c))=
        Ring.inverse (CFC.abs c)*(star c*c)*Ring.inverse (CFC.abs c) := by noncomm_ring
    _ = (Ring.inverse (CFC.abs c)*CFC.abs c)*(CFC.abs c*Ring.inverse (CFC.abs c)) := by
      rw [← CFC.abs_mul_abs c]
      noncomm_ring
    _ = 1 := by rw [Ring.inverse_mul_cancel _ ha,Ring.mul_inverse_cancel _ ha,one_mul]

theorem polar_decomposition (c : A) (hc : IsUnit c) : c=polarFactor c*CFC.abs c := by
  dsimp [polarFactor]
  rw [mul_assoc,Ring.inverse_mul_cancel _ (modulus_isUnit c hc),mul_one]

theorem inverse_polar_formula (c : A) (hc : IsUnit c) :
    Ring.inverse c=Ring.inverse (CFC.abs c)*star (polarFactor c) := by
  have ha := modulus_isUnit c hc
  have hv := polarFactor_mem_unitary c hc
  have hr : c*(Ring.inverse (CFC.abs c)*star (polarFactor c))=1 := by
    calc
      c*(Ring.inverse (CFC.abs c)*star (polarFactor c))=
          (polarFactor c*CFC.abs c)*(Ring.inverse (CFC.abs c)*star (polarFactor c)) :=
        congrArg (fun x : A => x*(Ring.inverse (CFC.abs c)*star (polarFactor c)))
          (polar_decomposition c hc)
      _ = polarFactor c*(CFC.abs c*Ring.inverse (CFC.abs c))*star (polarFactor c) := by noncomm_ring
      _ = 1 := by rw [Ring.mul_inverse_cancel _ ha,mul_one,Unitary.mul_star_self_of_mem hv]
  calc
    Ring.inverse c=Ring.inverse c*(c*(Ring.inverse (CFC.abs c)*star (polarFactor c))) := by rw [hr,mul_one]
    _ = (Ring.inverse c*c)*(Ring.inverse (CFC.abs c)*star (polarFactor c)) := by noncomm_ring
    _ = _ := by rw [Ring.inverse_mul_cancel _ hc,one_mul]

theorem inverse_norm_eq_modulus_inverse_norm (c : A) (hc : IsUnit c) :
    ‖Ring.inverse c‖=‖Ring.inverse (CFC.abs c)‖ := by
  rw [inverse_polar_formula c hc]
  exact CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (polarFactor_mem_unitary c hc))

/-- A positive invertible element has its smallest real spectral value at the
reciprocal inverse norm. Existence is witnessed by the maximum inverse norm. -/
theorem positive_unit_spectrum_isLeast (a : Aˣ) (ha : (0:A)≤a) :
    IsLeast (spectrum ℝ (a:A)) ‖(↑a⁻¹:A)‖⁻¹ := by
  have hnpos := Units.norm_pos a⁻¹
  refine ⟨?_,?_⟩
  · exact spectrum.inv₀_mem_iff.mpr
      (CStarAlgebra.norm_mem_spectrum_of_nonneg (↑a⁻¹:A) (CFC.inv_nonneg_of_nonneg a ha))
  · intro r hr
    have hr0 : r≠0 := by
      intro he
      exact (spectrum.zero_notMem ℝ a.isUnit) (he ▸ hr)
    have hrpos : 0<r := lt_of_le_of_ne (spectrum_nonneg_of_nonneg ha hr) hr0.symm
    have hir : r⁻¹ ∈ spectrum ℝ (↑a⁻¹:A) := spectrum.inv₀_mem_inv_iff.mpr hr
    have hbound : r⁻¹≤‖(↑a⁻¹:A)‖ := by
      simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hrpos)] using spectrum.norm_le_norm_of_mem hir
    exact (inv_le_comm₀ hnpos hrpos).mpr hbound

theorem modulus_spectrum_isLeast (c : A) (hc : IsUnit c) :
    IsLeast (spectrum ℝ (CFC.abs c)) ‖Ring.inverse c‖⁻¹ := by
  obtain ⟨a,ha⟩ := modulus_isUnit c hc
  have hapos : (0:A)≤a := by rw [ha]; exact CFC.abs_nonneg c
  have h := positive_unit_spectrum_isLeast a hapos
  have hi : (↑a⁻¹:A)=Ring.inverse (CFC.abs c) := by rw [←ha,Ring.inverse_unit]
  rw [ha,hi,←inverse_norm_eq_modulus_inverse_norm c hc] at h
  exact h

theorem modulus_spectral_infimum (c : A) (hc : IsUnit c) :
    sInf (spectrum ℝ (CFC.abs c))=‖Ring.inverse c‖⁻¹ :=
  (modulus_spectrum_isLeast c hc).csInf_eq

/-- Literal complex-spectrum reading of the source minimum; all spectral
values of the positive modulus are real, ordered by Complex.partialOrder. -/
theorem modulus_complex_spectrum_isLeast (c : A) (hc : IsUnit c) :
    IsLeast (spectrum ℂ (CFC.abs c)) ((‖Ring.inverse c‖⁻¹:ℝ):ℂ) := by
  have hm := modulus_spectrum_isLeast c hc
  refine ⟨spectrum.algebraMap_mem ℂ hm.1,?_⟩
  intro z hz
  have hsa : IsSelfAdjoint (CFC.abs c) := (CFC.abs_nonneg c).isSelfAdjoint
  have he : z=(z.re:ℂ) := hsa.mem_spectrum_eq_re hz
  have hr : z.re ∈ spectrum ℝ (CFC.abs c) := spectrum.of_algebraMap_mem ℂ (he ▸ hz)
  rw [he]
  exact Complex.real_le_real.mpr (hm.2 hr)

theorem minimum_positive (c : A) (hc : IsUnit c) : 0<‖Ring.inverse c‖⁻¹ :=
  inv_pos.mpr (norm_pos_iff.mpr hc.ringInverse.ne_zero)

theorem polar_boundary_nonunit (c : A) (hc : IsUnit c) :
    ¬IsUnit (c-‖Ring.inverse c‖⁻¹ • polarFactor c) := by
  let m : ℝ := ‖Ring.inverse c‖⁻¹
  have hbad : ¬IsUnit (CFC.abs c-m • (1:A)) := by
    intro h
    apply (spectrum.mem_iff.mp (modulus_spectrum_isLeast c hc).1)
    simpa only [neg_sub,Algebra.algebraMap_eq_smul_one] using h.neg
  have hfactor : c-m • polarFactor c=polarFactor c*(CFC.abs c-m • (1:A)) := by
    calc
      c-m • polarFactor c=(polarFactor c*CFC.abs c)-m • polarFactor c :=
        congrArg (fun x : A => x-m • polarFactor c) (polar_decomposition c hc)
      _ = _ := by rw [mul_sub,mul_smul_comm,mul_one]
  intro hb
  have hunitv : IsUnit (polarFactor c) := hc.mul (modulus_isUnit c hc).ringInverse
  have h := hunitv.star.mul hb
  rw [hfactor,←mul_assoc,Unitary.star_mul_self_of_mem (polarFactor_mem_unitary c hc),one_mul] at h
  exact hbad h

theorem polar_boundary_distance (c : A) (hc : IsUnit c) :
    ‖c-(c-‖Ring.inverse c‖⁻¹ • polarFactor c)‖=‖Ring.inverse c‖⁻¹ := by
  have he : c-(c-‖Ring.inverse c‖⁻¹ • polarFactor c)=‖Ring.inverse c‖⁻¹ • polarFactor c := by abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    CStarRing.norm_of_mem_unitary (polarFactor_mem_unitary c hc),mul_one]

/-- The literal explicit nearest nonunit of the source proof. -/
theorem polar_nearest_nonunit (c : A) (hc : IsUnit c) :
    ¬IsUnit (c-‖Ring.inverse c‖⁻¹ • polarFactor c) ∧
      ‖c-(c-‖Ring.inverse c‖⁻¹ • polarFactor c)‖=‖Ring.inverse c‖⁻¹ ∧
      Metric.infDist c {b:A | ¬IsUnit b}=‖c-(c-‖Ring.inverse c‖⁻¹ • polarFactor c)‖ :=
  ⟨polar_boundary_nonunit c hc,polar_boundary_distance c hc,
    (distance_to_nonunits c hc).trans (polar_boundary_distance c hc).symm⟩

end SpectralIsometry.InvertiblePolarDistance

