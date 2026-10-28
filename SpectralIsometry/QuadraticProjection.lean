module

public import SpectralIsometry.CommutingDyadicProjection
public import OAI.Analysis.BoundedHochschild.Corners
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Quadratic Projection

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open scoped ComplexOrder CStarAlgebra
open Filter Topology
open OAI.HochschildCorners

namespace SpectralIsometry.QuadraticProjection

variable {M X Y : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

private theorem orthogonal_zero (β : M →L[ℂ] M →L[ℂ] Y)
    (hs : ∀ a b, β a b = β b a)
    (hproj : ∀ p : M, IsStarProjection p → β p p = 0)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p*q=0) :
    β p q = 0 := by
  have hh := hproj (p+q) (hp.add hq hpq)
  simp only [map_add, ContinuousLinearMap.add_apply, hproj p hp, hproj q hq,
    hs q p, zero_add, add_zero] at hh
  have hh' : (2:ℂ) • β p q=0 := by simpa only [two_smul ℂ] using hh
  exact (smul_eq_zero.mp hh').resolve_left (by norm_num)

private theorem subprojection_zero (β : M →L[ℂ] M →L[ℂ] Y)
    (hs : ∀ a b, β a b = β b a)
    (hproj : ∀ p : M, IsStarProjection p → β p p = 0)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q≤p) :
    β p q=0 := by
  have hmul : q*p=q := (hq.le_iff_mul_eq_left hp).mp hqp
  have hsub := hq.sub_of_mul_eq_left hp hmul
  have hz : q*(p-q)=0 := by rw [mul_sub,hmul,hq.isIdempotentElem.eq,sub_self]
  have hh := orthogonal_zero β hs hproj hq hsub hz
  simp only [map_sub,hproj q hq,sub_zero] at hh
  exact (hs p q).trans hh

private theorem projection_commuting_zero
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (β : M →L[ℂ] M →L[ℂ] Y)
    (hs : ∀ a b, β a b = β b a)
    (hproj : ∀ p : M, IsStarProjection p → β p p=0)
    {p a : M} (hp : IsStarProjection p) (hac : Commute a p) : β p a=0 := by
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R:=ℂ)
  intro F
  let G : StrongDual ℂ M := F.comp (β p)
  have h1 : G (p*a*p)=0 := dual_zero_on_corner e G hp (by
    intro q hq hqp
    change F (β p q)=0
    rw [subprojection_zero β hs hproj hp hq hqp,map_zero]) (compress_mem_corner hp a)
  have h2 : G ((1-p)*a*(1-p))=0 := dual_zero_on_corner e G hp.one_sub (by
    intro q hq hqp
    have hh : q*(1-p)=q := (hq.le_iff_mul_eq_left hp.one_sub).mp hqp
    rw [mul_sub,mul_one] at hh
    have hqp0 : q*p=0 := sub_eq_self.mp hh
    change F (β p q)=0
    rw [hs p q,orthogonal_zero β hs hproj hq hp hqp0,map_zero])
      (compress_mem_corner hp.one_sub a)
  have hpap : p*a*p=p*a := by
    rw [mul_assoc,hac.eq,←mul_assoc,hp.isIdempotentElem.eq]
  have hqc : Commute a (1-p) := (Commute.one_right a).sub_right hac
  have hqaq : (1-p)*a*(1-p)=(1-p)*a := by
    rw [mul_assoc,hqc.eq,←mul_assoc,hp.one_sub.isIdempotentElem.eq]
  have hsum : p*a*p+(1-p)*a*(1-p)=a := by
    rw [hpap,hqaq,←add_mul,add_sub_cancel,one_mul]
  change G a=0
  rw [←hsum,map_add,h1,h2,add_zero]

private theorem positive_contraction_diagonal_zero
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (β : M →L[ℂ] M →L[ℂ] Y)
    (hs : ∀ a b, β a b = β b a)
    (hproj : ∀ p : M, IsStarProjection p → β p p=0)
    {a : M} (ha0 : 0≤a) (ha1 : a≤1) : β a a=0 := by
  have hbound : ∀ n : ℕ, ∀ b : M, 0≤b → b≤1 →
      ‖β b b‖ ≤ (1/4:ℝ)^n * ‖β‖ := by
    intro n
    induction n with
    | zero =>
      intro b hb0 hb1
      have hbn : ‖b‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg b hb0).mpr hb1
      simpa only [pow_zero,one_mul] using
        ((β b).le_opNorm b).trans (calc
          ‖β b‖*‖b‖ ≤ (‖β‖*‖b‖)*‖b‖ :=
            mul_le_mul_of_nonneg_right (β.le_opNorm b) (norm_nonneg b)
          _ ≤ (‖β‖*1)*1 := by gcongr
          _ = ‖β‖ := by ring)
    | succ n ih =>
      intro b hb0 hb1
      obtain ⟨p,hp,hbp,hc0,hc1⟩ :=
        SquareZeroPreserver.exists_commuting_dyadic_projection e b hb0 hb1
      have hpb := projection_commuting_zero e β hs hproj hp hbp
      have hbp' : β b p=0 := (hs b p).trans hpb
      have he : β ((2:ℝ) • b-p) ((2:ℝ) • b-p)=(4:ℂ) • β b b := by
        simp only [←Complex.coe_smul,map_sub,map_smul,ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply,hpb,hbp',hproj p hp,smul_zero,sub_zero,
          zero_sub,sub_neg_eq_add]
        module
      have hh := ih ((2:ℝ) • b-p) hc0 hc1
      rw [he,norm_smul] at hh
      norm_num at hh
      rw [pow_succ]
      nlinarith
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have ht : Tendsto (fun n : ℕ => (1/4:ℝ)^n * ‖β‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/4)
        (by norm_num : (1/4:ℝ)<1)).mul_const ‖β‖
  exact ge_of_tendsto ht (Eventually.of_forall fun n => hbound n a ha0 ha1)

private theorem positive_diagonal_zero
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (β : M →L[ℂ] M →L[ℂ] Y)
    (hs : ∀ a b, β a b = β b a)
    (hproj : ∀ p : M, IsStarProjection p → β p p=0)
    {a : M} (ha : 0≤a) : β a a=0 := by
  let r : ℝ := ‖a‖+1
  have hr : 0<r := by dsimp [r]; positivity
  let c : M := r⁻¹ • a
  have hc0 : 0≤c := smul_nonneg (inv_nonneg.mpr hr.le) ha
  have hcn : ‖c‖≤1 := by
    dsimp [c]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hh := positive_contraction_diagonal_zero e β hs hproj hc0
    ((CStarAlgebra.norm_le_one_iff_of_nonneg c hc0).mp hcn)
  have hac : a=r • c := by
    dsimp [c]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  calc β a a = β (r • c) (r • c) := by rw [←hac]
       _ = 0 := by simp only [←Complex.coe_smul,map_smul,
         ContinuousLinearMap.smul_apply,hh,smul_zero]

/-- A continuous symmetric complex bilinear map on a von Neumann algebra is zero
if its diagonal vanishes on every projection. The supplied predual is actual
structure; no density of projections is assumed. -/
theorem bilinear_eq_zero_of_projection_diagonal_zero
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (β : M →L[ℂ] M →L[ℂ] Y)
    (hs : ∀ a b, β a b = β b a)
    (hproj : ∀ p : M, IsStarProjection p → β p p=0) : β=0 := by
  have hpos (a b : M) (ha : 0≤a) (hb : 0≤b) : β a b=0 := by
    have hh := positive_diagonal_zero e β hs hproj (add_nonneg ha hb)
    simp only [map_add,ContinuousLinearMap.add_apply,
      positive_diagonal_zero e β hs hproj ha,
      positive_diagonal_zero e β hs hproj hb,hs b a,zero_add,add_zero] at hh
    have hh' : (2:ℂ) • β a b=0 := by simpa only [two_smul ℂ] using hh
    exact (smul_eq_zero.mp hh').resolve_left (by norm_num)
  have hleft (a : M) (ha : 0≤a) (b : M) : β a b=0 := by
    have hk : (⊤ : Submodule ℂ M) ≤ (β a).ker := by
      rw [←CStarAlgebra.span_nonneg]
      exact Submodule.span_le.mpr (fun b hb => hpos a b ha hb)
    exact hk Submodule.mem_top
  ext a b
  have hk : (⊤ : Submodule ℂ M) ≤ (β.flip b).ker := by
    rw [←CStarAlgebra.span_nonneg]
    exact Submodule.span_le.mpr (fun a ha => hleft a ha b)
  exact hk Submodule.mem_top

end SpectralIsometry.QuadraticProjection

