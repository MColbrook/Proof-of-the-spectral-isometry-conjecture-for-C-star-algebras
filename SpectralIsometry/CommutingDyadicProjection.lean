module

public import OAI.Analysis.BoundedHochschild.SpectralProjections
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Commuting Dyadic Projection

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open scoped ComplexOrder CStarAlgebra
open OAI.HochschildSakai

namespace SpectralIsometry.SquareZeroPreserver

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_commuting_dyadic_projection
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : M, IsStarProjection p ∧ Commute a p ∧
      0 ≤ (2 : ℝ) • a - p ∧ (2 : ℝ) • a - p ≤ 1 := by
  let b : M := a-(1/2:ℝ) • (1:M)
  let c : M := b⁺
  let d : M := b⁻
  have hbsa : IsSelfAdjoint b := (IsSelfAdjoint.of_nonneg ha0).sub
    (IsSelfAdjoint.of_nonneg (smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) zero_le_one))
  have hb : c-d=b := CFC.posPart_sub_negPart b hbsa
  have hc0 : 0 ≤ c := CFC.posPart_nonneg b
  have hd0 : 0 ≤ d := CFC.negPart_nonneg b
  obtain ⟨p,hp⟩ := exists_support_projection e c hc0
  have hpd : p*d=0 := hp.annihilate d (CFC.posPart_mul_negPart b)
  have hdp : d*p=0 := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg hd0).star_eq,
      hp.proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hpd
  have hcp : b*p=c := by rw [← hb,sub_mul,hp.right,hdp,sub_zero]
  have hpc : p*b=c := by rw [← hb,mul_sub,hp.left,hpd,sub_zero]
  have hac : Commute a p := by
    change a*p=p*a
    have hh := hcp.trans hpc.symm
    dsimp [b] at hh
    simpa only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
      sub_left_inj] using hh
  have har : 0 ≤ a*(1-p) :=
    (show Commute a (1-p) from (Commute.one_right a).sub_right hac).mul_nonneg ha0
      (sub_nonneg.mpr hp.proj.le_one)
  have hal : 0 ≤ (1-a)*p :=
    ((Commute.one_left p).sub_left hac).mul_nonneg (sub_nonneg.mpr ha1) hp.proj.nonneg
  have hpa : a*p=c+(1/2:ℝ) • p := by
    dsimp [b] at hcp
    rw [sub_mul,smul_mul_assoc,one_mul] at hcp
    exact sub_eq_iff_eq_add.mp hcp
  have hlow : 0 ≤ a-(1/2:ℝ) • p := by
    have he : a-(1/2:ℝ) • p=c+a*(1-p) := by
      rw [mul_sub,mul_one,hpa]
      module
    rw [he]
    exact add_nonneg hc0 har
  have hhigh : 0 ≤ (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p) := by
    have he : (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p)=(1-a)*p+d := by
      rw [sub_mul,one_mul,hpa]
      have haa : a=c-d+(1/2:ℝ) • (1:M) := by
        exact (sub_eq_iff_eq_add.mp hb.symm)
      conv_lhs => rw [haa]
      module
    rw [he]
    exact add_nonneg hal hd0
  refine ⟨p,hp.proj,hac,?_,?_⟩
  · have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlow
    convert hh using 1; module
  · apply sub_nonneg.mp
    have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hhigh
    convert hh using 1; module

end SpectralIsometry.SquareZeroPreserver

