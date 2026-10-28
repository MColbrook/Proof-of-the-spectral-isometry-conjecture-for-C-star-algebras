module

public import SpectralIsometry.Normalization
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Normalization Unitary

Supporting results for spectral isometries of complex unital C*-algebras.
-/

/- Original ordinary-linear onto/radius normalization development. No main
Jordan conclusion is claimed here. Exact finite positivity certificates and
Gelfand powers reuse pinned Mathlib; no character-space or native oracle.
Root AI supplied the mathematical plan; body authored by child AI. -/

@[expose] public section
noncomputable section
open Filter Topology
open scoped CStarAlgebra
namespace SpectralIsometry.Normalization
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
/- Untested continuation for the original-hypothesis normalization proof.
No theorem in this text is assumed before being checked. -/

private theorem central_star {c : A} (hc : Central c) : Central (star c) := by
  intro x
  have he := congrArg star (hc (star x))
  simpa only [star_mul, star_star] using he.symm

private theorem central_add {c d : A} (hc : Central c) (hd : Central d) : Central (c+d) := by
  intro x
  simp only [add_mul, mul_add, hc x, hd x]

private theorem central_sub {c d : A} (hc : Central c) (hd : Central d) : Central (c-d) := by
  intro x
  simp only [sub_mul, mul_sub, hc x, hd x]

private theorem central_mul {c d : A} (hc : Central c) (hd : Central d) : Central (c*d) := by
  intro x
  rw [mul_assoc, hd x, ←mul_assoc, hc x, mul_assoc]

private theorem central_real_smul {c : A} (hc : Central c) (r : ℝ) : Central (r•c) := by
  intro x
  rw [smul_mul_assoc, mul_smul_comm, hc x]

private theorem normal_of_central {c : A} (hc : Central c) : IsStarNormal c := ⟨(hc (star c)).symm⟩

private theorem norm_eq_radius_of_central {c : A} (hc : Central c) :
    ‖c‖ = (spectralRadius ℂ c).toReal := by
  letI := normal_of_central hc
  rw [IsStarNormal.spectralRadius_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm]

/-- The unit is extreme in the full closed unit ball, proved by order algebra. -/
theorem eq_zero_of_one_add_sub_contractions (a : A)
    (hp : ‖1+a‖≤1) (hm : ‖1-a‖≤1) : a=0 := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  have hs (x : A) (hx : ‖x‖≤1) : star x*x≤1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg x)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg x]
  have h := add_le_add (hs (1+a) hp) (hs (1-a) hm)
  have he : star (1+a)*(1+a)+star (1-a)*(1-a) =
      ((1:A)+1)+(star a*a+star a*a) := by
    simp only [star_add, star_sub, star_one]
    noncomm_ring
  rw [he] at h
  have hle : star a*a+star a*a ≤ 0 := by
    exact (add_le_add_iff_left ((1:A)+1)).mp (by simpa only [add_zero] using h)
  apply (CStarRing.star_mul_self_eq_zero_iff a).mp
  exact le_antisymm ((le_add_of_nonneg_right (star_mul_self_nonneg a)).trans hle)
    (star_mul_self_nonneg a)

/-- Finite polynomial certificate gives two contractions around a central contraction. -/
theorem central_contraction_perturbations (c : A) (hc : Central c) (hn : ‖c‖≤1) :
    ‖c+(1/2:ℝ)•(1-star c*c)‖≤1 ∧ ‖c-(1/2:ℝ)•(1-star c*c)‖≤1 := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  let q : A := 1-star c*c
  have hq : 0≤q := by
    apply sub_nonneg.mpr
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg c)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg c]
  have hqsa : IsSelfAdjoint q := hq.isSelfAdjoint
  have hqcen : Central q := central_sub (fun x => by rw [one_mul,mul_one])
    (central_mul (central_star hc) hc)
  have hcc : star c*c=c*star c := (hc (star c)).symm
  have hcert (b : A) (hb : Central b) (hbn : ‖b‖≤1)
      (hqdef : q=1-star b*b) : 0≤1-star (b+(1/2:ℝ)•q)*(b+(1/2:ℝ)•q) := by
    have hpos : 0≤(1-b)*(1-star b) := by
      simpa only [star_sub,star_one] using mul_star_self_nonneg (1-b)
    have hprod : 0≤q*((1-b)*(1-star b)) := Commute.mul_nonneg hq hpos (hqcen _)
    have hsq : 0≤q*q := hqsa.mul_self_nonneg
    have he : 1-star (b+(1/2:ℝ)•q)*(b+(1/2:ℝ)•q) =
        (1/2:ℝ)•(q*((1-b)*(1-star b)))+(1/4:ℝ)•(q*q) := by
      have hbcomm : Commute (star b) b := (hb (star b)).symm
      rw [hqdef]
      simp only [star_add,star_smul,star_trivial,star_sub,star_one,star_mul,star_star,
        smul_add,smul_sub,smul_mul_assoc,mul_smul_comm,smul_smul]
      noncomm_ring [hbcomm.eq, hbcomm.left_comm] <;> module
    rw [he]
    exact add_nonneg (smul_nonneg (by norm_num) hprod) (smul_nonneg (by norm_num) hsq)
  have hplus := hcert c hc hn rfl
  have hminus := hcert (-c) (fun x => by simpa using congrArg Neg.neg (hc x))
    (by simpa using hn) (by simp only [star_neg,neg_mul_neg]; rfl)
  have hnorm (b : A) (hb : 0≤1-star b*b) : ‖b‖≤1 := by
    have he := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg b)).mpr
      (sub_nonneg.mp hb)
    rw [CStarRing.norm_star_mul_self] at he
    nlinarith [norm_nonneg b]
  refine ⟨hnorm _ hplus, ?_⟩
  have he : -c+(1/2:ℝ)•q = -(c-(1/2:ℝ)•q) := by abel
  simpa only [he,norm_neg] using hnorm _ hminus

/-- T(1) is unitary from the original onto and radius hypotheses. -/
theorem map_one_unitary (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) : T 1 ∈ unitary B := by
  let e : A ≃ₗ[ℂ] B := LinearEquiv.ofBijective T ⟨injective_of_preservesRadius T hr,honto⟩
  have he (a : A) : e a=T a := rfl
  have hsrad : PreservesRadius e.symm.toLinearMap := by
    intro b
    change spectralRadius ℂ (e.symm b)=spectralRadius ℂ b
    have hq : T (e.symm b)=b := (he (e.symm b)).symm.trans (e.apply_symm_apply b)
    exact (hr (e.symm b)).symm.trans (congrArg (spectralRadius ℂ) hq)
  let c : B := T 1
  have hc : Central c := map_one_central T honto hr
  have hnc : ‖c‖≤1 := by
    rw [norm_eq_radius_of_central hc,hr]
    apply (AutomaticContinuity.radiusReal_le_norm (1:A)).trans
    have he := CStarRing.norm_star_mul_self (x := (1:A))
    simp only [star_one,one_mul] at he
    nlinarith [norm_nonneg (1:A)]
  let q : B := 1-star c*c
  have hqcen : Central q := central_sub (fun x => by rw [one_mul,mul_one])
    (central_mul (central_star hc) hc)
  let d : B := (1/2:ℝ)•q
  have hdcen : Central d := central_real_smul hqcen _
  let a : A := e.symm d
  have hacen : Central a := central_image e.symm.toLinearMap e.symm.surjective hsrad d hdcen
  have hnorm (b : A) (hb : Central b) : ‖b‖=‖T b‖ := by
    rw [norm_eq_radius_of_central hb,norm_eq_radius_of_central (central_image T honto hr b hb),hr]
  have hTplus : T (1+a)=c+d := by rw [map_add]; change c+e (e.symm d)=_; rw[e.apply_symm_apply]
  have hTminus : T (1-a)=c-d := by rw [map_sub]; change c-e (e.symm d)=_; rw[e.apply_symm_apply]
  have hcon := central_contraction_perturbations c hc hnc
  have hap : ‖1+a‖≤1 := by
    rw [hnorm _ (central_add (fun x => by rw[one_mul,mul_one]) hacen),hTplus]
    exact hcon.1
  have ham : ‖1-a‖≤1 := by
    rw [hnorm _ (central_sub (fun x => by rw[one_mul,mul_one]) hacen),hTminus]
    exact hcon.2
  have ha0 : a=0 := eq_zero_of_one_add_sub_contractions a hap ham
  have hd0 : d=0 := by
    have ht := congrArg e ha0
    simpa only [a,e.apply_symm_apply,map_zero] using ht
  have hq0 : q=0 := by
    apply (smul_eq_zero.mp hd0).resolve_left
    norm_num
  have hleft : star c*c=1 := sub_eq_zero.mp hq0 |>.symm
  have hright : c*star c=1 := (hc (star c)).trans hleft
  exact ⟨hleft,hright⟩

/- Untested final preparation; no Jordan conclusion is claimed here.
Promote only after the central/unitary inputs actually pass. -/

theorem radius_mul_central_unitary (u b : A) (hu : Central u) (hU : u ∈ unitary A) :
    spectralRadius ℂ (u*b)=spectralRadius ℂ b := by
  have hp (n : ℕ) : ‖(u*b)^n‖₊=‖b^n‖₊ := by
    apply Subtype.ext
    change ‖(u*b)^n‖=‖b^n‖
    rw [Commute.mul_pow (hu b : Commute u b)]
    exact CStarRing.norm_mem_unitary_mul _ ((unitary A).pow_mem hU n)
  apply tendsto_nhds_unique
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (u*b))
  simpa only [hp] using spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius b

/-- Normalization preparation from the original hypotheses. The Jordan
conclusion still requires the separately proved main theorem. -/
theorem exists_unital_radius_normalization (T : A →ₗ[ℂ] B)
    (honto : Function.Surjective T) (hr : PreservesRadius T) :
    ∃ (u : B) (J : A →ₗ[ℂ] B), Central u ∧ u ∈ unitary B ∧ J 1=1 ∧
      Function.Surjective J ∧ PreservesRadius J ∧ ∀ a, T a=u*J a := by
  let c : B := T 1
  have hc : Central c := map_one_central T honto hr
  have hU : c ∈ unitary B := map_one_unitary T honto hr
  have hstar : star c ∈ unitary B := by
    exact ⟨by simpa only [star_star] using hU.2,by simpa only [star_star] using hU.1⟩
  let J : A →ₗ[ℂ] B :=
    { toFun := fun a => star c*T a
      map_add' := fun a b => by rw [map_add,mul_add]
      map_smul' := fun r a => by simp only [map_smul,mul_smul_comm,RingHom.id_apply] }
  have hJ1 : J 1=1 := hU.1
  have hJon : Function.Surjective J := by
    intro b
    obtain ⟨a,ha⟩ := honto (c*b)
    refine ⟨a,?_⟩
    change star c*T a=b
    rw [ha,←mul_assoc,hU.1,one_mul]
  have hJr : PreservesRadius J := by
    intro a
    change spectralRadius ℂ (star c*T a)=spectralRadius ℂ a
    rw [radius_mul_central_unitary _ _ (central_star hc) hstar,hr]
  have hfac (a : A) : T a=c*J a := by
    change T a=c*(star c*T a)
    rw [←mul_assoc,hU.2,one_mul]
  exact ⟨c,J,hc,hU,hJ1,hJon,hJr,hfac⟩

theorem map_one_central_unitary (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) : Central (T 1) ∧ T 1 ∈ unitary B :=
  ⟨map_one_central T honto hr, map_one_unitary T honto hr⟩

end SpectralIsometry.Normalization
