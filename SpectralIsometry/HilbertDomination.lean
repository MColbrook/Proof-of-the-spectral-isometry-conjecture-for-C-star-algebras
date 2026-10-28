module

public import OAI.Analysis.Commutator.LittleGrothendieckSequence
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

/-!
# Hilbert Domination

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open scoped ComplexOrder
open scoped InnerProductSpace
open scoped BoundedContinuousFunction

namespace SpectralIsometry.HilbertDomination

variable {A : Type*} [CStarAlgebra A]

private def constantLinear : A →ₗ[ℂ] (ℕ →ᵇ A) where
  toFun := BoundedContinuousFunction.const ℕ
  map_add' a b := by ext n; rfl
  map_smul' z a := by ext n; rfl

private def constantEmbedding : A →L[ℂ] (ℕ →ᵇ A) :=
  (constantLinear (A:=A)).mkContinuous 1 (by
    intro a
    simpa only [constantLinear,LinearMap.coe_mk,AddHom.coe_mk,
      BoundedContinuousFunction.norm_const_eq,one_mul] using (le_rfl : ‖a‖≤‖a‖))

@[simp] private theorem constantEmbedding_apply (a : A) :
    constantEmbedding a=BoundedContinuousFunction.const ℕ a := rfl

@[simp] private theorem constantEmbedding_mul (a b : A) :
    constantEmbedding (a*b)=constantEmbedding a*constantEmbedding b := by ext n; rfl

@[simp] private theorem constantEmbedding_star (a : A) :
    constantEmbedding (star a)=star (constantEmbedding a) := by ext n; rfl

private def starFunctionalLinear (φ : A →L[ℂ] ℂ) : A →ₗ[ℂ] ℂ where
  toFun a := star (φ (star a))
  map_add' a b := by simp only [star_add,map_add]
  map_smul' z a := by simp only [star_smul,map_smul,star_star,RingHom.id_apply]

private def starFunctional (φ : A →L[ℂ] ℂ) : A →L[ℂ] ℂ :=
  (starFunctionalLinear φ).mkContinuous ‖φ‖ (by
    intro a
    simpa only [starFunctionalLinear,LinearMap.coe_mk,AddHom.coe_mk,norm_star] using
      φ.le_opNorm (star a))

private def hermitianPart (φ : A →L[ℂ] ℂ) : A →L[ℂ] ℂ :=
  (1/2:ℂ) • (φ+starFunctional φ)

private theorem hermitianPart_apply_selfadjoint (φ : A →L[ℂ] ℂ)
    {a : A} (ha : IsSelfAdjoint a) : hermitianPart φ a=((φ a).re:ℂ) := by
  change (1/2:ℂ)*(φ a+star (φ (star a)))=((φ a).re:ℂ)
  rw [ha.star_eq]
  apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im] <;> ring

section Ordered

local instance (priority := 2000) : PartialOrder ℂ := Complex.partialOrder
local instance (priority := 2000) : StarOrderedRing ℂ := RCLike.toStarOrderedRing
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private def leftFunctional (V : A →L[ℂ] E) (u : unitary A) : A →L[ℂ] ℂ :=
  ((innerSL ℂ (V (u:A))).comp V).comp ((ContinuousLinearMap.mul ℂ A) (u:A))

private def rightFunctional (V : A →L[ℂ] E) (u : unitary A) : A →L[ℂ] ℂ :=
  ((innerSL ℂ (V (u:A))).comp V).comp ((ContinuousLinearMap.mul ℂ A).flip (u:A))

private theorem leftFunctional_re_nonneg (V : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖V (v:A)‖≤‖V (u:A)‖)
    (p : A) (hp : 0≤p) : 0≤(leftFunctional V u p).re := by
  have hs : IsSelfAdjoint (CFC.sqrt p) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)
  have hh := OAI.Kadison.LittleGrothendieck.selfAdjoint_square_at_unitary_max
    V u hu (CFC.sqrt p) hs
  rw [CFC.sqrt_mul_sqrt_self p hp] at hh
  exact (sq_nonneg _).trans hh

private theorem rightFunctional_re_nonneg (V : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖V (v:A)‖≤‖V (u:A)‖)
    (p : A) (hp : 0≤p) : 0≤(rightFunctional V u p).re := by
  let W : A →L[ℂ] E := V.comp ((ContinuousLinearMap.mul ℂ A).flip (u:A))
  have hw (v : unitary A) : ‖W (v:A)‖≤‖W (1:A)‖ := by
    change ‖V ((v:A)*(u:A))‖≤‖V (1*(u:A))‖
    simpa only [one_mul,Submonoid.coe_mul] using hu (v*u)
  have hh := leftFunctional_re_nonneg W 1 hw p hp
  change 0≤(⟪V ((1:A)*(u:A)),V (((1:A)*p)*(u:A))⟫_ℂ).re at hh
  change 0≤(⟪V (u:A),V (p*(u:A))⟫_ℂ).re
  simpa only [one_mul] using hh

private theorem hermitianPart_nonneg (φ : A →L[ℂ] ℂ)
    (hφ : ∀ p : A, 0≤p → 0≤(φ p).re) (p : A) (hp : 0≤p) :
    0≤hermitianPart φ p := by
  rw [hermitianPart_apply_selfadjoint φ (IsSelfAdjoint.of_nonneg hp)]
  exact Complex.nonneg_iff.mpr ⟨hφ p hp,rfl⟩

private def positiveOfCLM (φ : A →L[ℂ] ℂ)
    (hφ : ∀ p : A, 0≤p → 0≤φ p) : A →ₚ[ℂ] ℂ where
  toLinearMap := φ.toLinearMap
  monotone' := by
    intro a b hab
    have hh := hφ (b-a) (sub_nonneg.mpr hab)
    rw [map_sub] at hh
    exact sub_nonneg.mp hh

/-- At a unitary norm maximum the second-derivative construction gives two
positive functionals dominating the Hilbert norm. No positivity is assumed. -/
theorem positive_domination_at_unitary_max (V : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖V (v:A)‖≤‖V (u:A)‖) :
    ∃ φ ψ : A →ₚ[ℂ] ℂ, ∀ a : A,
      ‖V a‖^2≤(φ (star a*a)).re+(ψ (a*star a)).re := by
  let f := leftFunctional V u
  let g := rightFunctional V u
  let φ := positiveOfCLM (hermitianPart f)
    (hermitianPart_nonneg f (leftFunctional_re_nonneg V u hu))
  let ψ := positiveOfCLM (hermitianPart g)
    (hermitianPart_nonneg g (rightFunctional_re_nonneg V u hu))
  refine ⟨φ,ψ,fun a => ?_⟩
  have hstar : IsSelfAdjoint (star a*a) := IsSelfAdjoint.star_mul_self a
  have hself : IsSelfAdjoint (a*star a) := IsSelfAdjoint.mul_star_self a
  change ‖V a‖^2≤(hermitianPart f (star a*a)).re+(hermitianPart g (a*star a)).re
  rw [hermitianPart_apply_selfadjoint f hstar,hermitianPart_apply_selfadjoint g hself]
  simp only [Complex.ofReal_re]
  let b : A := (star u:A)*a
  have hub : (u:A)*b=a := by
    dsimp only [b]
    rw [←mul_assoc,Unitary.mul_star_self_of_mem u.property,one_mul]
  have hid : (u:A)*(star b*b+b*star b)=
      (u:A)*(star a*a)+(a*star a)*(u:A) := by
    dsimp only [b]
    calc
      (u:A)*(star ((star u:A)*a)*((star u:A)*a)+
          ((star u:A)*a)*star ((star u:A)*a)) =
          ((u:A)*star a)*((u:A)*star (u:A))*a+
          ((u:A)*star (u:A))*(a*star a)*(u:A) := by
        simp only [star_mul,star_star]
        noncomm_ring
      _ = (u:A)*(star a*a)+(a*star a)*(u:A) := by
        rw [Unitary.mul_star_self_of_mem u.property]
        simp only [mul_one,one_mul,mul_assoc]
  have hh := OAI.Kadison.LittleGrothendieck.square_at_unitary_max V u hu b
  rw [hub,hid,map_add,inner_add_right,Complex.add_re] at hh
  exact hh

/-- Every bounded map from an arbitrary complex Cstar algebra to an inner
product space has positive-functional square domination. Completeness and
separability of the Hilbert target, and nonzero algebras, are not hypotheses. -/
theorem exists_positive_domination (T : A →L[ℂ] E) :
    ∃ φ ψ : A →ₚ[ℂ] ℂ, ∀ a : A,
      ‖T a‖^2≤(φ (star a*a)).re+(ψ (a*star a)).re := by
  obtain ⟨ω,u,hu⟩ := OAI.Kadison.LittleGrothendieck.exists_sequence_unitary_max T
  let V := OAI.Kadison.LittleGrothendieck.sequenceMap ω T
  letI : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder (ℕ →ᵇ A)
  letI : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing (ℕ →ᵇ A)
  obtain ⟨f,g,hfg⟩ := positive_domination_at_unitary_max V u hu
  have hC (p : A) (hp : 0≤p) : 0≤constantEmbedding p := by
    have he : constantEmbedding p=star (constantEmbedding (CFC.sqrt p))*
        constantEmbedding (CFC.sqrt p) := by
      rw [←constantEmbedding_star,←constantEmbedding_mul,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq,
        CFC.sqrt_mul_sqrt_self p hp]
    rw [he]
    exact star_mul_self_nonneg _
  let φ : A →ₚ[ℂ] ℂ := {
    toLinearMap := f.toLinearMap.comp (constantEmbedding (A:=A)).toLinearMap
    monotone' := by
      intro a b hab
      apply f.monotone'
      have hh := hC (b-a) (sub_nonneg.mpr hab)
      rw [map_sub] at hh
      exact sub_nonneg.mp hh }
  let ψ : A →ₚ[ℂ] ℂ := {
    toLinearMap := g.toLinearMap.comp (constantEmbedding (A:=A)).toLinearMap
    monotone' := by
      intro a b hab
      apply g.monotone'
      have hh := hC (b-a) (sub_nonneg.mpr hab)
      rw [map_sub] at hh
      exact sub_nonneg.mp hh }
  refine ⟨φ,ψ,fun a => ?_⟩
  have hh := hfg (constantEmbedding a)
  rw [show V (constantEmbedding a)=OAI.Kadison.HilbertSequence.constant ω E (T a) from
    OAI.Kadison.LittleGrothendieck.sequenceMap_const ω T a,
    LinearIsometry.norm_map] at hh
  change ‖T a‖^2≤(f (constantEmbedding (star a*a))).re+
    (g (constantEmbedding (a*star a))).re
  simpa only [constantEmbedding_mul,constantEmbedding_star] using hh

end Ordered

end SpectralIsometry.HilbertDomination

