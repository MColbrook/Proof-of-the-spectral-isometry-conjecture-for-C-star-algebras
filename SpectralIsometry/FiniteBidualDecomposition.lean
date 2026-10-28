module

public import SpectralIsometry.BidualFoundation
public import OAI.Analysis.BoundedHochschild.ProperlyInfiniteIsometries
public import OAI.Analysis.BoundedHochschild.FiniteTracialDecomposition
import Mathlib.Tactic.NoncommRing

/-!
# Finite Bidual Decomposition

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.FiniteBidualDecomposition

open OAI.HochschildCorners OAI.HochschildNormalPart
open OAI.BoundedHochschild OAI.BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

local instance orderedM : PartialOrder M := CStarAlgebra.spectralOrder M
local instance starOrderedM : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
local instance (priority := 2000) complexOrder : PartialOrder ℂ := Complex.partialOrder
local instance (priority := 2000) complexStarOrder : StarOrderedRing ℂ := RCLike.toStarOrderedRing

def IsNormalTracialState (τ : M →ₚ[ℂ] ℂ) : Prop :=
  TraceInPredual e τ ∧ τ 1=1 ∧ ∀ a b : M, τ (a*b)=τ (b*a)

/-- The finite central cut has an actually properly infinite complement,
including the zero-corner cases. No trace or decomposition is an input. -/
theorem exists_finite_properlyInfinite_cut (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ (q : M) (hq : IsStarProjection q), (∀ a : M, q*a=a*q) ∧
      FiniteAlgebra (Corner q hq) ∧ ProperlyInfiniteProjection (1-q) := by
  obtain ⟨q,hq,hqc,hfinite,hno⟩ := exists_finite_central_cut_noFiniteSummand e
  let eP := cornerPredualEquiv (1-q) hq.one_sub e
  have hproper := properlyInfinite_one eP hno
  have hambient := properlyInfinite_from_corner hq.one_sub hproper
  exact ⟨q,hq,hqc,hfinite,by simpa only [corner_coe_one] using hambient⟩

/-- Literal source notation: p is properly infinite, q finite, p+q=1. -/
theorem exists_central_split (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q),
      (∀ a : M, p*a=a*p) ∧ (∀ a : M, q*a=a*q) ∧ p+q=1 ∧ p*q=0 ∧
      ProperlyInfiniteProjection p ∧ FiniteAlgebra (Corner q hq) := by
  obtain ⟨q,hq,hqc,hfinite,hproper⟩ := exists_finite_properlyInfinite_cut e
  refine ⟨1-q,q,hq.one_sub,hq,?_,hqc,by abel,?_,hproper,hfinite⟩
  · intro a
    simp only [sub_mul,mul_sub,one_mul,mul_one,hqc]
  · exact hq.one_sub_mul_self

/-- A central piece carrying a center-faithful normal state has a global normal
tracial state which is faithful on that piece. The global finite hypothesis is
the actual finite-algebra property, not a trace-existence assumption. -/
theorem exists_normal_tracial_state_faithful_on_piece (hfinite : FiniteAlgebra M)
    (p : M) (hp : IsStarProjection p) (hpc : ∀ a : M, p*a=a*p)
    (hstate : HasCentralFaithfulNormalState e p) :
    ∃ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ ∧
      ∀ x : M, τ (star x*x)=0 → p*x=0 := by
  obtain ⟨ψ,hψ,hψ1,hψp,hfaith⟩ := hstate
  obtain ⟨τ,hτ,hτ1,htr,hcenter⟩ := exists_normal_tracial_average e hfinite ψ hψ
  have hτp : τ p=1 := (hcenter p hpc).trans hψp
  let ρ := cornerTrace p hp τ
  have hρeval (a : Corner p hp) : ρ a=τ (a:M) := by
    simp only [ρ,cornerTrace_apply,hτp,Complex.one_re,Complex.ofReal_one,inv_one,one_mul]
  have hρnormal : TraceInPredual (cornerPredualEquiv p hp e) ρ :=
    cornerTrace_normal p hp e τ hτ
  have hρtr : ∀ a b : Corner p hp, ρ (a*b)=ρ (b*a) :=
    cornerTrace_tracial p hp τ htr
  have hρcenter : ∀ r : Corner p hp, IsStarProjection r →
      (∀ a : Corner p hp, r*a=a*r) → ρ r=0 → r=0 := by
    intro r hr hrc hzero
    apply Subtype.ext
    apply hfaith (r:M) (corner_projection_coe p hp hr)
      (centralCorner_central hp hpc r hrc) (corner_projection_le p hp hr)
    rw [hρeval] at hzero
    exact (hcenter (r:M) (centralCorner_central hp hpc r hrc)).symm.trans hzero
  have hρfaith := normal_trace_faithful_of_center (cornerPredualEquiv p hp e)
    ρ hρnormal hρtr hρcenter
  refine ⟨τ,⟨hτ,hτ1.trans hψ1,htr⟩,?_⟩
  intro x hx
  let c : Corner p hp := CentralCorner.compressMap p hp hpc x
  have hsq : star (c:M)*(c:M) ≤ star x*x := by
    change star (p*x)*(p*x) ≤ star x*x
    have heq : star (p*x)*(p*x)=star x*p*x := by
      calc
        _ = star x*(p*p)*x := by rw [star_mul,hp.isSelfAdjoint.star_eq]; noncomm_ring
        _ = _ := by rw [hp.isIdempotentElem.eq]
    rw [heq]
    simpa only [mul_one] using star_left_conjugate_le_conjugate hp.le_one x
  have hτc : τ (star (c:M)*(c:M))=0 :=
    le_antisymm ((τ.monotone hsq).trans_eq hx)
      (τ.map_nonneg (star_mul_self_nonneg (c:M)))
  have hc0 : c=0 := hρfaith c (by rw [hρeval]; exact hτc)
  exact congrArg (fun a : Corner p hp => (a:M)) hc0

/-- Normal tracial states of an arbitrary finite Wstar model separate
star-squares. The separating family is constructed by maximal central pieces;
a single global faithful normal state is not assumed or asserted. -/
theorem eq_zero_of_all_normal_tracial_states (hfinite : FiniteAlgebra M) (x : M)
    (h : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ → τ (star x*x)=0) : x=0 := by
  classical
  obtain ⟨D⟩ := exists_maximal_central_partition e (HasCentralFaithfulNormalState e)
  have hD0 : D.complement=0 := by
    by_contra hn
    obtain ⟨p,hp,hpc,hple,hp0,hstate⟩ := exists_central_normal_state_subprojection e
      D.complement_isProjection D.complement_central hn
    exact hp0 (D.maximal p hp hpc hple hstate)
  apply D.total x
  · rw [hD0,zero_mul]
  · intro i
    obtain ⟨τ,hτ,hfaith⟩ := exists_normal_tracial_state_faithful_on_piece e hfinite
      (D.projection i) (D.isProjection i) (D.central i) (D.property i)
    exact hfaith x (h τ hτ)

/-- Literal source separation of positive elements, derived from the proved
star-square separation and the existing C*-positive-square theorem. -/
theorem positive_eq_zero_of_all_normal_tracial_states (hfinite : FiniteAlgebra M)
    (a : M) (ha : 0≤a)
    (h : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ → τ a=0) : a=0 := by
  obtain ⟨b,hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  have hb0 : b=0 := eq_zero_of_all_normal_tracial_states e hfinite b (by
    intro τ hτ
    rw [←hb]
    exact h τ hτ)
  rw [hb,hb0,star_zero,zero_mul]

end SpectralIsometry.FiniteBidualDecomposition

