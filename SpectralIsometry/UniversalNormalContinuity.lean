module

public import SpectralIsometry.UniversalApproximation
public import SpectralIsometry.HilbertDomination
public import SpectralIsometry.WeakHilbertBounds
public import SpectralIsometry.GenericNormalProjectionContinuity
import Mathlib.Tactic.NormNum

/-!
# Universal Normal Continuity

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexOrder

namespace SpectralIsometry.BidualFoundation.UniversalNormalContinuity

open UniversalWeakClosure CoefficientPredual StrongStarApproximation

universe u v
variable (A : Type u) [CStarAlgebra A]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] UniversalWeakClosure.orderedA UniversalWeakClosure.starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] UniversalWeakClosure.predualNormedGroup UniversalWeakClosure.predualNormedSpace

-- These only guide elaboration across the universal-GNS subtype dictionaries;
-- every resulting term is still checked by Lean's kernel.
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

abbrev Target := K →L[ℂ] K

/-- Normality for scalar vector coefficients in the actual coefficient predual. -/
def HasNormalCoefficients (V : algebra A →L[ℂ] Target (K:=K)) : Prop :=
  ∀ ξ η : K, ∃ Φ : predual A, ∀ x : algebra A,
    (Φ : StrongDual ℂ (algebra A)) x=⟪η,V x ξ⟫_ℂ

private def starSandwichLinear (T : A →L[ℂ] Target (K:=K)) : A →ₗ[ℂ] Target (K:=K) where
  toFun a := star (T (star a))
  map_add' a b := by simp only [star_add,map_add]
  map_smul' z a := by simp only [star_smul,map_smul,star_star,RingHom.id_apply]

private def starSandwich (T : A →L[ℂ] Target (K:=K)) : A →L[ℂ] Target (K:=K) :=
  (starSandwichLinear A T).mkContinuous ‖T‖ (by
    intro a
    simpa only [starSandwichLinear,LinearMap.coe_mk,AddHom.coe_mk,norm_star] using
      T.le_opNorm (star a))

private theorem positive_square_coefficient (φ : A →ₚ[ℂ] ℂ) (a : A) :
    (φ (star a*a)).re=
      ‖(inclusion A a : Hilbert A →L[ℂ] Hilbert A) (cyclicVector A φ)‖^2 := by
  have hh := NormalProjectionContinuity.diagonalPositive_star_mul_self
    (OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation (M:=A))
    (cyclicVector A φ) a
  change (⟪cyclicVector A φ,
    OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation (star a*a)
      (cyclicVector A φ)⟫_ℂ).re = _ at hh
  rw [cyclicVector_coefficient] at hh
  exact hh

private theorem positive_flipped_square_coefficient (φ : A →ₚ[ℂ] ℂ) (a : A) :
    (φ (a*star a)).re=
      ‖star (inclusion A a : Hilbert A →L[ℂ] Hilbert A) (cyclicVector A φ)‖^2 := by
  have hh := NormalProjectionContinuity.diagonalPositive_mul_star_self
    (OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation (M:=A))
    (cyclicVector A φ) a
  change (⟪cyclicVector A φ,
    OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation (a*star a)
      (cyclicVector A φ)⟫_ℂ).re = _ at hh
  rw [cyclicVector_coefficient,map_star] at hh
  exact hh

private theorem original_vector_domination (V : algebra A →L[ℂ] Target (K:=K)) (ξ : K) :
    ∃ w₁ w₂ : Hilbert A, ∀ a : A,
      ‖V (inclusion A a) ξ‖^2≤
        ‖(inclusion A a : Hilbert A →L[ℂ] Hilbert A) w₁‖^2+
        ‖star (inclusion A a : Hilbert A →L[ℂ] Hilbert A) w₂‖^2 := by
  let S : A →L[ℂ] K := ((ContinuousLinearMap.apply ℂ K) ξ).comp (V.comp (inclusionCLM A))
  obtain ⟨φ,ψ,h⟩ := HilbertDomination.exists_positive_domination S
  refine ⟨cyclicVector A φ,cyclicVector A ψ,fun a => ?_⟩
  have hh := h a
  rw [positive_square_coefficient A φ a,positive_flipped_square_coefficient A ψ a] at hh
  exact hh

private theorem original_adjoint_vector_domination (V : algebra A →L[ℂ] Target (K:=K)) (ξ : K) :
    ∃ w₁ w₂ : Hilbert A, ∀ a : A,
      ‖star (V (inclusion A a)) ξ‖^2≤
        ‖(inclusion A a : Hilbert A →L[ℂ] Hilbert A) w₁‖^2+
        ‖star (inclusion A a : Hilbert A →L[ℂ] Hilbert A) w₂‖^2 := by
  let T : A →L[ℂ] Target (K:=K) := V.comp (inclusionCLM A)
  let S : A →L[ℂ] K := ((ContinuousLinearMap.apply ℂ K) ξ).comp (starSandwich A T)
  obtain ⟨φ,ψ,h⟩ := HilbertDomination.exists_positive_domination S
  refine ⟨cyclicVector A ψ,cyclicVector A φ,fun a => ?_⟩
  have hh := h (star a)
  have hleft : S (star a)=star (V (inclusion A a)) ξ := by
    change star (T (star (star a))) ξ=star (V (inclusion A a)) ξ
    rw [star_star]
    rfl
  rw [hleft,star_star,positive_square_coefficient A ψ a] at hh
  have hr := positive_flipped_square_coefficient A φ a
  rw [hr,add_comm] at hh
  exact hh

private theorem weak_vector_limit (V : algebra A →L[ℂ] Target (K:=K))
    (hV : HasNormalCoefficients A V) (x : algebra A)
    (a : UniversalApproximation.Index A → A) (haN : ∀ i, ‖a i‖≤‖x‖)
    (haT : StrongStarTendsto
      (fun i => (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A)) atTop
      (x : Hilbert A →L[ℂ] Hilbert A)) (ξ η : K) :
    Tendsto (fun i => ⟪η,V (inclusion A (a i)) ξ⟫_ℂ) atTop (𝓝 ⟪η,V x ξ⟫_ℂ) := by
  obtain ⟨Φ,hΦ⟩ := hV ξ η
  have hh := coefficientPredual_tendsto_of_strong (algebra A) ‖x‖
    (a:=fun i => inclusion A (a i)) (T:=x)
    (fun i => by simpa only [inclusion_norm] using haN i) le_rfl haT.1 Φ
  simpa only [hΦ] using hh

private theorem inner_adjoint_star (Y : Target (K:=K)) (ξ η : K) :
    ⟪η,star Y ξ⟫_ℂ=star ⟪ξ,Y η⟫_ℂ := by
  change ⟪η,Y.adjoint ξ⟫_ℂ=star ⟪ξ,Y η⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [Complex.star_def,inner_conj_symm]

/-- In the universal represented algebra every normal operator has explicit
two-vector norm bounds. Original-algebra density is discharged internally. -/
theorem exists_vector_bounds (V : algebra A →L[ℂ] Target (K:=K))
    (hV : HasNormalCoefficients A V) (ξ : K) :
    ∃ w₁ w₂ w₃ w₄ : Hilbert A, ∀ x : algebra A,
      (‖V x ξ‖^2≤‖(x : Hilbert A →L[ℂ] Hilbert A) w₁‖^2+
        ‖star (x : Hilbert A →L[ℂ] Hilbert A) w₂‖^2) ∧
      (‖star (V x) ξ‖^2≤‖(x : Hilbert A →L[ℂ] Hilbert A) w₃‖^2+
        ‖star (x : Hilbert A →L[ℂ] Hilbert A) w₄‖^2) := by
  obtain ⟨w₁,w₂,h₁⟩ := original_vector_domination A V ξ
  obtain ⟨w₃,w₄,h₂⟩ := original_adjoint_vector_domination A V ξ
  refine ⟨w₁,w₂,w₃,w₄,fun x => ?_⟩
  obtain ⟨a,haN,haT⟩ := UniversalApproximation.exists_bounded_net A x
  letI : (atTop : Filter (UniversalApproximation.Index A)).NeBot := UniversalApproximation.index_neBot A
  have hweak (η : K) := weak_vector_limit A V hV x a haN haT ξ η
  have hadj (η : K) : Tendsto (fun i => ⟪η,star (V (inclusion A (a i))) ξ⟫_ℂ)
      atTop (𝓝 ⟪η,star (V x) ξ⟫_ℂ) := by
    have hh := (weak_vector_limit A V hV x a haN haT η ξ).star
    simpa only [←inner_adjoint_star] using hh
  have hr₁ := ((haT.1 w₁).norm.pow 2).add ((haT.2 w₂).norm.pow 2)
  have hr₂ := ((haT.1 w₃).norm.pow 2).add ((haT.2 w₄).norm.pow 2)
  constructor
  · exact WeakHilbertBounds.norm_sq_le_of_weak_limit _ _ _ _ hweak hr₁
      (Eventually.of_forall fun i => h₁ (a i))
  · exact WeakHilbertBounds.norm_sq_le_of_weak_limit _ _ _ _ hadj hr₂
      (Eventually.of_forall fun i => h₂ (a i))

/-- Actual strong-star continuity on the universal model. The original
manuscript's bounded-net application is a consequence; no continuity of the
canonical bidual operator is assumed in this theorem. -/
theorem strongStarTendsto_map {ι : Type*} {l : Filter ι}
    (V : algebra A →L[ℂ] Target (K:=K)) (hV : HasNormalCoefficients A V)
    (a : ι → algebra A) (x : algebra A)
    (ha : StrongStarTendsto (fun i => (a i : Hilbert A →L[ℂ] Hilbert A)) l
      (x : Hilbert A →L[ℂ] Hilbert A)) :
    StrongStarTendsto (fun i => V (a i)) l (V x) := by
  have hd : StrongStarTendsto
      (fun i => ((a i-x : algebra A) : Hilbert A →L[ℂ] Hilbert A)) l 0 := by
    constructor
    · intro η
      change Tendsto (fun i => ((a i : Hilbert A →L[ℂ] Hilbert A)-
        (x : Hilbert A →L[ℂ] Hilbert A)) η) l (𝓝 (0 : Hilbert A))
      simpa only [ContinuousLinearMap.sub_apply,sub_self,
        ContinuousLinearMap.zero_apply] using (ha.1 η).sub_const ((x : Hilbert A →L[ℂ] Hilbert A) η)
    · intro η
      change Tendsto (fun i => star ((a i : Hilbert A →L[ℂ] Hilbert A)-
        (x : Hilbert A →L[ℂ] Hilbert A)) η) l (𝓝 (star (0 : Hilbert A →L[ℂ] Hilbert A) η))
      rw [show star (0 : Hilbert A →L[ℂ] Hilbert A)=(0 : Hilbert A →L[ℂ] Hilbert A) from
        star_zero (Hilbert A →L[ℂ] Hilbert A)]
      simpa only [star_sub,ContinuousLinearMap.sub_apply,sub_self,star_zero,
        ContinuousLinearMap.zero_apply] using (ha.2 η).sub_const
          (star (x : Hilbert A →L[ℂ] Hilbert A) η)
  constructor
  · intro ξ
    obtain ⟨w₁,w₂,w₃,w₄,hb⟩ := exists_vector_bounds A V hV ξ
    have hr := ((hd.1 w₁).norm.pow 2).add ((hd.2 w₂).norm.pow 2)
    have ht := WeakHilbertBounds.tendsto_zero_of_norm_sq_bound
      (fun i => V (a i-x) ξ) _ (by simpa using hr)
      (Eventually.of_forall fun i => (hb (a i-x)).1)
    simpa only [map_sub,ContinuousLinearMap.sub_apply,sub_add_cancel,zero_add] using
      ht.add_const (V x ξ)
  · intro ξ
    obtain ⟨w₁,w₂,w₃,w₄,hb⟩ := exists_vector_bounds A V hV ξ
    have hr := ((hd.1 w₃).norm.pow 2).add ((hd.2 w₄).norm.pow 2)
    have ht := WeakHilbertBounds.tendsto_zero_of_norm_sq_bound
      (fun i => star (V (a i-x)) ξ) _ (by simpa using hr)
      (Eventually.of_forall fun i => (hb (a i-x)).2)
    simpa only [map_sub,star_sub,ContinuousLinearMap.sub_apply,sub_add_cancel,zero_add] using
      ht.add_const (star (V x) ξ)

end SpectralIsometry.BidualFoundation.UniversalNormalContinuity

