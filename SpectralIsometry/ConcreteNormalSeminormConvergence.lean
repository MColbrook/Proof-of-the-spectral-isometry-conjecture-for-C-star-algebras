module
public import SpectralIsometry.NormalSeminormTopology
public import SpectralIsometry.BidualConcretePredual
public import SpectralIsometry.StrongStarApproximation

/-!
# Concrete Normal Seminorm Convergence

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexOrder

namespace SpectralIsometry.ConcreteNormalSeminorm
open BidualFoundation.CoefficientPredual StrongStarApproximation
open NormalProjectionContinuity OAI.HochschildNormalPart
attribute [local instance] complexNormedSpaceSelf coefficientNormedGroup coefficientNormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : VonNeumannAlgebra H)
local instance concreteOrder : PartialOrder M := CStarAlgebra.spectralOrder M
local instance concreteStarOrder : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
local instance (priority := 2000) concreteComplexOrder : PartialOrder ℂ := Complex.partialOrder
local instance (priority := 2000) concreteComplexStarOrder : StarOrderedRing ℂ := RCLike.toStarOrderedRing
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private theorem coe_sub' (x y : M) : ((x-y:M):H →L[ℂ] H)=(x:H →L[ℂ] H)-(y:H →L[ℂ] H) :=
  map_sub M.toStarSubalgebra.subtype x y
private theorem coe_mul' (x y : M) : ((x*y:M):H →L[ℂ] H)=(x:H →L[ℂ] H)*(y:H →L[ℂ] H) :=
  map_mul M.toStarSubalgebra.subtype x y
private theorem coe_star' (x : M) : ((star x:M):H →L[ℂ] H)=star (x:H →L[ℂ] H) :=
  map_star M.toStarSubalgebra.subtype x
private theorem coe_zero' : ((0:M):H →L[ℂ] H)=0 := map_zero M.toStarSubalgebra.subtype

theorem bounded_strongStar_to_normalPositive {I : Type*} {l : Filter I}
    (a : I → M) (b : M) (C : ℝ) (hbound : ∀ i, ‖a i‖≤C)
    (ha : StrongStarTendsto (fun i => (a i:H →L[ℂ] H)) l (b:H →L[ℂ] H)) :
    NormalPositiveStrongStarTendsto (concretePredualIsometry M) a l b := by
  let D : ℝ := max C 0+‖b‖
  let d : I → M := fun i => a i-b
  have hD : 0≤D := add_nonneg (le_max_right _ _) (norm_nonneg b)
  have hd (i : I) : ‖d i‖≤D :=
    (norm_sub_le (a i) b).trans (add_le_add ((hbound i).trans (le_max_left C 0)) le_rfl)
  have hdT : StrongStarTendsto (fun i => (d i:H →L[ℂ] H)) l 0 := by
    constructor
    · intro ξ
      have hh := (ha.1 ξ).sub (tendsto_const_nhds (x:=(b:H →L[ℂ] H) ξ) (f:=l))
      simpa only [d,coe_sub',sub_apply,sub_self,zero_apply] using hh
    · intro ξ
      have hh := (ha.2 ξ).sub (tendsto_const_nhds (x:=star (b:H →L[ℂ] H) ξ) (f:=l))
      simpa only [d,coe_sub',star_sub,sub_apply,sub_self,star_zero,zero_apply] using hh
  have hdOp : ∀ᶠ i in l, ‖(d i:H →L[ℂ] H)‖≤D := Eventually.of_forall hd
  have hdStar : ∀ᶠ i in l, ‖star (d i:H →L[ℂ] H)‖≤D := by
    simpa only [norm_star] using hdOp
  have hp := strongStarTendsto_mul_of_norm_bounds (strongStarTendsto_star hdT) hdT hdStar hdOp
  have hq := strongStarTendsto_mul_of_norm_bounds hdT (strongStarTendsto_star hdT) hdOp hdStar
  have hpBound (i : I) : ‖star (d i)*d i‖≤D^2 := by
    calc
      _ ≤ ‖star (d i)‖*‖d i‖ := norm_mul_le _ _
      _ = ‖d i‖*‖d i‖ := by rw [norm_star]
      _ ≤ D*D := mul_le_mul (hd i) (hd i) (norm_nonneg _) hD
      _ = D^2 := (pow_two D).symm
  have hqBound (i : I) : ‖d i*star (d i)‖≤D^2 := by
    calc
      _ ≤ ‖d i‖*‖star (d i)‖ := norm_mul_le _ _
      _ = ‖d i‖*‖d i‖ := by rw [norm_star]
      _ ≤ D*D := mul_le_mul (hd i) (hd i) (norm_nonneg _) hD
      _ = D^2 := (pow_two D).symm
  intro ψ φ heq hn
  have hmem : φ∈coefficientPredual M := by
    rw [←normalDual_eq_coefficientPredual M]
    exact hn
  let Φ : coefficientPredual M := ⟨φ,hmem⟩
  have hsP := coefficientPredual_tendsto_of_strong M (D^2) hpBound
    (a:=fun i => star (d i)*d i) (T:=0)
    (by simpa only [norm_zero] using sq_nonneg D)
    (by intro ξ; simpa only [coe_mul',coe_star',coe_zero',star_zero,zero_mul,zero_apply] using hp.1 ξ) Φ
  have hsQ := coefficientPredual_tendsto_of_strong M (D^2) hqBound
    (a:=fun i => d i*star (d i)) (T:=0)
    (by simpa only [norm_zero] using sq_nonneg D)
    (by intro ξ; simpa only [coe_mul',coe_star',coe_zero',star_zero,mul_zero,zero_apply] using hq.1 ξ) Φ
  have hsum := (Complex.continuous_re.continuousAt.tendsto.comp hsP).add
    (Complex.continuous_re.continuousAt.tendsto.comp hsQ)
  simpa only [Φ,heq,map_zero,Complex.zero_re,zero_add,Function.comp_def,d] using hsum

theorem normalPositive_to_strongStar {I : Type*} {l : Filter I}
    (a : I → M) (b : M)
    (ha : NormalPositiveStrongStarTendsto (concretePredualIsometry M) a l b) :
    StrongStarTendsto (fun i => (a i:H →L[ℂ] H)) l (b:H →L[ℂ] H) := by
  let π : M →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype
  have hπ (x : M) : π x=(x:H →L[ℂ] H) := rfl
  have hn (ξ : H) : coefficient π ξ ξ∈normalDual (concretePredualIsometry M) := by
    rw [normalDual_eq_coefficientPredual M]
    exact (coefficientVector M ξ ξ).property
  have hfix (ξ : H) : normalProjection (concretePredualIsometry M) π ξ=ξ :=
    normalProjection_apply_eq_self_of_diagonal_normal (concretePredualIsometry M) π ξ (hn ξ)
  have hProj : normalProjection (concretePredualIsometry M) π=(1:H →L[ℂ] H) := by
    apply ContinuousLinearMap.ext
    intro ξ
    simpa only [one_apply_eq_self] using hfix ξ
  have hc := strongStarTendsto_compressed_of_normalPositive (concretePredualIsometry M) π ha
  simpa only [hProj,one_mul,hπ] using hc

theorem bounded_topology_iff_strongStar {I : Type*} {l : Filter I}
    (a : I → M) (b : M) (C : ℝ) (hbound : ∀ i, ‖a i‖≤C) :
    Tendsto a l (@nhds M (NormalSeminorm.strongStarTopology (concretePredualIsometry M)) b) ↔
      StrongStarTendsto (fun i => (a i:H →L[ℂ] H)) l (b:H →L[ℂ] H) := by
  rw [NormalSeminorm.tendsto_topology_iff_normalPositive]
  exact ⟨normalPositive_to_strongStar M a b,bounded_strongStar_to_normalPositive M a b C hbound⟩

end SpectralIsometry.ConcreteNormalSeminorm

