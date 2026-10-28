module

public import SpectralIsometry.UniversalApproximation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Universal Self Adjoint Approximation

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace SpectralIsometry.BidualFoundation.UniversalSelfAdjointApproximation

open UniversalWeakClosure StrongStarApproximation

private theorem half_add_self {E : Type*} [AddCommGroup E] [Module ℂ E] (y : E) :
    (1/2:ℂ) • (y+y)=y := by
  rw [←two_smul ℂ y,smul_smul]
  norm_num

private theorem symmetrization_strongStar {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} {l : Filter ι}
    {a : ι → (H →L[ℂ] H)} {x : H →L[ℂ] H}
    (ha : StrongStarTendsto a l x) (hx : IsSelfAdjoint x) :
    StrongStarTendsto (fun i => (1/2:ℂ) • (a i+star (a i))) l x := by
  have hself (i : ι) : star ((1/2:ℂ) • (a i+star (a i)))=
      (1/2:ℂ) • (a i+star (a i)) := by
    simp only [star_smul,star_add,star_star]
    norm_num
    rw [add_comm]
  have ht (ξ : H) : Tendsto (fun i => ((1/2:ℂ) • (a i+star (a i))) ξ) l (𝓝 (x ξ)) := by
    simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,hx.star_eq,
      half_add_self] using ((ha.1 ξ).add (ha.2 ξ)).const_smul (1/2:ℂ)
  exact ⟨ht,fun ξ => by simpa only [hself,hx.star_eq] using ht ξ⟩

universe u
variable (A : Type u) [CStarAlgebra A]
attribute [local instance] UniversalWeakClosure.orderedA UniversalWeakClosure.starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem exists_bounded_net (x : algebra A) (hx : IsSelfAdjoint x) :
    ∃ a : UniversalApproximation.Index A → A,
      (∀ i, IsSelfAdjoint (a i)) ∧ (∀ i, ‖a i‖≤‖x‖) ∧
      StrongStarTendsto (fun i => (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A)) atTop
        (x : Hilbert A →L[ℂ] Hilbert A) := by
  obtain ⟨a,haN,haT⟩ := UniversalApproximation.exists_bounded_net A x
  let b : UniversalApproximation.Index A → A := fun i => (1/2:ℂ) • (a i+star (a i))
  have hbSA (i : UniversalApproximation.Index A) : IsSelfAdjoint (b i) := by
    change star ((1/2:ℂ) • (a i+star (a i)))=(1/2:ℂ) • (a i+star (a i))
    simp only [star_smul,star_add,star_star]
    norm_num
    rw [add_comm]
  have hbN (i : UniversalApproximation.Index A) : ‖b i‖≤‖x‖ := by
    dsimp only [b]
    rw [norm_smul]
    have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
    rw [hhalf]
    have hh := norm_add_le (a i) (star (a i))
    rw [norm_star] at hh
    linarith [haN i]
  have hxOp : IsSelfAdjoint (x : Hilbert A →L[ℂ] Hilbert A) := congrArg Subtype.val hx.star_eq
  have ht := symmetrization_strongStar haT hxOp
  have hbOp (i : UniversalApproximation.Index A) :
      (inclusion A (b i) : Hilbert A →L[ℂ] Hilbert A)=
      (1/2:ℂ) • ((inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A)+
        star (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A)) := by
    change OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation (b i)=
      (1/2:ℂ) • (OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation (a i)+
        star (OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation (a i)))
    dsimp only [b]
    rw [map_smul,map_add,map_star]
  exact ⟨b,hbSA,hbN,by simpa only [hbOp] using ht⟩

end SpectralIsometry.BidualFoundation.UniversalSelfAdjointApproximation

