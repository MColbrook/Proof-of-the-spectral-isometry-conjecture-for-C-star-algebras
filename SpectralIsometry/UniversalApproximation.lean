module

public import SpectralIsometry.BidualFoundation
public import SpectralIsometry.KaplanskyNets
import Mathlib.Tactic.Positivity

/-!
# Universal Approximation

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SpectralIsometry.BidualFoundation.UniversalApproximation

open UniversalWeakClosure StrongStarApproximation
open OAI.BoundedHochschild.KadisonRingrose

universe u

private theorem real_inv_smul_cancel {E : Type*} [MulAction ℝ E]
    (r : ℝ) (hr : r≠0) (x : E) : r • (r⁻¹ • x)=x := by
  rw [smul_smul,mul_inv_cancel₀ hr,one_smul]

/- Reuse the checked generic real-scalar limit argument from the private
strongStarTendsto_real_smul leaf in SpectralIsometry.NilpotentApproximation. It is stated
before the dependent universal-GNS dictionaries to keep elaboration small. -/
private theorem genericStrongStar_real_smul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} {l : Filter ι}
    {a : ι → (H →L[ℂ] H)} {b : H →L[ℂ] H} (ha : StrongStarTendsto a l b) (r : ℝ) :
    StrongStarTendsto (fun i => r • a i) l (r • b) := by
  constructor
  · intro ξ
    simpa only [ContinuousLinearMap.smul_apply] using (ha.1 ξ).const_smul r
  · intro ξ
    simpa only [star_smul,star_trivial,ContinuousLinearMap.smul_apply] using
      (ha.2 ξ).const_smul r

variable (A : Type u) [CStarAlgebra A]

attribute [local instance] UniversalWeakClosure.orderedA UniversalWeakClosure.starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder

abbrev Index := ProbeIndex (Hilbert A)

theorem index_neBot : (atTop : Filter (Index A)).NeBot := probeIndex_filter_neBot

set_option backward.isDefEq.respectTransparency.types false in
private theorem representation_range_closed :
    IsClosed (Set.range (universalGNSRepresentation (M:=A))) := by
  have hi : Isometry (universalGNSRepresentation (M:=A)) :=
    AddMonoidHomClass.isometry_of_norm (universalGNSRepresentation (M:=A))
      (fun a : A => universalGNSRepresentation_norm (M:=A) a)
  exact hi.isClosedEmbedding.isClosed_range

/- The norm-one density theorem is discharged from the matrix construction. -/
set_option backward.isDefEq.respectTransparency.types false in
theorem exists_contraction_net (x : algebra A) (hx : ‖x‖≤1) :
    ∃ a : Index A → A, (∀ i, ‖a i‖≤1) ∧
      StrongStarTendsto (fun i => (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A))
        atTop (x : Hilbert A →L[ℂ] Hilbert A) := by
  classical
  let S : StarSubalgebra ℂ (Hilbert A →L[ℂ] Hilbert A) :=
    (universalGNSRepresentation (M:=A)).range
  have hS : IsClosed (S : Set (Hilbert A →L[ℂ] Hilbert A)) := by
    change IsClosed (Set.range (universalGNSRepresentation (M:=A)))
    exact representation_range_closed A
  have hxm : (x : Hilbert A →L[ℂ] Hilbert A) ∈
      Set.centralizer (Set.centralizer (S : Set (Hilbert A →L[ℂ] Hilbert A))) := by
    have hh : (x : Hilbert A →L[ℂ] Hilbert A) ∈
        (weakClosure S : Set (Hilbert A →L[ℂ] Hilbert A)) := x.property
    rwa [weakClosure_coe S] at hh
  obtain ⟨b,hbM,hbN,hbT⟩ := exists_contraction_strongStar_net S
    hS (x : Hilbert A →L[ℂ] Hilbert A) hxm hx
  have hex (i : Index A) : ∃ a : A, universalGNSRepresentation a=b i := hbM i
  choose a ha using hex
  have hnorm (i : Index A) : ‖a i‖≤1 := by
    calc ‖a i‖ = ‖(inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A)‖ := (inclusion_norm A (a i)).symm
         _ = ‖b i‖ := congrArg norm (ha i)
         _ ≤ 1 := hbN i
  have heq : (fun i => (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A))=b := by
    funext i
    exact ha i
  refine ⟨a,hnorm,?_⟩
  rw [heq]
  exact hbT

set_option backward.isDefEq.respectTransparency.types false in
private theorem real_smul_inclusion (r : ℝ) (a : A) :
    (inclusion A (r • a) : Hilbert A →L[ℂ] Hilbert A)=
      r • (inclusion A a : Hilbert A →L[ℂ] Hilbert A) := by
  exact congrArg (fun z : algebra A => (z : Hilbert A →L[ℂ] Hilbert A))
    (((inclusionCLM A).restrictScalars ℝ).map_smul r a)

/- Arbitrary elements have original-algebra approximants bounded by their own
norm. The zero case and rescaling are internal, with no unit-ball premise. -/
set_option backward.isDefEq.respectTransparency.types false in
theorem exists_bounded_net (x : algebra A) :
    ∃ a : Index A → A, (∀ i, ‖a i‖≤‖x‖) ∧
      StrongStarTendsto (fun i => (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A))
        atTop (x : Hilbert A →L[ℂ] Hilbert A) := by
  by_cases hx0 : x=0
  · subst x
    refine ⟨fun _ => 0,fun _ => by simp,?_⟩
    simpa only [map_zero,ZeroMemClass.coe_zero] using
      strongStarTendsto_const (H:=Hilbert A) atTop 0
  let r : ℝ := ‖x‖
  have hr : 0<r := norm_pos_iff.mpr hx0
  let y : algebra A := r⁻¹ • x
  have hy : ‖y‖≤1 := by
    dsimp only [y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    change r⁻¹*r≤1
    rw [inv_mul_cancel₀ hr.ne']
  obtain ⟨a,haN,haT⟩ := exists_contraction_net A y hy
  let b : Index A → A := fun i => r • a i
  have hbN (i : Index A) : ‖b i‖≤‖x‖ := by
    dsimp only [b]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (haN i) hr.le
  have hscale : r • y=x := by
    dsimp only [y]
    exact real_inv_smul_cancel r hr.ne' x
  have hlim : StrongStarTendsto
      (fun i => r • (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A))
      atTop (r • (y : Hilbert A →L[ℂ] Hilbert A)) := genericStrongStar_real_smul haT r
  have hscaleOp : r • (y : Hilbert A →L[ℂ] Hilbert A)=
      (x : Hilbert A →L[ℂ] Hilbert A) := congrArg Subtype.val hscale
  refine ⟨b,hbN,?_⟩
  simpa only [b,real_smul_inclusion,hscaleOp] using hlim

end SpectralIsometry.BidualFoundation.UniversalApproximation

