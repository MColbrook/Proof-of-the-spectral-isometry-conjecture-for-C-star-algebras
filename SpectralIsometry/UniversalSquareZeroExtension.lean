module

public import SpectralIsometry.BidualOperatorCore
public import SpectralIsometry.UniversalNormalContinuity
public import SpectralIsometry.NilpotentApproximation
public import SpectralIsometry.SquareZeroPreservation

/-!
# Universal Square Zero Extension

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace SpectralIsometry.BidualFoundation.UniversalSquareZeroExtension

open UniversalWeakClosure CoefficientPredual OperatorExtension StrongStarApproximation
open OAI.BoundedHochschild.KadisonRingrose

universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] complexNormedSpaceSelf predualNormedGroup predualNormedSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private def operatorInclusion {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    M →L[ℂ] (H →L[ℂ] H) where
  toLinearMap :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  cont := continuous_subtype_val

theorem lift_strongStarTendsto (T : A →L[ℂ] B) {ι : Type*} {l : Filter ι}
    (a : ι → algebra A) (x : algebra A)
    (ha : StrongStarTendsto (fun i => (a i : Hilbert A →L[ℂ] Hilbert A)) l
      (x : Hilbert A →L[ℂ] Hilbert A)) :
    StrongStarTendsto (fun i => (lift T (a i) : Hilbert B →L[ℂ] Hilbert B)) l
      (lift T x : Hilbert B →L[ℂ] Hilbert B) := by
  let V := (operatorInclusion (algebra B)).comp (lift T)
  have hV : UniversalNormalContinuity.HasNormalCoefficients A V :=
    fun ξ η => lift_vector_pairing T ξ η
  exact UniversalNormalContinuity.strongStarTendsto_map A V hV a x ha

theorem exists_original_squareZero_net (n : algebra A) (h2 : n^2=0) :
    ∃ a : NilIndex (Hilbert A) → A,
      (∀ i, (a i)^2=0) ∧ (∀ i, ‖a i‖≤‖n‖) ∧
      StrongStarTendsto (fun i => (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A))
        atTop (n : Hilbert A →L[ℂ] Hilbert A) := by
  classical
  let S : StarSubalgebra ℂ (Hilbert A →L[ℂ] Hilbert A) :=
    (universalGNSRepresentation (M:=A)).range
  have hS : IsClosed (S : Set (Hilbert A →L[ℂ] Hilbert A)) :=
    representationRange_isClosed A
  have hn : (n : Hilbert A →L[ℂ] Hilbert A) ∈
      Set.centralizer (Set.centralizer (S : Set (Hilbert A →L[ℂ] Hilbert A))) := by
    have hh := n.property
    change (n : Hilbert A →L[ℂ] Hilbert A) ∈ (weakClosure S : Set (Hilbert A →L[ℂ] Hilbert A)) at hh
    rwa [weakClosure_coe] at hh
  have hn2 : (n : Hilbert A →L[ℂ] Hilbert A)^2=0 := congrArg Subtype.val h2
  obtain ⟨w,hwS,hw2,hwN,hwT⟩ := exists_bounded_squareZero_net S hS _ hn hn2
  choose a ha using hwS
  have he (i : NilIndex (Hilbert A)) : universalGNSRepresentation (a i)=w i := ha i
  refine ⟨a,fun i => ?_,fun i => ?_,?_⟩
  · apply universalGNSRepresentation_injective
    calc universalGNSRepresentation ((a i)^2) = (universalGNSRepresentation (a i))^2 := map_pow _ _ _
         _ = (w i)^2 := congrArg (fun T : Hilbert A →L[ℂ] Hilbert A => T^2) (he i)
         _ = 0 := hw2 i
         _ = universalGNSRepresentation 0 := (map_zero _).symm
  · calc ‖a i‖ = ‖universalGNSRepresentation (a i)‖ :=
           (universalGNSRepresentation_norm (a i)).symm
         _ = ‖w i‖ := congrArg norm (he i)
         _ ≤ ‖n‖ := hwN i
  · have hefun : (fun i => (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A))=w := funext he
    rw [hefun]
    exact hwT

/-- The full source approximation consequence for any bounded square-zero
preserver. The normality and all convergence facts of its second transpose
are proved internally, with no extra bidual continuity assumption. -/
theorem lift_preserves_squareZero (T : A →L[ℂ] B)
    (hT : ∀ a : A, a^2=0 → (T a)^2=0)
    (n : algebra A) (hn : n^2=0) : (lift T n)^2=0 := by
  obtain ⟨a,ha2,haN,haT⟩ := exists_original_squareZero_net n hn
  letI : (atTop : Filter (NilIndex (Hilbert A))).NeBot := nilIndex_filter_neBot
  have hlim := lift_strongStarTendsto T (fun i => inclusion A (a i)) n haT
  have hbound (i : NilIndex (Hilbert A)) :
      ‖(lift T (inclusion A (a i)) : Hilbert B →L[ℂ] Hilbert B)‖≤‖lift T‖*‖n‖ :=
    ((lift T).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (by simpa only [inclusion_norm] using haN i) (norm_nonneg _))
  have hprod := strongStarTendsto_mul_of_norm_bounds hlim hlim
    (Eventually.of_forall hbound) (Eventually.of_forall hbound)
  have hzero (i : NilIndex (Hilbert A)) :
      (lift T (inclusion A (a i)) : Hilbert B →L[ℂ] Hilbert B) *
      (lift T (inclusion A (a i)) : Hilbert B →L[ℂ] Hilbert B)=0 := by
    rw [lift_inclusion]
    have hh := congrArg (inclusion B) (hT (a i) (ha2 i))
    rw [map_pow,map_zero,pow_two] at hh
    exact congrArg Subtype.val hh
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro ξ
  change ((lift T n : Hilbert B →L[ℂ] Hilbert B) *
    (lift T n : Hilbert B →L[ℂ] Hilbert B)) ξ=0
  have hz : Tendsto
      (fun i => ((lift T (inclusion A (a i)) : Hilbert B →L[ℂ] Hilbert B) *
        (lift T (inclusion A (a i)) : Hilbert B →L[ℂ] Hilbert B)) ξ) atTop (𝓝 0) := by
    simpa only [hzero,zero_apply] using (tendsto_const_nhds (x:=(0 : Hilbert B)))
  exact tendsto_nhds_unique (hprod.1 ξ) hz

theorem spectral_lift_preserves_squareZero (U : A ≃L[ℂ] B)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (h1 : U 1=1)
    (n : algebra A) (hn : n^2=0) : (lift U.toContinuousLinearMap n)^2=0 :=
  lift_preserves_squareZero U.toContinuousLinearMap
    (fun a ha => SquareZeroPreservation.image_square_zero U hr h1 a ha) n hn

end SpectralIsometry.BidualFoundation.UniversalSquareZeroExtension

