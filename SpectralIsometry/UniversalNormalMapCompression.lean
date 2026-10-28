module

public import SpectralIsometry.UniversalNormalSupport
public import SpectralIsometry.UniversalSquareZeroExtension
public import SpectralIsometry.GenericNormalProjectionConverse

/-!
# Universal Normal Map Compression

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProductSpace

namespace SpectralIsometry.BidualFoundation.UniversalNormalProjection

open UniversalWeakClosure CoefficientPredual OperatorExtension StrongStarApproximation
open OAI.HochschildNormalPart OAI.BoundedHochschild.KadisonRingrose

private theorem strongStar_const_mul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} {l : Filter ι}
    {a : ι → (H →L[ℂ] H)} {b : H →L[ℂ] H}
    (ha : StrongStarTendsto a l b) (c : H →L[ℂ] H) :
    StrongStarTendsto (fun i => c*a i) l (c*b) := by
  constructor
  · intro ξ
    simpa only [mul_apply_eq_comp,Function.comp_def,Function.comp_apply] using
      c.continuous.continuousAt.tendsto.comp (ha.1 ξ)
  · intro ξ
    simpa only [star_mul,mul_apply_eq_comp] using ha.2 (star c ξ)

universe u v w
variable {M X : Type u} {N Y : Type v} [CStarAlgebra M] [CStarAlgebra N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
  (eM : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N)

attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] complexNormedSpaceSelf dualNormedGroup dualNormedSpace
attribute [local instance] predualNormedGroup predualNormedSpace
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

def NormalFunctionalPullback (T : M →L[ℂ] N) : Prop :=
  ∀ φ : StrongDual ℂ N, φ ∈ normalDual eN → φ.comp T ∈ normalDual eM

/-- Exact compatibility is proved by normal coefficient pairings and the
supported canonical extension. No compatibility equation is assumed. -/
theorem compressed_lift_inclusion (T : M →L[ℂ] N)
    (hT : NormalFunctionalPullback eM eN T) (a : M) :
    projection eN * (lift T (projectionElement eM * inclusion M a) : Hilbert N →L[ℂ] Hilbert N)=
      projection eN * universalGNSRepresentation (T a) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  let Ψ : predual N := coefficientVector (algebra N) η (projection eN ξ)
  let Φ : predual M := preadjoint T Ψ
  have hΨ : restriction N Ψ ∈ normalDual eN := by
    change coefficient (universalGNSRepresentation (M:=N)) η (projection eN ξ) ∈ normalDual eN
    apply (mem_normalVectors eN (universalGNSRepresentation (M:=N)) (projection eN ξ)).mp
    simp [projection,normalProjection]
  have hΦ : restriction M Φ ∈ normalDual eM := by
    change restriction M (preadjoint T Ψ) ∈ normalDual eM
    rw [preadjoint_restriction]
    exact hT _ hΨ
  have hcanon : (canonicalPredualEquiv M).symm (restriction M Φ)=Φ :=
    (canonicalPredualEquiv M).symm_apply_apply Φ
  have hs : (Φ : StrongDual ℂ (algebra M)) (projectionElement eM * inclusion M a)=
      (Φ : StrongDual ℂ (algebra M)) (inclusion M a) := by
    have hh := normal_extension_supported eM (restriction M Φ) hΦ (inclusion M a)
    simpa only [hcanon] using hh
  have hp : (Ψ : StrongDual ℂ (algebra N)) (lift T (projectionElement eM * inclusion M a))=
      (Ψ : StrongDual ℂ (algebra N)) (inclusion N (T a)) := by
    calc
      (Ψ : StrongDual ℂ (algebra N)) (lift T (projectionElement eM * inclusion M a)) =
          (Φ : StrongDual ℂ (algebra M)) (projectionElement eM * inclusion M a) :=
        lift_pairing T _ Ψ
      _ = (Φ : StrongDual ℂ (algebra M)) (inclusion M a) := hs
      _ = (Ψ : StrongDual ℂ (algebra N)) (lift T (inclusion M a)) :=
        (lift_pairing T _ Ψ).symm
      _ = (Ψ : StrongDual ℂ (algebra N)) (inclusion N (T a)) :=
        congrArg (fun x : algebra N => (Ψ : StrongDual ℂ (algebra N)) x) (lift_inclusion T a)
  have hv (x : algebra N) : (Ψ : StrongDual ℂ (algebra N)) x=
      ⟪η,(projection eN * (x : Hilbert N →L[ℂ] Hilbert N)) ξ⟫_ℂ := by
    change ⟪η,(x : Hilbert N →L[ℂ] Hilbert N) (projection eN ξ)⟫_ℂ=_
    rw [(projection_central eN x).eq]
    rfl
  rw [hv,hv] at hp
  exact hp

/-- Intermediate intrinsic convergence theorem. Its normal-functional
pullback interface is explicit; weak-star characterization is not presumed
by declaring this theorem. No bound on the net is used by this proof. -/
theorem normalPositiveTendsto_map_of_pullback (T : M →L[ℂ] N)
    (hT : NormalFunctionalPullback eM eN T) {ι : Type w} {l : Filter ι}
    (a : ι → M) (b : M)
    (ha : NormalProjectionContinuity.NormalPositiveStrongStarTendsto eM a l b) :
    NormalProjectionContinuity.NormalPositiveStrongStarTendsto eN (fun i => T (a i)) l (T b) := by
  have hsource : StrongStarTendsto
      (fun i => ((projectionElement eM * inclusion M (a i) : algebra M) : Hilbert M →L[ℂ] Hilbert M)) l
      ((projectionElement eM * inclusion M b : algebra M) : Hilbert M →L[ℂ] Hilbert M) :=
    NormalProjectionContinuity.strongStarTendsto_compressed_of_normalPositive eM
      (universalGNSRepresentation (M:=M)) ha
  have hmid := UniversalSquareZeroExtension.lift_strongStarTendsto T
    (fun i => projectionElement eM * inclusion M (a i))
    (projectionElement eM * inclusion M b) hsource
  have htarget := strongStar_const_mul hmid (projection eN)
  apply NormalProjectionContinuity.normalPositive_of_universal_compressed_strongStar eN
  change StrongStarTendsto
    (fun i => projection eN * universalGNSRepresentation (T (a i))) l
    (projection eN * universalGNSRepresentation (T b))
  simpa only [compressed_lift_inclusion eM eN T hT] using htarget

end SpectralIsometry.BidualFoundation.UniversalNormalProjection

