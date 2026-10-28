module

public import SpectralIsometry.GenericWeakStarFunctional
public import SpectralIsometry.UniversalNormalMapCompression

/-!
# Weak Star Normal Continuity

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace SpectralIsometry.BidualFoundation.WeakStarNormalContinuity

open UniversalWeakClosure UniversalNormalProjection OAI.HochschildNormalPart

universe u v w
variable {M X : Type u} {N Y : Type v} [CStarAlgebra M] [CStarAlgebra N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
  (eM : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N)

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def weakStarMap (T : M →L[ℂ] N) (f : WeakDual ℂ X) : WeakDual ℂ Y :=
  StrongDual.toWeakDual (eN.symm (T (eM (WeakDual.toStrongDual f))))

/-- The weak-star topologies are the actual weak dual topologies of the
supplied preduals, pulled back through their conjugate-linear isometries. -/
def WeakStarContinuous (T : M →L[ℂ] N) : Prop := Continuous (weakStarMap eM eN T)

private def coordinateFunctional (T : M →L[ℂ] N) (y : Y) : StrongDual ℂ X →ₗ[ℂ] ℂ where
  toFun f := eN.symm (T (eM f)) y
  map_add' f g := by simp only [map_add,add_apply]
  map_smul' z f := by
    simp only [map_smulₛₗ,map_smul,RingHom.id_apply,starRingEnd_apply,star_star,
      ContinuousLinearMap.smul_apply,smul_eq_mul]

/-- Weak-star continuity really supplies normality of every pulled-back
normal functional. It is proved from the weak representation theorem. -/
theorem normalFunctionalPullback_of_weakStarContinuous (T : M →L[ℂ] N)
    (hT : WeakStarContinuous eM eN T) : NormalFunctionalPullback eM eN T := by
  intro φ hφ
  obtain ⟨y,hy⟩ := (mem_normalDual eN φ).mp hφ
  have hcoord : Continuous (fun f : WeakDual ℂ X =>
      coordinateFunctional eM eN T y (WeakDual.toStrongDual f)) :=
    (WeakDual.eval_continuous y).comp hT
  obtain ⟨x,hx⟩ := WeakStarFunctional.exists_evaluation_of_continuous
    (coordinateFunctional eM eN T y) hcoord
  apply (mem_normalDual eM (φ.comp T)).mpr
  refine ⟨x,fun a => ?_⟩
  change φ (T a)=star (eM.symm a x)
  rw [hy (T a)]
  apply congrArg star
  have hh := hx (eM.symm a)
  change eN.symm (T (eM (eM.symm a))) y = (eM.symm a) x at hh
  simpa only [eM.apply_symm_apply] using hh

/-- Manuscript Lemma normal-continuity, in actual predual coordinates and
intrinsic normal-positive seminorms, for every norm-bounded net. No preadjoint,
compression compatibility, or continuity of the canonical lift is assumed. -/
theorem strongStar_on_bounded_sets (T : M →L[ℂ] N)
    (hT : WeakStarContinuous eM eN T) {ι : Type w} {l : Filter ι}
    (a : ι → M) (b : M) (C : ℝ) (_hbound : ∀ i, ‖a i‖≤C)
    (ha : NormalProjectionContinuity.NormalPositiveStrongStarTendsto eM a l b) :
    NormalProjectionContinuity.NormalPositiveStrongStarTendsto eN (fun i => T (a i)) l (T b) :=
  normalPositiveTendsto_map_of_pullback eM eN T
    (normalFunctionalPullback_of_weakStarContinuous eM eN T hT) a b ha

end SpectralIsometry.BidualFoundation.WeakStarNormalContinuity

