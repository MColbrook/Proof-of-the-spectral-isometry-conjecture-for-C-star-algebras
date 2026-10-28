module

public import SpectralIsometry.UniversalNormalProjection
public import SpectralIsometry.BidualRestriction
public import SpectralIsometry.GenericPredualPullback
public import OAI.Analysis.BoundedHochschild.NormalOperators
public import SpectralIsometry.GenericScalarNormalPart

/-!
# Universal Normal Support

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.UniversalNormalProjection

open UniversalWeakClosure CoefficientPredual OAI.HochschildNormalPart
open OAI.BoundedHochschild.KadisonRingrose
open scoped InnerProductSpace

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

attribute [local instance] UniversalWeakClosure.orderedA UniversalWeakClosure.starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] CoefficientPredual.dualNormedGroup CoefficientPredual.dualNormedSpace
attribute [local instance] UniversalWeakClosure.predualNormedGroup UniversalWeakClosure.predualNormedSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

def projectionElement : algebra M := ⟨projection e,projection_mem e⟩

private theorem positive_compressed_restriction (ψ : M →ₚ[ℂ] ℂ) (a : M) :
    ((positiveExtension M ψ : predual M) : StrongDual ℂ (algebra M))
        (projectionElement e * inclusion M a) =
      scalarNormalPart e (restriction M (positiveExtension M ψ)) a := by
  let v := cyclicVector M ψ
  change ⟪v,projection e (universalGNSRepresentation a v)⟫_ℂ =
    scalarNormalPart e (coefficient (universalGNSRepresentation (M:=M)) v v) a
  rw [scalarNormalPart_coefficient]
  exact congrArg (inner ℂ v)
    (congrArg (fun S : Hilbert M →L[ℂ] Hilbert M => S v)
      (normalProjection_mul e (universalGNSRepresentation (M:=M)) a))

private theorem extension_fourCombination (φ : StrongDual ℂ M) :
    (canonicalPredualEquiv M).symm φ =
      fourCombination M (fun i => positiveExtension M (fourPositiveFamily M φ i)) := by
  apply (canonicalPredualEquiv M).injective
  change restriction M ((canonicalPredualEquiv M).symm φ) =
    restriction M (fourCombination M (fun i => positiveExtension M (fourPositiveFamily M φ i)))
  rw [canonicalPredualEquiv_restrict,restriction_fourCombination]
  apply ContinuousLinearMap.ext
  intro a
  simpa only [add_apply,sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    positiveExtension_apply] using fourPositiveFamily_apply M φ a

theorem compressed_extension_restriction (φ : StrongDual ℂ M) (a : M) :
    (((canonicalPredualEquiv M).symm φ : predual M) : StrongDual ℂ (algebra M))
        (projectionElement e * inclusion M a) = scalarNormalPart e φ a := by
  let g : Fin 4 → predual M := fun i => positiveExtension M (fourPositiveFamily M φ i)
  have hg : restriction M (fourCombination M g)=φ := by
    rw [restriction_fourCombination]
    apply ContinuousLinearMap.ext
    intro b
    simpa only [g,add_apply,sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      positiveExtension_apply] using (fourPositiveFamily_apply M φ b).symm
  have hp (i : Fin 4) :
      (g i : StrongDual ℂ (algebra M)) (projectionElement e * inclusion M a) =
        scalarNormalPart e (restriction M (g i)) a :=
    positive_compressed_restriction e (fourPositiveFamily M φ i) a
  rw [extension_fourCombination φ]
  calc
    ((fourCombination M g : predual M) : StrongDual ℂ (algebra M))
        (projectionElement e * inclusion M a) =
      (g 0 : StrongDual ℂ (algebra M)) (projectionElement e * inclusion M a) -
      (g 1 : StrongDual ℂ (algebra M)) (projectionElement e * inclusion M a) +
      Complex.I * ((g 2 : StrongDual ℂ (algebra M)) (projectionElement e * inclusion M a) -
        (g 3 : StrongDual ℂ (algebra M)) (projectionElement e * inclusion M a)) := rfl
    _ = scalarNormalPart e (restriction M (g 0)) a -
      scalarNormalPart e (restriction M (g 1)) a +
      Complex.I * (scalarNormalPart e (restriction M (g 2)) a -
        scalarNormalPart e (restriction M (g 3)) a) := by
      exact congrArg₂ (fun r s : ℂ => r+Complex.I*s)
        (congrArg₂ (fun r s : ℂ => r-s) (hp 0) (hp 1))
        (congrArg₂ (fun r s : ℂ => r-s) (hp 2) (hp 3))
    _ = scalarNormalPart e (restriction M (fourCombination M g)) a := by
      rw [restriction_fourCombination M g]
      exact (ScalarNormalPart.four_evaluation e (fun i => restriction M (g i)) a).symm
    _ = scalarNormalPart e φ a := congrArg (fun f : StrongDual ℂ M => scalarNormalPart e f a) hg

/-- Original normality is proved to imply support of the unique canonical
extension. No normality of the four positive decomposition pieces is used. -/
theorem normal_extension_supported (φ : StrongDual ℂ M) (hφ : φ ∈ normalDual e)
    (x : algebra M) :
    (((canonicalPredualEquiv M).symm φ : predual M) : StrongDual ℂ (algebra M))
      (projectionElement e * x) =
    (((canonicalPredualEquiv M).symm φ : predual M) : StrongDual ℂ (algebra M)) x := by
  let Φ := (canonicalPredualEquiv M).symm φ
  have h : leftMulPullback (algebra M) Φ (projectionElement e) = Φ := by
    apply (canonicalPredualEquiv M).injective
    apply ContinuousLinearMap.ext
    intro a
    change (Φ : StrongDual ℂ (algebra M)) (projectionElement e * inclusion M a) =
      (Φ : StrongDual ℂ (algebra M)) (inclusion M a)
    calc
      (Φ : StrongDual ℂ (algebra M)) (projectionElement e * inclusion M a) =
        scalarNormalPart e φ a := compressed_extension_restriction e φ a
      _ = φ a := congrArg (fun f : StrongDual ℂ M => f a) (scalarNormalPart_fixes e hφ)
      _ = (Φ : StrongDual ℂ (algebra M)) (inclusion M a) :=
        (congrArg (fun f : StrongDual ℂ M => f a) (canonicalPredualEquiv_restrict M φ)).symm
  exact congrArg (fun Ψ : predual M => (Ψ : StrongDual ℂ (algebra M)) x) h

end SpectralIsometry.BidualFoundation.UniversalNormalProjection

