module

public import SpectralIsometry.GenericTransposeCore

/-!
# Generic Transpose

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SpectralIsometry.BidualFoundation.OperatorExtension
universe u v w
attribute [local instance] complexSelfModule

local instance dualGroup {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] :
    NormedAddCommGroup (StrongDual ℂ X) := inferInstance

local instance dualSpace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] :
    NormedSpace ℂ (StrongDual ℂ X) := inferInstance

local instance bidualGroup {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] :
    NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance

local instance bidualSpace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] :
    NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance

section Transpose

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

#synth Norm (StrongDual ℂ (StrongDual ℂ E) →L[ℂ] StrongDual ℂ (StrongDual ℂ F))

theorem transpose_norm_le (T : E →L[ℂ] F) : ‖transpose T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro φ
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg T) (norm_nonneg φ))
  intro a
  calc
    ‖transpose T φ a‖ ≤ ‖φ‖ * ‖T a‖ := φ.le_opNorm (T a)
    _ ≤ ‖φ‖ * (‖T‖ * ‖a‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm a) (norm_nonneg φ)
    _ = (‖T‖ * ‖φ‖) * ‖a‖ := by ring

theorem secondTranspose_norm_le (T : E →L[ℂ] F) : ‖secondTranspose T‖ ≤ ‖T‖ :=
  (transpose_norm_le (transpose T)).trans (transpose_norm_le T)

theorem secondTranspose_comp (T : E →L[ℂ] F) (S : F →L[ℂ] G) :
    secondTranspose (S.comp T) = (secondTranspose S).comp (secondTranspose T) := by
  ext Λ φ
  rfl

theorem secondTranspose_add (T S : E →L[ℂ] F) :
    secondTranspose (T + S) = secondTranspose T + secondTranspose S := by
  apply ContinuousLinearMap.ext
  intro Λ
  apply ContinuousLinearMap.ext
  intro φ
  have hc : φ.comp (T + S) = φ.comp T + φ.comp S := by
    apply ContinuousLinearMap.ext
    intro a
    exact φ.map_add (T a) (S a)
  change Λ (φ.comp (T + S)) = Λ (φ.comp T) + Λ (φ.comp S)
  exact (congrArg Λ hc).trans (Λ.map_add (φ.comp T) (φ.comp S))

theorem secondTranspose_smul (z : ℂ) (T : E →L[ℂ] F) :
    secondTranspose (z • T) = z • secondTranspose T := by
  apply ContinuousLinearMap.ext
  intro Λ
  apply ContinuousLinearMap.ext
  intro φ
  have hc : φ.comp (z • T) = z • φ.comp T := by
    apply ContinuousLinearMap.ext
    intro a
    exact φ.map_smul z (T a)
  change Λ (φ.comp (z • T)) = z * Λ (φ.comp T)
  exact (congrArg Λ hc).trans (Λ.map_smul z (φ.comp T))

theorem secondTranspose_id :
    secondTranspose (ContinuousLinearMap.id ℂ E) =
      ContinuousLinearMap.id ℂ (StrongDual ℂ (StrongDual ℂ E)) := by
  ext Λ φ
  rfl

end Transpose

end SpectralIsometry.BidualFoundation.OperatorExtension

