module

public import SpectralIsometry.GenericDualIsometry
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Generic Transpose Core

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SpectralIsometry.BidualFoundation.OperatorExtension

local instance complexSelfModule : NormedSpace ℂ ℂ := NormedField.toNormedSpace

universe u v
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def transpose (T : E →L[ℂ] F) : StrongDual ℂ F →L[ℂ] StrongDual ℂ E :=
  (ContinuousLinearMap.compL ℂ E F ℂ).flip T

@[simp] theorem transpose_apply (T : E →L[ℂ] F) (φ : StrongDual ℂ F) (a : E) :
    transpose T φ a = φ (T a) := rfl

def secondTranspose (T : E →L[ℂ] F) :
    StrongDual ℂ (StrongDual ℂ E) →L[ℂ] StrongDual ℂ (StrongDual ℂ F) :=
  transpose (transpose T)

@[simp] theorem secondTranspose_apply (T : E →L[ℂ] F)
    (Λ : StrongDual ℂ (StrongDual ℂ E)) (φ : StrongDual ℂ F) :
    secondTranspose T Λ φ = Λ (φ.comp T) := rfl

theorem secondTranspose_canonical (T : E →L[ℂ] F) (a : E) :
    secondTranspose T (NormedSpace.inclusionInDoubleDual ℂ E a) =
      NormedSpace.inclusionInDoubleDual ℂ F (T a) := by
  ext φ
  rfl

end SpectralIsometry.BidualFoundation.OperatorExtension

