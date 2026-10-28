module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Generic Dual Isometry

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.GenericDual

universe u v
variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

def dualIsometryEquiv (e : X ≃ₗᵢ[ℂ] Y) : StrongDual ℂ Y ≃ₗᵢ[ℂ] StrongDual ℂ X := by
  let E := e.symm.toContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  refine { E.toLinearEquiv with norm_map' := ?_ }
  intro F
  change ‖E F‖ = ‖F‖
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
    intro x
    change ‖F (e x)‖ ≤ ‖F‖ * ‖x‖
    simpa only [e.norm_map x] using F.le_opNorm (e x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (E F))
    intro y
    have h := (E F).le_opNorm (e.symm y)
    rw [e.symm.norm_map y] at h
    change ‖F (e (e.symm y))‖ ≤ ‖E F‖ * ‖y‖ at h
    rwa [e.apply_symm_apply y] at h

 theorem dualIsometryEquiv_apply (e : X ≃ₗᵢ[ℂ] Y) (F : StrongDual ℂ Y) (x : X) :
    dualIsometryEquiv e F x = F (e x) := rfl

end SpectralIsometry.BidualFoundation.GenericDual

