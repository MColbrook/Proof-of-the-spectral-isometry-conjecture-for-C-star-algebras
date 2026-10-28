module

public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Complex.Basic

/-!
# Generic Weak Star Functional

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.WeakStarFunctional

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem exists_evaluation_of_continuous (F : StrongDual ℂ X →ₗ[ℂ] ℂ)
    (hF : Continuous (fun f : WeakDual ℂ X => F (WeakDual.toStrongDual f))) :
    ∃ x : X, ∀ f : StrongDual ℂ X, F f=f x := by
  let L : StrongDual ℂ (WeakDual ℂ X) :=
    { toLinearMap := F.comp WeakDual.toStrongDual.toLinearMap
      cont := hF }
  obtain ⟨x,hx⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ X) L
  refine ⟨x,fun f => ?_⟩
  have hh := congrArg (fun g : StrongDual ℂ (WeakDual ℂ X) => g (StrongDual.toWeakDual f)) hx
  exact hh.symm

theorem continuous_iff_evaluation (F : StrongDual ℂ X →ₗ[ℂ] ℂ) :
    Continuous (fun f : WeakDual ℂ X => F (WeakDual.toStrongDual f)) ↔
      ∃ x : X, ∀ f : StrongDual ℂ X, F f=f x := by
  refine ⟨exists_evaluation_of_continuous F,?_⟩
  rintro ⟨x,hx⟩
  have he : (fun f : WeakDual ℂ X => F (WeakDual.toStrongDual f))=(fun f => f x) :=
    funext (fun f => hx (WeakDual.toStrongDual f))
  rw [he]
  exact WeakDual.eval_continuous x

end SpectralIsometry.WeakStarFunctional

