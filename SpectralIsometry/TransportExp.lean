module

public import SpectralIsometry.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Tactic.NoncommRing

/-!
# Transport Exp

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

namespace SpectralIsometry.TransportExp

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def innerCLM (h : A) : A →L[ℂ] A :=
  ContinuousLinearMap.mul ℂ A h - (ContinuousLinearMap.mul ℂ A).flip h

@[simp] theorem innerCLM_apply (h a : A) : innerCLM h a = h * a - a * h := rfl

theorem innerCLM_leibniz (h a b : A) :
    innerCLM h (a * b) = innerCLM h a * b + a * innerCLM h b := by
  simp only [innerCLM_apply]
  noncomm_ring

def transportedCLM (U : A ≃L[ℂ] B) (h : A) : B →L[ℂ] B :=
  U.conjContinuousAlgEquiv (innerCLM h)

@[simp] theorem transportedCLM_apply (U : A ≃L[ℂ] B) (h : A) (b : B) :
    transportedCLM U h b = U (h * U.symm b - U.symm b * h) := rfl

theorem exp_transportedCLM (U : A ≃L[ℂ] B) (h : A) (z : ℂ) :
    (NormedSpace.exp (z • transportedCLM U h) : B →L[ℂ] B) =
      U.toContinuousLinearMap.comp
        ((NormedSpace.exp (z • innerCLM h) : A →L[ℂ] A).comp U.symm.toContinuousLinearMap) := by
  have hex : z • innerCLM h ∈ Metric.eball (0 : A →L[ℂ] A)
      (NormedSpace.expSeries ℂ (A →L[ℂ] A)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top, Metric.eball_top_eq_univ]
    exact Set.mem_univ _
  have he := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) U.conjContinuousAlgEquiv
    U.conjContinuousAlgEquiv.continuous (z • innerCLM h) hex
  simpa only [map_smul, transportedCLM, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply,
    ContinuousLinearMap.comp_assoc] using he.symm

theorem exp_innerCLM_radius (h a : A) (z : ℂ) :
    spectralRadius ℂ ((NormedSpace.exp (z • innerCLM h) : A →L[ℂ] A) a) =
      spectralRadius ℂ a := by
  obtain ⟨hb, hm⟩ := exp_derivation_automorphism (innerCLM h) (innerCLM_leibniz h) z
  let e : A ≃ₗ[ℂ] A := LinearEquiv.ofBijective
    (NormedSpace.exp (z • innerCLM h) : A →L[ℂ] A).toLinearMap hb
  let φ : A ≃ₐ[ℂ] A := AlgEquiv.ofLinearEquiv e
    (exp_derivation_one (innerCLM h) (innerCLM_leibniz h) z) hm
  change spectralRadius ℂ (φ a) = spectralRadius ℂ a
  simp only [spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq φ a]

theorem exp_transportedCLM_one (U : A ≃L[ℂ] B) (h1 : U 1 = 1) (h : A) (z : ℂ) :
    (NormedSpace.exp (z • transportedCLM U h) : B →L[ℂ] B) 1 = 1 := by
  have hS1 : U.symm 1 = 1 := U.injective (by rw [U.apply_symm_apply, h1])
  rw [exp_transportedCLM]
  change U ((NormedSpace.exp (z • innerCLM h) : A →L[ℂ] A) (U.symm 1)) = 1
  rw [hS1, exp_derivation_one (innerCLM h) (innerCLM_leibniz h) z, h1]

theorem exp_transportedCLM_radius (U : A ≃L[ℂ] B)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (h : A) (z : ℂ) (b : B) :
    spectralRadius ℂ ((NormedSpace.exp (z • transportedCLM U h) : B →L[ℂ] B) b) =
      spectralRadius ℂ b := by
  rw [exp_transportedCLM]
  change spectralRadius ℂ (U ((NormedSpace.exp (z • innerCLM h) : A →L[ℂ] A) (U.symm b))) = _
  have hU (a : A) : spectralRadius ℂ (U a) = spectralRadius ℂ a := hr a
  calc
    spectralRadius ℂ (U ((NormedSpace.exp (z • innerCLM h) : A →L[ℂ] A) (U.symm b))) =
        spectralRadius ℂ ((NormedSpace.exp (z • innerCLM h) : A →L[ℂ] A) (U.symm b)) := hU _
    _ = spectralRadius ℂ (U.symm b) := exp_innerCLM_radius _ _ _
    _ = spectralRadius ℂ b := (hU (U.symm b)).symm.trans
      (congrArg (spectralRadius ℂ) (U.apply_symm_apply b))

end SpectralIsometry.TransportExp

