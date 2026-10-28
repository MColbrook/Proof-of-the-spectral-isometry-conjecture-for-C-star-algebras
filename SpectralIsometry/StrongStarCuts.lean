module

public import SpectralIsometry.StrongStarCFC
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Tactic.FunProp

/-!
# Strong Star Cuts

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open Filter Topology
open scoped CStarAlgebra ContinuousFunctionalCalculus

namespace SpectralIsometry.StrongStarApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem strongStarTendsto_cfc_of_norm_bounds {ι : Type*} {l : Filter ι}
    (a : ι → Op (H := H)) (b : Op (H := H)) (C : ℝ)
    (ha : ∀ i, IsSelfAdjoint (a i)) (hb : IsSelfAdjoint b)
    (hCa : ∀ i, ‖a i‖ ≤ C) (hCb : ‖b‖ ≤ C) (hab : StrongStarTendsto a l b)
    (f : ℝ → ℝ) (hf : Continuous f) :
    StrongStarTendsto (fun i => cfc f (a i)) l (cfc f b) := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · letI := hH
    have he : (fun i => cfc f (a i)) = fun _ : ι => cfc f b := by
      funext i
      ext x
      exact Subsingleton.elim _ _
    rw [he]
    exact strongStarTendsto_const l (cfc f b)
  · letI := hH
    let s : Set ℝ := Set.Icc (-C) C
    have hs : IsCompact s := isCompact_Icc
    letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
    have hspec (d : Op (H := H)) (hd : ‖d‖ ≤ C) : spectrum ℝ d ⊆ s := by
      intro t ht
      have hnorm : |t| ≤ C := by
        simpa only [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem ht).trans hd
      exact abs_le.mp hnorm
    let g : C(s, ℝ) := ⟨fun x => f x, hf.comp continuous_subtype_val⟩
    have he (d : Op (H := H)) (hd : IsSelfAdjoint d) (hds : spectrum ℝ d ⊆ s) :
        cfcHomSuperset hd hds g = cfc f d := by
      rw [cfcHomSuperset_apply, cfc_apply f d hd hf.continuousOn]
      rfl
    have hm := strongStarTendsto_cfcHomSuperset hs a b ha hb
      (fun i => hspec (a i) (hCa i)) (hspec b hCb) hab g
    simpa only [he] using hm

theorem strongStarTendsto_posPart {ι : Type*} {l : Filter ι}
    (a : ι → Op (H := H)) (b : Op (H := H)) (C : ℝ)
    (ha : ∀ i, IsSelfAdjoint (a i)) (hb : IsSelfAdjoint b)
    (hCa : ∀ i, ‖a i‖ ≤ C) (hCb : ‖b‖ ≤ C) (hab : StrongStarTendsto a l b) :
    StrongStarTendsto (fun i => (a i)⁺) l b⁺ := by
  have he (d : Op (H := H)) : d⁺ = cfc (fun t : ℝ => t⁺) d := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc]
  simpa only [← he] using strongStarTendsto_cfc_of_norm_bounds a b C ha hb hCa hCb hab
    (fun t : ℝ => t⁺) (by fun_prop)

theorem strongStarTendsto_negPart {ι : Type*} {l : Filter ι}
    (a : ι → Op (H := H)) (b : Op (H := H)) (C : ℝ)
    (ha : ∀ i, IsSelfAdjoint (a i)) (hb : IsSelfAdjoint b)
    (hCa : ∀ i, ‖a i‖ ≤ C) (hCb : ‖b‖ ≤ C) (hab : StrongStarTendsto a l b) :
    StrongStarTendsto (fun i => (a i)⁻) l b⁻ := by
  have he (d : Op (H := H)) : d⁻ = cfc (fun t : ℝ => t⁻) d := by
    rw [CFC.negPart_def, cfcₙ_eq_cfc]
  simpa only [← he] using strongStarTendsto_cfc_of_norm_bounds a b C ha hb hCa hCb hab
    (fun t : ℝ => t⁻) (by fun_prop)

theorem posPart_mem (S : StarSubalgebra ℂ (Op (H := H)))
    (hS : IsClosed (S : Set (Op (H := H)))) (a : Op (H := H)) (ha : a ∈ S) : a⁺ ∈ S := by
  letI : IsClosed (S : Set (Op (H := H))) := hS
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := S) (fun t : ℝ => t⁺) ha

theorem negPart_mem (S : StarSubalgebra ℂ (Op (H := H)))
    (hS : IsClosed (S : Set (Op (H := H)))) (a : Op (H := H)) (ha : a ∈ S) : a⁻ ∈ S := by
  letI : IsClosed (S : Set (Op (H := H))) := hS
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := S) (fun t : ℝ => t⁻) ha

end SpectralIsometry.StrongStarApproximation

