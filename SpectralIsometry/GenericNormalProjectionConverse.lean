module

public import SpectralIsometry.GenericNormalProjectionContinuity
public import SpectralIsometry.BidualFoundation

/-!
# Generic Normal Projection Converse

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.NormalProjectionContinuity

open Filter Topology OAI.HochschildNormalPart
open StrongStarApproximation BidualFoundation.UniversalWeakClosure
open OAI.BoundedHochschild.KadisonRingrose
open scoped InnerProductSpace ComplexOrder

universe u w
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

attribute [local instance] BidualFoundation.UniversalWeakClosure.orderedA
  BidualFoundation.UniversalWeakClosure.starOrderedA
attribute [local instance 2000] BidualFoundation.UniversalWeakClosure.complexOrder
  BidualFoundation.UniversalWeakClosure.complexStarOrder

/-- In the actual universal representation, compressed strong-star convergence
detects all intrinsic normal-positive seminorms. This statement does not claim
such detection for an arbitrary representation. -/
theorem normalPositive_of_universal_compressed_strongStar {ι : Type w} {l : Filter ι}
    {a : ι → M} {b : M}
    (h : StrongStarTendsto
      (fun i => normalProjection e (universalGNSRepresentation (M:=M)) *
        universalGNSRepresentation (a i)) l
      (normalProjection e (universalGNSRepresentation (M:=M)) * universalGNSRepresentation b)) :
    NormalPositiveStrongStarTendsto e a l b := by
  intro ψ φ hφ hn
  let π := universalGNSRepresentation (M:=M)
  let v := cyclicVector M ψ
  change StrongStarTendsto (fun i => normalProjection e π * π (a i)) l
    (normalProjection e π * π b) at h
  have hcoef : coefficient π v v = φ := by
    ext x
    exact (cyclicVector_coefficient M ψ x).trans (hφ x).symm
  have hnormal : coefficient π v v ∈ normalDual e := hcoef.symm ▸ hn
  have hfix : normalProjection e π v=v :=
    normalProjection_apply_eq_self_of_diagonal_normal e π v hnormal
  have hψ : diagonalPositive π v=ψ := by
    ext x
    exact cyclicVector_coefficient M ψ x
  have hd : Tendsto (fun i => π (a i-b) v) l (𝓝 0) := by
    have ht := (h.1 v).sub (tendsto_const_nhds (x:=(normalProjection e π * π b) v) (f:=l))
    simpa only [sub_self,compressed_difference,hfix] using ht
  have hds : Tendsto (fun i => π (star (a i-b)) v) l (𝓝 0) := by
    have ht := (h.2 v).sub (tendsto_const_nhds (x:=star (normalProjection e π * π b) v) (f:=l))
    simpa only [sub_self,star_compression,compressed_difference,star_sub,hfix] using ht
  have hsq : Tendsto (fun i => ‖π (a i-b) v‖^2 + ‖π (star (a i-b)) v‖^2) l (𝓝 (0:ℝ)) := by
    simpa only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add] using
      (hd.norm.pow 2).add (hds.norm.pow 2)
  rw [←hψ]
  simpa only [diagonalPositive_star_mul_self,diagonalPositive_mul_star_self] using hsq

/-- Exact equivalence for every actual original C*-algebra and supplied Wstar
predual, using its universal normal compressed representation. -/
theorem normalPositive_iff_universal_compressed_strongStar {ι : Type w} {l : Filter ι}
    {a : ι → M} {b : M} :
    NormalPositiveStrongStarTendsto e a l b ↔
      StrongStarTendsto
        (fun i => normalProjection e (universalGNSRepresentation (M:=M)) *
          universalGNSRepresentation (a i)) l
        (normalProjection e (universalGNSRepresentation (M:=M)) * universalGNSRepresentation b) :=
  ⟨strongStarTendsto_compressed_of_normalPositive e (universalGNSRepresentation (M:=M)),
    normalPositive_of_universal_compressed_strongStar e⟩

end SpectralIsometry.NormalProjectionContinuity

