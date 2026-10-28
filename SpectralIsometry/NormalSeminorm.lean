module

public import SpectralIsometry.WeakStarNormalContinuity

/-!
# Normal Seminorm

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace SpectralIsometry.NormalSeminorm

open OAI.HochschildNormalPart NormalProjectionContinuity

universe u v w
variable {M X : Type u} {N Y : Type v} [CStarAlgebra M] [CStarAlgebra N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

local instance orderedM : PartialOrder M := CStarAlgebra.spectralOrder M
local instance starOrderedM : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
local instance (priority := 2000) complexOrder : PartialOrder ℂ := Complex.partialOrder
local instance (priority := 2000) complexStarOrder : StarOrderedRing ℂ := RCLike.toStarOrderedRing

def seminorm (ψ : M →ₚ[ℂ] ℂ) (x : M) : ℝ :=
  Real.sqrt ((ψ (star x*x)).re+(ψ (x*star x)).re)

theorem quadratic_sum_nonneg (ψ : M →ₚ[ℂ] ℂ) (x : M) :
    0≤(ψ (star x*x)).re+(ψ (x*star x)).re := by
  apply add_nonneg
  · exact (Complex.nonneg_iff.mp (ψ.map_nonneg (star_mul_self_nonneg x))).1
  · exact (Complex.nonneg_iff.mp (ψ.map_nonneg (mul_star_self_nonneg x))).1

def SeminormTendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {ι : Type w}
    (a : ι → M) (l : Filter ι) (b : M) : Prop :=
  ∀ (ψ : M →ₚ[ℂ] ℂ) (φ : StrongDual ℂ M),
    (∀ x : M, φ x=ψ x) → φ ∈ normalDual e →
    Tendsto (fun i => seminorm ψ (a i-b)) l (𝓝 0)

theorem seminormTendsto_iff (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {ι : Type w}
    (a : ι → M) (l : Filter ι) (b : M) :
    SeminormTendsto e a l b ↔ NormalPositiveStrongStarTendsto e a l b := by
  constructor
  · intro h ψ φ heq hn
    have hs := (h ψ φ heq hn).pow 2
    simpa only [seminorm,Real.sq_sqrt (quadratic_sum_nonneg ψ _),zero_pow (by decide : (2:ℕ)≠0)] using hs
  · intro h ψ φ heq hn
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (h ψ φ heq hn)
    simpa only [seminorm,Real.sqrt_zero,Function.comp_def] using hs

theorem strongStar_on_bounded_sets (eM : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N) (T : M →L[ℂ] N)
    (hT : BidualFoundation.WeakStarNormalContinuity.WeakStarContinuous eM eN T)
    {ι : Type w} {l : Filter ι} (a : ι → M) (b : M) (C : ℝ)
    (hbound : ∀ i, ‖a i‖≤C) (ha : SeminormTendsto eM a l b) :
    SeminormTendsto eN (fun i => T (a i)) l (T b) := by
  apply (seminormTendsto_iff eN _ _ _).mpr
  exact BidualFoundation.WeakStarNormalContinuity.strongStar_on_bounded_sets
    eM eN T hT a b C hbound ((seminormTendsto_iff eM _ _ _).mp ha)

end SpectralIsometry.NormalSeminorm

