module

public import SpectralIsometry.BidualDensity

/-!
# Bidual Restriction Norm

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.UniversalWeakClosure

open Filter Topology
open scoped InnerProductSpace
open OAI.BoundedHochschild.KadisonRingrose

universe u
variable (A : Type u) [CStarAlgebra A]

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] predualNormedGroup predualNormedSpace

def contractionNet (hDense : ContractionStrongDense A) (T : algebra A) (hT : ‖T‖ ≤ 1) :
    Finset (Hilbert A) × ℕ → A :=
  Classical.choose (exists_strong_contraction_net A hDense T hT)

theorem contractionNet_norm (hDense : ContractionStrongDense A) (T : algebra A)
    (hT : ‖T‖ ≤ 1) (i : Finset (Hilbert A) × ℕ) :
    ‖contractionNet A hDense T hT i‖ ≤ 1 :=
  (Classical.choose_spec (exists_strong_contraction_net A hDense T hT)).1 i

theorem contractionNet_tendsto (hDense : ContractionStrongDense A) (T : algebra A)
    (hT : ‖T‖ ≤ 1) (η : Hilbert A) :
    Tendsto (fun i => (inclusion A (contractionNet A hDense T hT i) :
      Hilbert A →L[ℂ] Hilbert A) η) atTop (nhds ((T : Hilbert A →L[ℂ] Hilbert A) η)) :=
  (Classical.choose_spec (exists_strong_contraction_net A hDense T hT)).2 η

theorem restriction_norm_eq_of_density (hDense : ContractionStrongDense A)
    (Φ : predual A) : ‖restriction A Φ‖ = ‖Φ‖ := by
  classical
  apply le_antisymm (restriction_norm_le A Φ)
  rw [← predual_norm_coe A Φ]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
  intro T hT
  let a := contractionNet A hDense T hT.le
  have ha (i : Finset (Hilbert A) × ℕ) : ‖a i‖ ≤ 1 :=
    contractionNet_norm A hDense T hT.le i
  have hbound : ∀ i, ‖inclusion A (a i)‖ ≤ 1 := by
    intro i
    rw [inclusion_norm A (a i)]
    exact ha i
  have ht := CoefficientPredual.coefficientPredual_tendsto_of_strong
    (algebra A) 1 hbound hT.le (contractionNet_tendsto A hDense T hT.le) Φ
  apply le_of_tendsto ht.norm
  exact Filter.Eventually.of_forall (fun i => by
    calc
      ‖(Φ : StrongDual ℂ (algebra A)) (inclusion A (a i))‖ =
          ‖restriction A Φ (a i)‖ := rfl
      _ ≤ ‖restriction A Φ‖ * ‖a i‖ := (restriction A Φ).le_opNorm _
      _ ≤ ‖restriction A Φ‖ * 1 :=
        mul_le_mul_of_nonneg_left (ha i) (norm_nonneg _)
      _ = ‖restriction A Φ‖ := mul_one _)

end SpectralIsometry.BidualFoundation.UniversalWeakClosure

