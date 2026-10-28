module

public import SpectralIsometry.BidualFoundation
public import SpectralIsometry.MatrixKaplansky
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Bidual Density

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

def ContractionStrongDense : Prop :=
  ∀ (T : algebra A), ‖T‖ ≤ 1 → ∀ (s : Finset (Hilbert A)) (ε : ℝ), 0 < ε →
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ η ∈ s,
      ‖(inclusion A a : Hilbert A →L[ℂ] Hilbert A) η -
        (T : Hilbert A →L[ℂ] Hilbert A) η‖ < ε

-- This elaboration option permits unfolding the imported non-exposed adjoint
-- while reconciling two inherited presentations of the same star operation.
-- The resulting declaration is still checked by the kernel.
set_option backward.isDefEq.respectTransparency.types false in
theorem representationRange_isClosed :
    IsClosed (Set.range (universalGNSRepresentation (M := A))) := by
  have hi : Isometry (universalGNSRepresentation (M := A)) :=
    AddMonoidHomClass.isometry_of_norm (universalGNSRepresentation (M := A))
      (fun a : A => universalGNSRepresentation_norm (M := A) a)
  exact hi.isClosedEmbedding.isClosed_range

/- This is an actual proof adapter, not an assumed density axiom. It may only be
inserted/checked after importing a successfully exported SpectralIsometry.MatrixKaplansky. -/

set_option backward.isDefEq.respectTransparency.types false in
theorem contractionStrongDense : ContractionStrongDense A := by
  classical
  let S : StarSubalgebra ℂ (Hilbert A →L[ℂ] Hilbert A) :=
    (universalGNSRepresentation (M := A)).range
  letI : IsClosed (S : Set (Hilbert A →L[ℂ] Hilbert A)) := by
    change IsClosed (Set.range (universalGNSRepresentation (M := A)))
    exact representationRange_isClosed A
  intro T hT s ε hε
  have hT' : (T : Hilbert A →L[ℂ] Hilbert A) ∈
      Set.centralizer (Set.centralizer (S : Set (Hilbert A →L[ℂ] Hilbert A))) := by
    have ht : (T : Hilbert A →L[ℂ] Hilbert A) ∈
        (weakClosure S : Set (Hilbert A →L[ℂ] Hilbert A)) := T.property
    rwa [weakClosure_coe S] at ht
  obtain ⟨a, ha, hna, happ⟩ :=
    SpectralIsometry.MatrixKaplansky.contraction_finite_approx S (↥s) hT' hT
      (fun ξ => ξ.val) ε hε
  obtain ⟨b, rfl⟩ := ha
  refine ⟨b, ?_, ?_⟩
  · calc
      ‖b‖ = ‖inclusion A b‖ := (inclusion_norm A b).symm
      _ = ‖(universalGNSRepresentation (M := A)) b‖ := rfl
      _ ≤ 1 := hna
  · intro η hη
    exact happ ⟨η, hη⟩

theorem exists_strong_contraction_net (hDense : ContractionStrongDense A)
    (T : algebra A) (hT : ‖T‖ ≤ 1) :
    ∃ a : Finset (Hilbert A) × ℕ → A, (∀ i, ‖a i‖ ≤ 1) ∧
      ∀ η : Hilbert A,
        Filter.Tendsto (fun i => (inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A) η)
          Filter.atTop (nhds ((T : Hilbert A →L[ℂ] Hilbert A) η)) := by
  classical
  choose a ha htest using (fun i : Finset (Hilbert A) × ℕ =>
    hDense T hT i.1 (1 / ((i.2 : ℝ) + 1)) (by positivity))
  refine ⟨a, ha, ?_⟩
  intro η
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hε)
  apply Filter.eventually_atTop.mpr
  refine ⟨({η}, N), ?_⟩
  intro i hi
  rw [dist_eq_norm]
  exact (htest i η (hi.1 (by simp))).trans (hN i.2 hi.2)

end SpectralIsometry.BidualFoundation.UniversalWeakClosure

