module

public import SpectralIsometry.UnitCopySequence
public import OAI.Analysis.BoundedHochschild.OrthogonalProjectionSums

/-!
# Unit Copy Tails

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open Filter Topology
open scoped BigOperators ComplexOrder CStarAlgebra
open OAI.HochschildComparison OAI.BoundedHochschild OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.SquareZeroPreserver

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_orthogonal_unitCopy_tails (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (v w : M) (hv : star v * v = 1) (hw : star w * w = 1) (hvw : star v * w = 0) :
    ∃ (c : ℕ → PartialIso M) (r : ℕ → M),
      (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      (∀ n, IsStarProjection (r n) ∧ (c n).final ≤ r n ∧ (c (n+1)).final ≤ r n) ∧
      PredualTendsto e r atTop 0 := by
  obtain ⟨c,hci,horth⟩ := exists_orthogonal_unitCopy_sequence v w hv hw hvw
  let S (n : ℕ) : M := ∑ i ∈ Finset.range n, (c i).final
  have hS (n : ℕ) : IsStarProjection (S n) :=
    orthogonal_projection_finset_sum (fun i => (c i).final)
      (fun i => (c i).final_proj) horth (Finset.range n)
  have hSm : Monotone S := by
    intro n m hnm
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
      (fun i _ _ => (c i).final_proj.nonneg)
  obtain ⟨P,hP,hLUB,hconv⟩ := exists_increasing_projection_limit e S hS hSm
  have hSP (n : ℕ) : S n ≤ P := hLUB.1 (Set.mem_range_self n)
  have hPiP (i : ℕ) : (c i).final ≤ P := by
    apply le_trans ?_ (hSP (i+1))
    exact Finset.single_le_sum (fun j _ => (c j).final_proj.nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self i))
  let r (n : ℕ) : M := P - S n
  have hr (n : ℕ) : IsStarProjection (r n) := ((hS n).le_iff_sub hP).mp (hSP n)
  have htail (n i : ℕ) (hni : n ≤ i) : (c i).final ≤ r n := by
    have hzero : (c i).final * S n = 0 := by
      dsimp only [S]
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i j ((lt_of_lt_of_le (Finset.mem_range.mp hj) hni).ne')
    apply ((c i).final_proj.le_iff_mul_eq_left (hr n)).mpr
    change (c i).final * (P - S n) = (c i).final
    rw [mul_sub,((c i).final_proj.le_iff_mul_eq_left hP).mp (hPiP i),hzero,sub_zero]
  have hrlim : PredualTendsto e r atTop 0 := by
    have hh := predual_tendsto_sub e (predual_tendsto_const e P atTop) hconv
    simpa only [sub_self] using hh
  exact ⟨c,r,hci,horth,fun n => ⟨hr n,htail n n le_rfl,htail n (n+1) (Nat.le_succ n)⟩,hrlim⟩

end SpectralIsometry.SquareZeroPreserver

