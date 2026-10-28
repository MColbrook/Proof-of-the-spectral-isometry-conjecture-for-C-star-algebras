module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Strong Star Approximation

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open Filter Topology

namespace SpectralIsometry.StrongStarApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Op := H →L[ℂ] H

/-- Concrete strong convergence, tested on every Hilbert-space vector. -/
def StrongTendsto {ι : Type*} (a : ι → Op (H := H)) (l : Filter ι) (b : Op (H := H)) : Prop :=
  ∀ x : H, Tendsto (fun i => a i x) l (𝓝 (b x))

/-- Strong convergence of operators and their adjoints. -/
def StrongStarTendsto {ι : Type*} (a : ι → Op (H := H)) (l : Filter ι)
    (b : Op (H := H)) : Prop :=
  StrongTendsto a l b ∧ StrongTendsto (fun i => star (a i)) l (star b)

theorem mul_vector_error_le (a b a' b' : Op (H := H)) (x : H) :
    ‖(a * b) x - (a' * b') x‖ ≤
      ‖a‖ * ‖b x - b' x‖ + ‖a (b' x) - a' (b' x)‖ := by
  have he : (a * b) x - (a' * b') x =
      a (b x - b' x) + (a (b' x) - a' (b' x)) := by
    simp only [mul_apply_eq_comp, map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ((a.le_opNorm _)) le_rfl)

/-- The left factor's explicit bound controls the varying input vector. -/
theorem strongTendsto_mul_of_left_norm_bound {ι : Type*} {l : Filter ι}
    {a b : ι → Op (H := H)} {a' b' : Op (H := H)} {C : ℝ}
    (ha : StrongTendsto a l a') (hb : StrongTendsto b l b')
    (hC : ∀ᶠ i in l, ‖a i‖ ≤ C) :
    StrongTendsto (fun i => a i * b i) l (a' * b') := by
  intro x
  have hz : Tendsto (fun i => a i (b i x - b' x)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hlim : Tendsto (fun i => C * ‖b i x - b' x‖) l (𝓝 0) := by
      simpa only [sub_self, norm_zero, mul_zero] using
        (tendsto_const_nhds (x := C)).mul
          ((hb x).sub (tendsto_const_nhds (x := b' x))).norm
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
    filter_upwards [hC] with i hi
    exact ((a i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  simpa only [map_sub, sub_add_cancel, zero_add, mul_apply_eq_comp] using
    hz.add (ha (b' x))

/-- Joint strong-star continuity of multiplication on explicitly bounded nets. -/
theorem strongStarTendsto_mul_of_norm_bounds {ι : Type*} {l : Filter ι}
    {a b : ι → Op (H := H)} {a' b' : Op (H := H)} {C D : ℝ}
    (ha : StrongStarTendsto a l a') (hb : StrongStarTendsto b l b')
    (hC : ∀ᶠ i in l, ‖a i‖ ≤ C) (hD : ∀ᶠ i in l, ‖b i‖ ≤ D) :
    StrongStarTendsto (fun i => a i * b i) l (a' * b') := by
  refine ⟨strongTendsto_mul_of_left_norm_bound ha.1 hb.1 hC, ?_⟩
  have hs : ∀ᶠ i in l, ‖star (b i)‖ ≤ D := by simpa only [norm_star] using hD
  have he := strongTendsto_mul_of_left_norm_bound hb.2 ha.2 hs
  intro x
  simpa only [star_mul] using he x

theorem strongStarTendsto_const {ι : Type*} (l : Filter ι) (a : Op (H := H)) :
    StrongStarTendsto (fun _ : ι => a) l a :=
  ⟨fun _ => tendsto_const_nhds, fun _ => tendsto_const_nhds⟩

theorem strongStarTendsto_star {ι : Type*} {l : Filter ι}
    {a : ι → Op (H := H)} {b : Op (H := H)} (ha : StrongStarTendsto a l b) :
    StrongStarTendsto (fun i => star (a i)) l (star b) := by
  refine ⟨ha.2, ?_⟩
  intro x
  simpa only [star_star] using ha.1 x

end SpectralIsometry.StrongStarApproximation

