module

public import SpectralIsometry.StrongStarApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Strong StarCFC

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open Filter Topology
open scoped CStarAlgebra ContinuousFunctionalCalculus

namespace SpectralIsometry.StrongStarApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem strongStarTendsto_add {ι : Type*} {l : Filter ι}
    {a b : ι → Op (H := H)} {a' b' : Op (H := H)}
    (ha : StrongStarTendsto a l a') (hb : StrongStarTendsto b l b') :
    StrongStarTendsto (fun i => a i + b i) l (a' + b') := by
  constructor
  · intro x
    simpa only [ContinuousLinearMap.add_apply] using (ha.1 x).add (hb.1 x)
  · intro x
    simpa only [star_add, ContinuousLinearMap.add_apply] using (ha.2 x).add (hb.2 x)

theorem strongTendsto_of_uniform_approx {ι : Type*} {l : Filter ι}
    {a : ι → Op (H := H)} {a' : Op (H := H)}
    (h : ∀ δ : ℝ, 0 < δ → ∃ b : ι → Op (H := H), ∃ b' : Op (H := H),
      StrongTendsto b l b' ∧ (∀ i, ‖a i - b i‖ ≤ δ) ∧ ‖a' - b'‖ ≤ δ) :
    StrongTendsto a l a' := by
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (3 * (‖x‖ + 1))
  have hden : 0 < 3 * (‖x‖ + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : δ * (3 * (‖x‖ + 1)) = ε := by
    dsimp only [δ]
    exact div_mul_cancel₀ ε hden.ne'
  have hδx : δ * ‖x‖ < ε / 3 := by nlinarith
  obtain ⟨b, b', hb, hib, hb'⟩ := h δ hδ
  filter_upwards [Metric.tendsto_nhds.mp (hb x) (ε / 3) (by positivity)] with i hi
  have hm : ‖b i x - b' x‖ < ε / 3 := by simpa only [dist_eq_norm] using hi
  have hfirst : ‖(a i - b i) x‖ ≤ δ * ‖x‖ :=
    ((a i - b i).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hib i) (norm_nonneg x))
  have hlast : ‖(b' - a') x‖ ≤ δ * ‖x‖ := by
    calc
      ‖(b' - a') x‖ ≤ ‖b' - a'‖ * ‖x‖ := (b' - a').le_opNorm x
      _ = ‖a' - b'‖ * ‖x‖ := by rw [norm_sub_rev]
      _ ≤ δ * ‖x‖ := mul_le_mul_of_nonneg_right hb' (norm_nonneg x)
  have he : a i x - a' x = (a i - b i) x + (b i x - b' x) + (b' - a') x := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  rw [dist_eq_norm, he]
  calc
    ‖(a i - b i) x + (b i x - b' x) + (b' - a') x‖ ≤
        (‖(a i - b i) x‖ + ‖b i x - b' x‖) + ‖(b' - a') x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < ε := by linarith

theorem strongStarTendsto_of_uniform_approx {ι : Type*} {l : Filter ι}
    {a : ι → Op (H := H)} {a' : Op (H := H)}
    (h : ∀ δ : ℝ, 0 < δ → ∃ b : ι → Op (H := H), ∃ b' : Op (H := H),
      StrongStarTendsto b l b' ∧ (∀ i, ‖a i - b i‖ ≤ δ) ∧ ‖a' - b'‖ ≤ δ) :
    StrongStarTendsto a l a' := by
  constructor
  · apply strongTendsto_of_uniform_approx
    intro δ hδ
    obtain ⟨b, b', hb, hib, hb'⟩ := h δ hδ
    exact ⟨b, b', hb.1, hib, hb'⟩
  · apply strongTendsto_of_uniform_approx
    intro δ hδ
    obtain ⟨b, b', hb, hib, hb'⟩ := h δ hδ
    refine ⟨fun i => star (b i), star b', hb.2, ?_, ?_⟩
    · intro i
      simpa only [← star_sub, norm_star] using hib i
    · simpa only [← star_sub, norm_star] using hb'

theorem norm_cfcHomSuperset_le {s : Set ℝ} [CompactSpace s]
    (a : Op (H := H)) (ha : IsSelfAdjoint a) (hs : spectrum ℝ a ⊆ s) (f : C(s, ℝ)) :
    ‖cfcHomSuperset ha hs f‖ ≤ ‖f‖ := by
  rw [cfcHomSuperset_apply]
  rw [isometry_cfcHom (R := ℝ) a ha |>.norm_map_of_map_zero (map_zero (cfcHom ha))]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact ContinuousMap.norm_coe_le_norm f ⟨x, hs x.property⟩

/-- Common-compact-spectrum CFC continuity follows from the checked bounded
multiplication and uniform polynomial approximation, with no extra premise. -/
theorem strongStarTendsto_cfcHomSuperset {ι : Type*} {l : Filter ι}
    {s : Set ℝ} (hs : IsCompact s) (a : ι → Op (H := H)) (b : Op (H := H))
    (ha : ∀ i, IsSelfAdjoint (a i)) (hb : IsSelfAdjoint b)
    (has : ∀ i, spectrum ℝ (a i) ⊆ s) (hbs : spectrum ℝ b ⊆ s)
    (hab : StrongStarTendsto a l b) (f : C(s, ℝ)) :
    StrongStarTendsto (fun i => cfcHomSuperset (ha i) (has i) f) l
      (cfcHomSuperset hb hbs f) := by
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have he : ContinuousMap.const s r = algebraMap ℝ C(s, ℝ) r := rfl
    simpa only [he, AlgHomClass.commutes] using
      strongStarTendsto_const l (algebraMap ℝ (Op (H := H)) r)
  | id => simpa only [cfcHomSuperset_id] using hab
  | star_id =>
    simpa only [map_star, cfcHomSuperset_id] using strongStarTendsto_star hab
  | add f g hf hg => simpa only [map_add] using strongStarTendsto_add hf hg
  | mul f g hf hg =>
    have hC : ∀ᶠ i in l, ‖cfcHomSuperset (ha i) (has i) f‖ ≤ ‖f‖ :=
      Eventually.of_forall fun i => norm_cfcHomSuperset_le (a i) (ha i) (has i) f
    have hD : ∀ᶠ i in l, ‖cfcHomSuperset (ha i) (has i) g‖ ≤ ‖g‖ :=
      Eventually.of_forall fun i => norm_cfcHomSuperset_le (a i) (ha i) (has i) g
    simpa only [map_mul] using strongStarTendsto_mul_of_norm_bounds hf hg hC hD
  | frequently f hf =>
    apply strongStarTendsto_of_uniform_approx
    intro δ hδ
    obtain ⟨g, hg, hgP⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hδ)
    have hfg : ‖f - g‖ ≤ δ := by
      simpa only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] using hg
    refine ⟨fun i => cfcHomSuperset (ha i) (has i) g, cfcHomSuperset hb hbs g,
      hgP, ?_, ?_⟩
    · intro i
      rw [← map_sub]
      exact (norm_cfcHomSuperset_le (a i) (ha i) (has i) (f - g)).trans hfg
    · rw [← map_sub]
      exact (norm_cfcHomSuperset_le b hb hbs (f - g)).trans hfg

end SpectralIsometry.StrongStarApproximation

