module

public import SpectralIsometry.StrongStarApproximation
public import SpectralIsometry.MatrixKaplansky
import Mathlib.Tactic.Positivity

/-!
# Kaplansky Nets

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open Filter Topology

namespace SpectralIsometry.StrongStarApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ProbeIndex (H : Type*) := Finset H × ℕ

def precision (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem probeIndex_filter_neBot : (atTop : Filter (ProbeIndex H)).NeBot := by
  classical
  infer_instance

theorem strongTendsto_of_probe_errors (a : ProbeIndex H → Op (H := H)) (b : Op (H := H))
    (h : ∀ i : ProbeIndex H, ∀ x ∈ i.1, ‖a i x - b x‖ < precision i.2) :
    StrongTendsto a atTop b := by
  classical
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hfrac : Tendsto precision atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hfrac.eventually (gt_mem_nhds hε))
  refine eventually_atTop.mpr ⟨({x}, N), ?_⟩
  intro i hi
  have hx : x ∈ i.1 := hi.1 (Finset.mem_singleton_self x)
  simpa only [dist_eq_norm] using (h i x hx).trans (hN i.2 hi.2)

/-- A bounded selfadjoint strong-star net, with no CFC-continuity premise. -/
theorem exists_selfAdjoint_contraction_net (S : StarSubalgebra ℂ (Op (H := H)))
    (hS : IsClosed (S : Set (Op (H := H)))) (b : Op (H := H))
    (hb : b ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))))
    (hsa : IsSelfAdjoint b) (hnb : ‖b‖ ≤ 1) :
    ∃ a : ProbeIndex H → Op (H := H),
      (∀ i, a i ∈ S) ∧ (∀ i, IsSelfAdjoint (a i)) ∧ (∀ i, ‖a i‖ ≤ 1) ∧
      StrongStarTendsto a atTop b := by
  classical
  have hex (i : ProbeIndex H) : ∃ a : Op (H := H), a ∈ S ∧ IsSelfAdjoint a ∧
      ‖a‖ ≤ 1 ∧ ∀ x ∈ i.1, ‖a x - b x‖ < precision i.2 := by
    obtain ⟨a, ha, hsa', hna, happ⟩ :=
      OAI.Kadison.Kaplansky.selfAdjoint_contraction_finite_approx (↥(i.1)) S hS hb hsa hnb
        (fun x : i.1 => (x : H)) (precision i.2) (by unfold precision; positivity)
    exact ⟨a, ha, hsa', hna, fun x hx => happ ⟨x, hx⟩⟩
  let a : ProbeIndex H → Op (H := H) := fun i => Classical.choose (hex i)
  have hspec (i : ProbeIndex H) := Classical.choose_spec (hex i)
  have hmem (i : ProbeIndex H) : a i ∈ S := (hspec i).1
  have hsa' (i : ProbeIndex H) : IsSelfAdjoint (a i) := (hspec i).2.1
  have hn (i : ProbeIndex H) : ‖a i‖ ≤ 1 := (hspec i).2.2.1
  have herr (i : ProbeIndex H) : ∀ x ∈ i.1, ‖a i x - b x‖ < precision i.2 :=
    (hspec i).2.2.2
  have hs : StrongTendsto a atTop b := strongTendsto_of_probe_errors a b herr
  refine ⟨a, hmem, hsa', hn, hs, ?_⟩
  have he : (fun i => star (a i)) = a := funext fun i => (hsa' i).star_eq
  rw [he, hsa.star_eq]
  exact hs

/-- The full contraction net is derived from the checked matrix density result. -/
theorem exists_contraction_strongStar_net (S : StarSubalgebra ℂ (Op (H := H)))
    (hS : IsClosed (S : Set (Op (H := H)))) (b : Op (H := H))
    (hb : b ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))))
    (hnb : ‖b‖ ≤ 1) :
    ∃ a : ProbeIndex H → Op (H := H),
      (∀ i, a i ∈ S) ∧ (∀ i, ‖a i‖ ≤ 1) ∧ StrongStarTendsto a atTop b := by
  classical
  letI : IsClosed (S : Set (Op (H := H))) := hS
  have hex (i : ProbeIndex H) : ∃ a : Op (H := H), a ∈ S ∧ ‖a‖ ≤ 1 ∧
      ∀ x ∈ i.1, ‖a x - b x‖ < precision i.2 ∧
        ‖star a x - star b x‖ < precision i.2 := by
    obtain ⟨a, ha, hna, happ⟩ :=
      SpectralIsometry.MatrixKaplansky.contraction_strongStar_finite_approx S (↥(i.1)) hb hnb
        (fun x : i.1 => (x : H)) (precision i.2) (by unfold precision; positivity)
    exact ⟨a, ha, hna, fun x hx => happ ⟨x, hx⟩⟩
  let a : ProbeIndex H → Op (H := H) := fun i => Classical.choose (hex i)
  have hspec (i : ProbeIndex H) := Classical.choose_spec (hex i)
  have hmem (i : ProbeIndex H) : a i ∈ S := (hspec i).1
  have hn (i : ProbeIndex H) : ‖a i‖ ≤ 1 := (hspec i).2.1
  have herr (i : ProbeIndex H) : ∀ x ∈ i.1, ‖a i x - b x‖ < precision i.2 :=
    fun x hx => ((hspec i).2.2 x hx).1
  have herrStar (i : ProbeIndex H) :
      ∀ x ∈ i.1, ‖star (a i) x - star b x‖ < precision i.2 :=
    fun x hx => ((hspec i).2.2 x hx).2
  exact ⟨a, hmem, hn, strongTendsto_of_probe_errors a b herr,
    strongTendsto_of_probe_errors (fun i => star (a i)) (star b) herrStar⟩

end SpectralIsometry.StrongStarApproximation

