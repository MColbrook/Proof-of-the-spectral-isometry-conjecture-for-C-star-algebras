module

public import SpectralIsometry.KaplanskyNets
public import SpectralIsometry.NilpotentSupports
public import SpectralIsometry.StrongStarCuts
import Mathlib.Tactic.NoncommRing

/-!
# Nilpotent Approximation

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open Filter Topology
open scoped CStarAlgebra

namespace SpectralIsometry.StrongStarApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev NilIndex (H : Type*) := ProbeIndex H × ProbeIndex H

private theorem norm_mul_le_one (a b : Op (H := H)) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ 1 := by
  calc
    ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg b) zero_le_one
    _ = 1 := one_mul _

private theorem strongStarTendsto_comp {ι κ : Type*} {l : Filter ι} {k : Filter κ}
    {a : ι → Op (H := H)} {b : Op (H := H)} (ha : StrongStarTendsto a l b)
    (φ : κ → ι) (hφ : Tendsto φ k l) : StrongStarTendsto (fun j => a (φ j)) k b :=
  ⟨fun x => (ha.1 x).comp hφ, fun x => (ha.2 x).comp hφ⟩

private theorem fst_tendsto_probe :
    Tendsto (Prod.fst : NilIndex H → ProbeIndex H) atTop atTop := by
  classical
  apply tendsto_atTop.mpr
  intro i
  exact eventually_atTop.mpr ⟨(i, (∅, 0)), fun j hj => hj.1⟩

private theorem snd_tendsto_probe :
    Tendsto (Prod.snd : NilIndex H → ProbeIndex H) atTop atTop := by
  classical
  apply tendsto_atTop.mpr
  intro i
  exact eventually_atTop.mpr ⟨((∅, 0), i), fun j hj => hj.2⟩

theorem nilIndex_filter_neBot : (atTop : Filter (NilIndex H)).NeBot := by
  classical
  infer_instance

/-- Square-zero contractions are strong-star approximated by square-zero
contractions in the original norm-closed unital star subalgebra. -/
theorem exists_squareZero_contraction_net (S : StarSubalgebra ℂ (Op (H := H)))
    (hS : IsClosed (S : Set (Op (H := H)))) (n : Op (H := H))
    (hn : n ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))))
    (h2 : n ^ 2 = 0) (hnorm : ‖n‖ ≤ 1) :
    ∃ w : NilIndex H → Op (H := H), (∀ i, w i ∈ S) ∧
      (∀ i, w i ^ 2 = 0) ∧ (∀ i, ‖w i‖ ≤ 1) ∧ StrongStarTendsto w atTop n := by
  obtain ⟨e, f, he, hf, heM, hfM, hef, hfe, henf, hsa, hnb, hpos, hneg⟩ :=
    nilpotent_support_projections S n hn h2
  have hdiff : e - f ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))) := by
    intro r hr
    rw [mul_sub, sub_mul, heM r hr, hfM r hr]
  obtain ⟨a, haS, haSA, haN, haT⟩ :=
    exists_selfAdjoint_contraction_net S hS (e - f) hdiff hsa hnb
  obtain ⟨b, hbS, hbN, hbT⟩ := exists_contraction_strongStar_net S hS n hn hnorm
  have hap : StrongStarTendsto (fun i => (a i)⁺) atTop e := by
    simpa only [hpos] using strongStarTendsto_posPart a (e - f) 1 haSA hsa haN hnb haT
  have han : StrongStarTendsto (fun i => (a i)⁻) atTop f := by
    simpa only [hneg] using strongStarTendsto_negPart a (e - f) 1 haSA hsa haN hnb haT
  let E : NilIndex H → Op (H := H) := fun i => (a i.1)⁺
  let F : NilIndex H → Op (H := H) := fun i => (a i.1)⁻
  let Y : NilIndex H → Op (H := H) := fun i => b i.2
  let w : NilIndex H → Op (H := H) := fun i => E i * Y i * F i
  have hET : StrongStarTendsto E atTop e := strongStarTendsto_comp hap Prod.fst fst_tendsto_probe
  have hFT : StrongStarTendsto F atTop f := strongStarTendsto_comp han Prod.fst fst_tendsto_probe
  have hYT : StrongStarTendsto Y atTop n := strongStarTendsto_comp hbT Prod.snd snd_tendsto_probe
  have hEN (i : NilIndex H) : ‖E i‖ ≤ 1 :=
    (CStarAlgebra.norm_posPart_le (a i.1)).trans (haN i.1)
  have hFN (i : NilIndex H) : ‖F i‖ ≤ 1 :=
    (CStarAlgebra.norm_negPart_le (a i.1)).trans (haN i.1)
  have hYN (i : NilIndex H) : ‖Y i‖ ≤ 1 := hbN i.2
  have hP : StrongStarTendsto (fun i => E i * Y i) atTop (e * n) :=
    strongStarTendsto_mul_of_norm_bounds hET hYT
      (Eventually.of_forall hEN) (Eventually.of_forall hYN)
  have hPN (i : NilIndex H) : ‖E i * Y i‖ ≤ 1 := norm_mul_le_one _ _ (hEN i) (hYN i)
  have hwT : StrongStarTendsto w atTop n := by
    simpa only [w, henf] using strongStarTendsto_mul_of_norm_bounds hP hFT
      (Eventually.of_forall hPN) (Eventually.of_forall hFN)
  have hwS (i : NilIndex H) : w i ∈ S :=
    mul_mem (mul_mem (posPart_mem S hS _ (haS i.1)) (hbS i.2))
      (negPart_mem S hS _ (haS i.1))
  have hwN (i : NilIndex H) : ‖w i‖ ≤ 1 := norm_mul_le_one _ _ (hPN i) (hFN i)
  have hw2 (i : NilIndex H) : w i ^ 2 = 0 := by
    have hz : F i * E i = 0 := CFC.negPart_mul_posPart (a i.1)
    dsimp only [w]
    rw [pow_two]
    calc
      (E i * Y i * F i) * (E i * Y i * F i) = E i * Y i * (F i * E i) * Y i * F i := by
        noncomm_ring
      _ = 0 := by simp only [hz, mul_zero, zero_mul]
  exact ⟨w, hwS, hw2, hwN, hwT⟩

private theorem strongStarTendsto_real_smul {ι : Type*} {l : Filter ι}
    {a : ι → Op (H := H)} {b : Op (H := H)} (ha : StrongStarTendsto a l b) (r : ℝ) :
    StrongStarTendsto (fun i => r • a i) l (r • b) := by
  constructor
  · intro x
    simpa only [ContinuousLinearMap.smul_apply] using (ha.1 x).const_smul r
  · intro x
    simpa only [star_smul, star_trivial, ContinuousLinearMap.smul_apply] using
      (ha.2 x).const_smul r

/-- Original arbitrary-norm bounded nilpotent approximation. The normalization
and zero case are internal; norm(n)<=1 is not an extra hypothesis here. -/
theorem exists_bounded_squareZero_net (S : StarSubalgebra ℂ (Op (H := H)))
    (hS : IsClosed (S : Set (Op (H := H)))) (n : Op (H := H))
    (hn : n ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))))
    (h2 : n ^ 2 = 0) :
    ∃ w : NilIndex H → Op (H := H), (∀ i, w i ∈ S) ∧
      (∀ i, w i ^ 2 = 0) ∧ (∀ i, ‖w i‖ ≤ ‖n‖) ∧ StrongStarTendsto w atTop n := by
  by_cases hn0 : n = 0
  · subst n
    exact ⟨fun _ => 0, fun _ => zero_mem S, fun _ => by simp,
      fun _ => by simp, strongStarTendsto_const atTop 0⟩
  let r : ℝ := ‖n‖
  have hr : 0 < r := norm_pos_iff.mpr hn0
  let m : Op (H := H) := r⁻¹ • n
  have hmM : m ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))) := by
    intro a ha
    dsimp only [m]
    rw [mul_smul_comm, smul_mul_assoc, hn a ha]
  have hm2 : m ^ 2 = 0 := by
    dsimp only [m]
    rw [smul_pow, h2, smul_zero]
  have hmN : ‖m‖ ≤ 1 := by
    dsimp only [m]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    change r⁻¹ * r ≤ 1
    rw [inv_mul_cancel₀ hr.ne']
  obtain ⟨a, haS, ha2, haN, haT⟩ := exists_squareZero_contraction_net S hS m hmM hm2 hmN
  let w : NilIndex H → Op (H := H) := fun i => r • a i
  have hwS (i : NilIndex H) : w i ∈ S := by
    simpa only [Complex.coe_smul] using S.smul_mem (haS i) (r : ℂ)
  have hw2 (i : NilIndex H) : w i ^ 2 = 0 := by
    dsimp only [w]
    rw [smul_pow, ha2 i, smul_zero]
  have hwN (i : NilIndex H) : ‖w i‖ ≤ ‖n‖ := by
    dsimp only [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (haN i) hr.le
  have hscale : r • m = n := by
    dsimp only [m]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hwT : StrongStarTendsto w atTop n := by
    simpa only [hscale] using strongStarTendsto_real_smul haT r
  exact ⟨w, hwS, hw2, hwN, hwT⟩

/-- Finite-vector form of the same approximation, with no countability premise. -/
theorem squareZero_strongStar_finite_approx {ι : Type*} [Fintype ι]
    (S : StarSubalgebra ℂ (Op (H := H)))
    (hS : IsClosed (S : Set (Op (H := H)))) (n : Op (H := H))
    (hn : n ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))))
    (h2 : n ^ 2 = 0) (x : ι → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : Op (H := H), w ∈ S ∧ w ^ 2 = 0 ∧ ‖w‖ ≤ ‖n‖ ∧
      ∀ j, ‖w (x j) - n (x j)‖ < ε ∧ ‖star w (x j) - star n (x j)‖ < ε := by
  obtain ⟨w, hwS, hw2, hwN, hwT⟩ := exists_bounded_squareZero_net S hS n hn h2
  have heach (j : ι) : ∀ᶠ i in (atTop : Filter (NilIndex H)),
      ‖w i (x j) - n (x j)‖ < ε ∧ ‖star (w i) (x j) - star n (x j)‖ < ε := by
    have hf := Metric.tendsto_nhds.mp (hwT.1 (x j)) ε hε
    have hs := Metric.tendsto_nhds.mp (hwT.2 (x j)) ε hε
    simpa only [dist_eq_norm] using hf.and hs
  have hall : ∀ᶠ i in (atTop : Filter (NilIndex H)), ∀ j,
      ‖w i (x j) - n (x j)‖ < ε ∧ ‖star (w i) (x j) - star n (x j)‖ < ε :=
    eventually_all.mpr heach
  letI : (atTop : Filter (NilIndex H)).NeBot := nilIndex_filter_neBot
  obtain ⟨i, hi⟩ := hall.exists
  exact ⟨w i, hwS i, hw2 i, hwN i, hi⟩

end SpectralIsometry.StrongStarApproximation

