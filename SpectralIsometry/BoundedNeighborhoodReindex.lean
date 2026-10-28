module
public import SpectralIsometry.ConcreteNormalSeminormConvergence
public import SpectralIsometry.GenericNeighborhoodReindex

/-!
# Bounded Neighborhood Reindex

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace SpectralIsometry.BoundedNeighborhoodReindex
open BidualFoundation.CoefficientPredual StrongStarApproximation
attribute [local instance] complexNormedSpaceSelf coefficientNormedGroup coefficientNormedSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Index (M : VonNeumannAlgebra H) :=
  NeighborhoodReindex.Index M
    (NormalSeminorm.strongStarTopology (concretePredualIsometry M)) (0:M)

theorem index_atTop_neBot (M : VonNeumannAlgebra H) :
    (atTop : Filter (Index M)).NeBot :=
  NeighborhoodReindex.index_atTop_neBot M _ 0

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem exists_reindex (M : VonNeumannAlgebra H) {A I : Type*} [CStarAlgebra A]
    (j : A →⋆ₐ[ℂ] M) (hnorm : ∀ x : A, ‖j x‖≤‖x‖)
    {l : Filter I} [l.NeBot] (a : I → A) (b : M) (C : ℝ)
    (hbound : ∀ i, ‖a i‖≤C)
    (ha : StrongStarTendsto (fun i => (j (a i):H →L[ℂ] H)) l (b:H →L[ℂ] H))
    (P : A → Prop) (hP : ∀ i, P (a i)) :
    ∃ a' : Index M → A, (∀ U, ‖a' U‖≤C) ∧ (∀ U, P (a' U)) ∧
      StrongStarTendsto (fun U => (j (a' U):H →L[ℂ] H)) atTop (b:H →L[ℂ] H) := by
  let e := concretePredualIsometry M
  have ht : Tendsto (fun i => j (a i)) l (@nhds M (NormalSeminorm.strongStarTopology e) b) :=
    (ConcreteNormalSeminorm.bounded_topology_iff_strongStar M _ b C
      (fun i => (hnorm (a i)).trans (hbound i))).mpr ha
  have hs := (NormalSeminorm.tendsto_topology_iff e _ l b).mp ht
  have hd : NormalSeminorm.SeminormTendsto e (fun i => j (a i)-b) l 0 := by
    intro ψ φ heq hn
    simpa only [sub_zero] using hs ψ φ heq hn
  have hdt : Tendsto (fun i => j (a i)-b) l (@nhds M (NormalSeminorm.strongStarTopology e) 0) :=
    (NormalSeminorm.tendsto_topology_iff e _ l 0).mpr hd
  obtain ⟨a',hpoint,hconv⟩ := NeighborhoodReindex.exists_reindex
    (NormalSeminorm.strongStarTopology e) (0:M) (fun x : A => j x-b) a hdt
    (fun x : A => ‖x‖≤C ∧ P x) (fun i => ⟨hbound i,hP i⟩)
  have hs' := (NormalSeminorm.tendsto_topology_iff e _ atTop 0).mp hconv
  have hd' : NormalSeminorm.SeminormTendsto e (fun U => j (a' U)) atTop b := by
    intro ψ φ heq hn
    simpa only [sub_zero] using hs' ψ φ heq hn
  have hn' := (NormalSeminorm.seminormTendsto_iff e _ atTop b).mp hd'
  exact ⟨a',fun U => (hpoint U).1,fun U => (hpoint U).2,
    ConcreteNormalSeminorm.normalPositive_to_strongStar M _ b hn'⟩

end SpectralIsometry.BoundedNeighborhoodReindex

