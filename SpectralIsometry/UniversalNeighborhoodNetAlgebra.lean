module
public import SpectralIsometry.GenericBoundedNetLifts
public import SpectralIsometry.BoundedNeighborhoodReindex
public import SpectralIsometry.UniversalApproximation
public import SpectralIsometry.UniversalSquareZeroExtension

/-!
# Universal Neighborhood Net Algebra

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction

namespace SpectralIsometry.UniversalNeighborhoodNetAlgebra
open BidualFoundation UniversalWeakClosure CoefficientPredual StrongStarApproximation

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] predualNormedGroup predualNormedSpace orderedA starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder

universe u
variable (A : Type u) [CStarAlgebra A]

abbrev Index := BoundedNeighborhoodReindex.Index (algebra A)
local instance indexTopology : TopologicalSpace (Index A) := ⊥
local instance indexDiscrete : DiscreteTopology (Index A) := ⟨rfl⟩
local instance indexNeBot : (atTop : Filter (Index A)).NeBot :=
  BoundedNeighborhoodReindex.index_atTop_neBot (algebra A)

theorem inclusion_contractive (a : A) : ‖inclusion A a‖≤‖a‖ :=
  (inclusion_norm A a).le

def netSubalgebra : StarSubalgebra ℂ (((Index A) →ᵇ A) × algebra A) :=
  BoundedStrongStarNetGraph.graph (algebra A) (inclusion A)
    (inclusion_contractive A) (atTop : Filter (Index A))

abbrev NetAlgebra := ↥(netSubalgebra A)

instance netAlgebraCStar : CStarAlgebra (NetAlgebra A) :=
  BoundedStrongStarNetGraph.graphCStarAlgebra (algebra A) (inclusion A)
    (inclusion_contractive A) (atTop : Filter (Index A))

def limitMap : NetAlgebra A →⋆ₐ[ℂ] algebra A :=
  BoundedStrongStarNetGraph.limitHom (algebra A) (inclusion A)
    (inclusion_contractive A) (atTop : Filter (Index A))

def firstMap : NetAlgebra A →⋆ₐ[ℂ] ((Index A) →ᵇ A) :=
  BoundedStrongStarNetGraph.firstHom (algebra A) (inclusion A)
    (inclusion_contractive A) (atTop : Filter (Index A))

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

theorem exists_bounded_original_neighborhood_net (b : algebra A) :
    ∃ a : Index A → A, (∀ U, ‖a U‖≤‖b‖) ∧
      StrongStarTendsto (fun U => (inclusion A (a U):Hilbert A →L[ℂ] Hilbert A))
        atTop (b:Hilbert A →L[ℂ] Hilbert A) := by
  obtain ⟨a,haN,haT⟩ := UniversalApproximation.exists_bounded_net A b
  letI : (atTop : Filter (UniversalApproximation.Index A)).NeBot :=
    UniversalApproximation.index_neBot A
  obtain ⟨a',hN,_hP,hT⟩ := BoundedNeighborhoodReindex.exists_reindex
    (algebra A) (inclusion A) (inclusion_contractive A) a b ‖b‖ haN haT
    (fun _ : A => True) (fun _ => trivial)
  exact ⟨a',hN,hT⟩

theorem exists_squareZero_original_neighborhood_net (b : algebra A) (hb : b^2=0) :
    ∃ a : Index A → A, (∀ U, (a U)^2=0) ∧ (∀ U, ‖a U‖≤‖b‖) ∧
      StrongStarTendsto (fun U => (inclusion A (a U):Hilbert A →L[ℂ] Hilbert A))
        atTop (b:Hilbert A →L[ℂ] Hilbert A) := by
  obtain ⟨a,ha2,haN,haT⟩ := UniversalSquareZeroExtension.exists_original_squareZero_net b hb
  letI : (atTop : Filter (NilIndex (Hilbert A))).NeBot := nilIndex_filter_neBot
  obtain ⟨a',hN,hP,hT⟩ := BoundedNeighborhoodReindex.exists_reindex
    (algebra A) (inclusion A) (inclusion_contractive A) a b ‖b‖ haN haT
    (fun x : A => x^2=0) ha2
  exact ⟨a',hP,hN,hT⟩

theorem limitMap_surjective : Function.Surjective (limitMap A) :=
  BoundedStrongStarNetGraph.limitHom_surjective_of_approximants
    (algebra A) (inclusion A) (inclusion_contractive A)
    (atTop : Filter (Index A)) (exists_bounded_original_neighborhood_net A)

theorem firstMap_isometry : Isometry (firstMap A) :=
  BoundedStrongStarNetGraph.firstHom_isometry
    (algebra A) (inclusion A) (inclusion_contractive A) (atTop : Filter (Index A))

theorem squareZero_lift (b : algebra A) (hb : b^2=0) :
    ∃ p : NetAlgebra A, p^2=0 ∧ ‖p‖≤‖b‖ ∧ limitMap A p=b := by
  obtain ⟨a,ha2,haN,haT⟩ := exists_squareZero_original_neighborhood_net A b hb
  exact BoundedStrongStarNetGraph.squareZero_lift_of_approximants
    (algebra A) (inclusion A) (inclusion_contractive A)
    (atTop : Filter (Index A)) b hb a ha2 haN haT

theorem squareZero_contraction_lift (b : algebra A) (hb : b^2=0) (hbN : ‖b‖≤1) :
    ∃ p : NetAlgebra A, p^2=0 ∧ ‖p‖≤1 ∧ limitMap A p=b := by
  obtain ⟨p,hp2,hpN,hp⟩ := squareZero_lift A b hb
  exact ⟨p,hp2,hpN.trans hbN,hp⟩

theorem contraction_approximants_from_lift (b : algebra A) (hb : b^2=0) (hbN : ‖b‖≤1) :
    ∃ a : Index A → A, (∀ U, (a U)^2=0) ∧ (∀ U, ‖a U‖≤1) ∧
      StrongStarTendsto (fun U => (inclusion A (a U):Hilbert A →L[ℂ] Hilbert A))
        atTop (b:Hilbert A →L[ℂ] Hilbert A) := by
  obtain ⟨p,hp2,hpN,hp⟩ := squareZero_contraction_lift A b hb hbN
  let a : Index A → A := fun U => firstMap A p U
  have hfirst : (firstMap A p)^2=0 := by
    simpa only [map_pow,map_zero] using congrArg (firstMap A) hp2
  have hN : ‖firstMap A p‖=‖p‖ :=
    (BoundedStrongStarNetGraph.graph_norm (algebra A) (inclusion A)
      (inclusion_contractive A) (atTop : Filter (Index A)) p).symm
  refine ⟨a,fun U => congrArg (fun f : (Index A) →ᵇ A => f U) hfirst,
    fun U => ((firstMap A p).norm_coe_le_norm U).trans (hN.le.trans hpN),?_⟩
  have ht := p.property
  change StrongStarTendsto (fun U => (inclusion A (a U):Hilbert A →L[ℂ] Hilbert A))
    atTop (limitMap A p:Hilbert A →L[ℂ] Hilbert A) at ht
  simpa only [hp] using ht

end SpectralIsometry.UniversalNeighborhoodNetAlgebra

