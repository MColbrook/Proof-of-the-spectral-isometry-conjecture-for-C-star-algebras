module
public import SpectralIsometry.GenericBoundedNetLifts
public import SpectralIsometry.UniversalApproximation
public import SpectralIsometry.UniversalSquareZeroExtension

/-!
# Universal Bounded Net Algebra

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction

namespace SpectralIsometry.UniversalBoundedNetAlgebra
open BidualFoundation UniversalWeakClosure CoefficientPredual StrongStarApproximation

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] predualNormedGroup predualNormedSpace orderedA starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder

universe u
variable (A : Type u) [CStarAlgebra A]

abbrev Index := NilIndex (Hilbert A)
local instance indexTopology : TopologicalSpace (Index A) := ⊥
local instance indexDiscrete : DiscreteTopology (Index A) := ⟨rfl⟩
local instance indexNeBot : (atTop : Filter (Index A)).NeBot := nilIndex_filter_neBot

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

theorem index_fst_tendsto :
    Tendsto (Prod.fst : Index A → ProbeIndex (Hilbert A)) atTop atTop := by
  classical
  apply tendsto_atTop.mpr
  intro i
  exact eventually_atTop.mpr ⟨(i,(∅,0)),fun j hj => hj.1⟩

theorem exists_bounded_original_net (b : algebra A) :
    ∃ a : Index A → A, (∀ i, ‖a i‖≤‖b‖) ∧
      StrongStarTendsto (fun i => (inclusion A (a i):Hilbert A →L[ℂ] Hilbert A))
        atTop (b:Hilbert A →L[ℂ] Hilbert A) := by
  obtain ⟨a,haN,haT⟩ := UniversalApproximation.exists_bounded_net A b
  refine ⟨fun i => a i.1,fun i => haN i.1,?_⟩
  exact ⟨fun ξ => (haT.1 ξ).comp (index_fst_tendsto A),
    fun ξ => (haT.2 ξ).comp (index_fst_tendsto A)⟩

theorem limitMap_surjective : Function.Surjective (limitMap A) :=
  BoundedStrongStarNetGraph.limitHom_surjective_of_approximants
    (algebra A) (inclusion A) (inclusion_contractive A)
    (atTop : Filter (Index A)) (exists_bounded_original_net A)

theorem firstMap_isometry : Isometry (firstMap A) :=
  BoundedStrongStarNetGraph.firstHom_isometry
    (algebra A) (inclusion A) (inclusion_contractive A) (atTop : Filter (Index A))

theorem squareZero_lift (b : algebra A) (hb : b^2=0) :
    ∃ p : NetAlgebra A, p^2=0 ∧ ‖p‖≤‖b‖ ∧ limitMap A p=b := by
  obtain ⟨a,ha2,haN,haT⟩ :=
    UniversalSquareZeroExtension.exists_original_squareZero_net b hb
  exact BoundedStrongStarNetGraph.squareZero_lift_of_approximants
    (algebra A) (inclusion A) (inclusion_contractive A)
    (atTop : Filter (Index A)) b hb a ha2 haN haT

theorem squareZero_contraction_lift (b : algebra A) (hb : b^2=0) (hbN : ‖b‖≤1) :
    ∃ p : NetAlgebra A, p^2=0 ∧ ‖p‖≤1 ∧ limitMap A p=b := by
  obtain ⟨p,hp2,hpN,hp⟩ := squareZero_lift A b hb
  exact ⟨p,hp2,hpN.trans hbN,hp⟩

end SpectralIsometry.UniversalBoundedNetAlgebra

