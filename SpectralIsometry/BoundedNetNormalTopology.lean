module
public import SpectralIsometry.BoundedStrongStarNetGraph
public import SpectralIsometry.ConcreteNormalSeminormConvergence

/-!
# Bounded Net Normal Topology

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction

namespace SpectralIsometry.BoundedStrongStarNetGraph
open BidualFoundation.CoefficientPredual
attribute [local instance] complexNormedSpaceSelf coefficientNormedGroup coefficientNormedSpace

variable {I A H : Type*} [TopologicalSpace I] [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (j : A →⋆ₐ[ℂ] M)
  (hnorm : ∀ a : A, ‖j a‖≤‖a‖) (l : Filter I)
include hnorm

theorem converges_iff_normalTopology (f : I →ᵇ A) (b : M) :
    Converges M j l (f,b) ↔
      Tendsto (fun i => j (f i)) l
        (@nhds M (NormalSeminorm.strongStarTopology (concretePredualIsometry M)) b) :=
  (ConcreteNormalSeminorm.bounded_topology_iff_strongStar
    M (fun i => j (f i)) b ‖f‖ (pointwise_norm_bound M j hnorm f)).symm

theorem firstHom_range_normalTopology [l.NeBot] :
    Set.range (firstHom M j hnorm l)=
      {f : I →ᵇ A | ∃ b : M, Tendsto (fun i => j (f i)) l
        (@nhds M (NormalSeminorm.strongStarTopology (concretePredualIsometry M)) b)} := by
  rw [firstHom_range M j hnorm l]
  apply Set.ext
  intro f
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨b,(converges_iff_normalTopology M j hnorm l f b).mp hb⟩
  · rintro ⟨b,hb⟩
    exact ⟨b,(converges_iff_normalTopology M j hnorm l f b).mpr hb⟩

end SpectralIsometry.BoundedStrongStarNetGraph

