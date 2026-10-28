module
public import SpectralIsometry.NormalSeminormTopology

/-!
# Normal Seminorm Witness

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ComplexOrder

namespace SpectralIsometry.NormalSeminorm
open OAI.HochschildNormalPart
universe u w
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
local instance witnessOrderedM : PartialOrder M := CStarAlgebra.spectralOrder M
local instance witnessStarOrderedM : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
local instance (priority := 2000) witnessComplexOrder : PartialOrder ℂ := Complex.partialOrder
local instance (priority := 2000) witnessComplexStarOrder : StarOrderedRing ℂ := RCLike.toStarOrderedRing

theorem exists_complex_seminorm (ψ : M →ₚ[ℂ] ℂ) :
    ∃ p : Seminorm ℂ M, ∀ x : M,
      p x=Real.sqrt ((ψ (star x*x)).re+(ψ (x*star x)).re) :=
  ⟨bundled ψ,fun x => bundled_apply ψ x⟩

theorem exists_normal_seminorm_topology (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ t : TopologicalSpace M, ∀ (ι : Type w) (a : ι → M) (l : Filter ι) (b : M),
      Tendsto a l (@nhds M t b) ↔ SeminormTendsto e a l b :=
  ⟨strongStarTopology e,fun _ a l b => tendsto_topology_iff e a l b⟩

/-- A single package realizes the literal normal-positive seminorm family,
its generated topology, and all-filter convergence in that topology. -/
theorem exists_generated_normal_seminorm_topology (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ p : (M →ₚ[ℂ] ℂ) → Seminorm ℂ M,
      (∀ (ψ : M →ₚ[ℂ] ℂ) (x : M), p ψ x=seminorm ψ x) ∧
      ∃ t : TopologicalSpace M,
        @WithSeminorms ℂ M (NormalPositiveIndex e) _ _ _ (fun i => p i.val) t ∧
        ∀ (ι : Type w) (a : ι → M) (l : Filter ι) (b : M),
          Tendsto a l (@nhds M t b) ↔ SeminormTendsto e a l b :=
  ⟨bundled,fun ψ x => bundled_apply ψ x,strongStarTopology e,
    topology_withSeminorms e,fun _ a l b => tendsto_topology_iff e a l b⟩

end SpectralIsometry.NormalSeminorm

