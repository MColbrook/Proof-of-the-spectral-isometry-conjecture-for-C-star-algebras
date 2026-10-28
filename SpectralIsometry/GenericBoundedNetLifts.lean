module
public import SpectralIsometry.BoundedStrongStarNetGraph

/-!
# Generic Bounded Net Lifts

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction

namespace SpectralIsometry.BoundedStrongStarNetGraph
open StrongStarApproximation

variable {I A H : Type*} [TopologicalSpace I] [DiscreteTopology I] [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (j : A →⋆ₐ[ℂ] M)
  (hnorm : ∀ a : A, ‖j a‖≤‖a‖) (l : Filter I) [l.NeBot]

theorem limitHom_surjective_of_approximants
    (happrox : ∀ b : M, ∃ a : I → A, (∀ i, ‖a i‖≤‖b‖) ∧
      StrongStarTendsto (fun i => (j (a i):H →L[ℂ] H)) l (b:H →L[ℂ] H)) :
    Function.Surjective (limitHom M j hnorm l) := by
  intro b
  obtain ⟨a,haN,haT⟩ := happrox b
  let f : I →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete a ‖b‖ haN
  let p : graph M j hnorm l := ⟨(f,b),haT⟩
  exact ⟨p,rfl⟩

theorem squareZero_lift_of_approximants
    (b : M) (hb : b^2=0)
    (a : I → A) (ha2 : ∀ i, (a i)^2=0) (haN : ∀ i, ‖a i‖≤‖b‖)
    (haT : StrongStarTendsto (fun i => (j (a i):H →L[ℂ] H)) l (b:H →L[ℂ] H)) :
    ∃ p : graph M j hnorm l, p^2=0 ∧ ‖p‖≤‖b‖ ∧ limitHom M j hnorm l p=b := by
  let f : I →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete a ‖b‖ haN
  let p : graph M j hnorm l := ⟨(f,b),haT⟩
  refine ⟨p,?_,?_,rfl⟩
  · apply Subtype.ext
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro i
      exact ha2 i
    · exact hb
  · rw [graph_norm M j hnorm l p]
    change ‖f‖≤‖b‖
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      continuous_of_discreteTopology (norm_nonneg b) haN

theorem squareZero_contraction_lift_of_approximants
    (b : M) (hb : b^2=0) (hbN : ‖b‖≤1)
    (a : I → A) (ha2 : ∀ i, (a i)^2=0) (haN : ∀ i, ‖a i‖≤‖b‖)
    (haT : StrongStarTendsto (fun i => (j (a i):H →L[ℂ] H)) l (b:H →L[ℂ] H)) :
    ∃ p : graph M j hnorm l, p^2=0 ∧ ‖p‖≤1 ∧ limitHom M j hnorm l p=b := by
  obtain ⟨p,hp2,hpN,hp⟩ :=
    squareZero_lift_of_approximants M j hnorm l b hb a ha2 haN haT
  exact ⟨p,hp2,hpN.trans hbN,hp⟩

end SpectralIsometry.BoundedStrongStarNetGraph

