module

public import SpectralIsometry.ConcreteCornerRange

/-!
# Concrete Corner Topology

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open Filter Topology
open SpectralIsometry.StrongStarApproximation
open OAI.HochschildCorners

namespace SpectralIsometry.ConcreteCorner

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def WeakOperatorTendsto {ι : Type*} (a : ι → H →L[ℂ] H) (l : Filter ι)
    (b : H →L[ℂ] H) : Prop :=
  ∀ ξ η : H, Tendsto (fun i => inner ℂ ξ (a i η)) l (𝓝 (inner ℂ ξ (b η)))

lemma inner_compress (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (ξ η : K) :
    inner ℂ ξ (compress V T η) = inner ℂ (V ξ) (T (V η)) :=
  V.toContinuousLinearMap.adjoint_inner_right ξ (T (V η))

lemma inner_lift (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) (ξ η : H) :
    inner ℂ ξ (lift V T η) =
      inner ℂ (V.toContinuousLinearMap.adjoint ξ) (T (V.toContinuousLinearMap.adjoint η)) :=
  (V.toContinuousLinearMap.adjoint_inner_left (T (V.toContinuousLinearMap.adjoint η)) ξ).symm

theorem weakOperatorTendsto_compress (V : K →ₗᵢ[ℂ] H) {ι : Type*} {l : Filter ι}
    {a : ι → H →L[ℂ] H} {b : H →L[ℂ] H} (h : WeakOperatorTendsto a l b) :
    WeakOperatorTendsto (fun i => compress V (a i)) l (compress V b) := by
  intro ξ η
  simpa only [inner_compress] using h (V ξ) (V η)

theorem weakOperatorTendsto_lift (V : K →ₗᵢ[ℂ] H) {ι : Type*} {l : Filter ι}
    {a : ι → K →L[ℂ] K} {b : K →L[ℂ] K} (h : WeakOperatorTendsto a l b) :
    WeakOperatorTendsto (fun i => lift V (a i)) l (lift V b) := by
  intro ξ η
  simpa only [inner_lift] using h (V.toContinuousLinearMap.adjoint ξ) (V.toContinuousLinearMap.adjoint η)

theorem weakOperatorTendsto_lift_iff (V : K →ₗᵢ[ℂ] H) {ι : Type*} {l : Filter ι}
    {a : ι → K →L[ℂ] K} {b : K →L[ℂ] K} :
    WeakOperatorTendsto (fun i => lift V (a i)) l (lift V b) ↔ WeakOperatorTendsto a l b := by
  constructor
  · intro h
    simpa only [compress_lift] using weakOperatorTendsto_compress V h
  · exact weakOperatorTendsto_lift V

theorem strongTendsto_compress (V : K →ₗᵢ[ℂ] H) {ι : Type*} {l : Filter ι}
    {a : ι → H →L[ℂ] H} {b : H →L[ℂ] H} (h : StrongTendsto a l b) :
    StrongTendsto (fun i => compress V (a i)) l (compress V b) := by
  intro ξ
  change Tendsto (fun i => V.toContinuousLinearMap.adjoint (a i (V ξ))) l
    (𝓝 (V.toContinuousLinearMap.adjoint (b (V ξ))))
  exact V.toContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp (h (V ξ))

theorem strongTendsto_lift (V : K →ₗᵢ[ℂ] H) {ι : Type*} {l : Filter ι}
    {a : ι → K →L[ℂ] K} {b : K →L[ℂ] K} (h : StrongTendsto a l b) :
    StrongTendsto (fun i => lift V (a i)) l (lift V b) := by
  intro ξ
  change Tendsto (fun i => V (a i (V.toContinuousLinearMap.adjoint ξ))) l
    (𝓝 (V (b (V.toContinuousLinearMap.adjoint ξ))))
  exact V.continuous.continuousAt.tendsto.comp (h (V.toContinuousLinearMap.adjoint ξ))

theorem strongStarTendsto_compress (V : K →ₗᵢ[ℂ] H) {ι : Type*} {l : Filter ι}
    {a : ι → H →L[ℂ] H} {b : H →L[ℂ] H} (h : StrongStarTendsto a l b) :
    StrongStarTendsto (fun i => compress V (a i)) l (compress V b) := by
  refine ⟨strongTendsto_compress V h.1,?_⟩
  simpa only [compress_star] using strongTendsto_compress V h.2

theorem strongStarTendsto_lift (V : K →ₗᵢ[ℂ] H) {ι : Type*} {l : Filter ι}
    {a : ι → K →L[ℂ] K} {b : K →L[ℂ] K} (h : StrongStarTendsto a l b) :
    StrongStarTendsto (fun i => lift V (a i)) l (lift V b) := by
  refine ⟨strongTendsto_lift V h.1,?_⟩
  simpa only [lift_star] using strongTendsto_lift V h.2

theorem strongStarTendsto_lift_iff (V : K →ₗᵢ[ℂ] H) {ι : Type*} {l : Filter ι}
    {a : ι → K →L[ℂ] K} {b : K →L[ℂ] K} :
    StrongStarTendsto (fun i => lift V (a i)) l (lift V b) ↔ StrongStarTendsto a l b := by
  constructor
  · intro h
    simpa only [compress_lift] using strongStarTendsto_compress V h
  · exact strongStarTendsto_lift V

def continuousEquivalence (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :
    model M p hp ≃L[ℂ] Corner p hp where
  toLinearEquiv := (equivalence M p hp).toAlgEquiv.toLinearEquiv
  continuous_toFun := (equivalence_isometry M p hp).continuous
  continuous_invFun := (equivalence_symm_isometry M p hp).continuous

theorem strongStarTendsto_equivalence_iff
    (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    {ι : Type*} {l : Filter ι} (a : ι → model M p hp) (b : model M p hp) :
    StrongStarTendsto (fun i => (((equivalence M p hp (a i) : Corner p hp) : M) : H →L[ℂ] H)) l
      (((equivalence M p hp b : Corner p hp) : M) : H →L[ℂ] H) ↔
    StrongStarTendsto (fun i => (a i : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)) l
      (b : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp) := by
  change StrongStarTendsto (fun i => lift (cornerInclusion M p hp) (a i)) l
    (lift (cornerInclusion M p hp) b) ↔ _
  exact strongStarTendsto_lift_iff (cornerInclusion M p hp)

theorem weakOperatorTendsto_equivalence_iff
    (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    {ι : Type*} {l : Filter ι} (a : ι → model M p hp) (b : model M p hp) :
    WeakOperatorTendsto (fun i => (((equivalence M p hp (a i) : Corner p hp) : M) : H →L[ℂ] H)) l
      (((equivalence M p hp b : Corner p hp) : M) : H →L[ℂ] H) ↔
    WeakOperatorTendsto (fun i => (a i : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)) l
      (b : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp) := by
  change WeakOperatorTendsto (fun i => lift (cornerInclusion M p hp) (a i)) l
    (lift (cornerInclusion M p hp) b) ↔ _
  exact weakOperatorTendsto_lift_iff (cornerInclusion M p hp)

end SpectralIsometry.ConcreteCorner

