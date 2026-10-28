module

public import SpectralIsometry.UniversalSelfAdjointApproximation
public import SpectralIsometry.UniversalSquareZeroExtension
public import SpectralIsometry.BoundedInverseLimit
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Universal Real Spectrum Extension

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped NNReal

namespace SpectralIsometry.BidualFoundation.UniversalRealSpectrumExtension

open UniversalWeakClosure OperatorExtension StrongStarApproximation
open OAI.BoundedHochschild.KadisonRingrose

private theorem strongStar_const_sub {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} {l : Filter ι}
    {a : ι → (H →L[ℂ] H)} {b : H →L[ℂ] H}
    (ha : StrongStarTendsto a l b) (c : H →L[ℂ] H) :
    StrongStarTendsto (fun i => c-a i) l (c-b) := by
  constructor
  · intro ξ
    simpa only [sub_apply] using (tendsto_const_nhds (x:=c ξ) (f:=l)).sub (ha.1 ξ)
  · intro ξ
    simpa only [star_sub,sub_apply] using
      (tendsto_const_nhds (x:=star c ξ) (f:=l)).sub (ha.2 ξ)

private theorem vonNeumann_normClosed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  exact Eq.mp (congrArg IsClosed M.centralizer_centralizer') (Set.isClosed_centralizer _)

private theorem vonNeumann_isUnit_of_coe {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) (x : M)
    (hx : IsUnit (x : H →L[ℂ] H)) : IsUnit x := by
  letI : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumann_normClosed M
  exact (StarSubalgebra.coe_isUnit M.toStarSubalgebra).mp hx

universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] predualNormedGroup predualNormedSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

/-- The image of every self-adjoint universal-bidual element has an invertible
resolvent at every nonreal scalar. Original spectral-isometry hypotheses only. -/
theorem lift_selfadjoint_resolvent_isUnit (U : A ≃L[ℂ] B)
    (hρ : PreservesRadius U.toLinearEquiv.toLinearMap) (h1 : U 1=1)
    (x : algebra A) (hx : IsSelfAdjoint x) (z : ℂ) (hz : z.im≠0) :
    IsUnit (algebraMap ℂ (algebra B) z-lift U.toContinuousLinearMap x) := by
  obtain ⟨a,haSA,haN,haT⟩ := UniversalSelfAdjointApproximation.exists_bounded_net A x hx
  let I := UniversalApproximation.Index A
  letI : (atTop : Filter I).NeBot := UniversalApproximation.index_neBot A
  let π : B →⋆ₐ[ℂ] (Hilbert B →L[ℂ] Hilbert B) := universalGNSRepresentation (M:=B)
  let c : I → B := fun i => algebraMap ℂ B z-U (a i)
  let C : I → (Hilbert B →L[ℂ] Hilbert B) := fun i => π (c i)
  let D : I → (Hilbert B →L[ℂ] Hilbert B) := fun i => π (Ring.inverse (c i))
  let L : ℝ≥0 := ⟨‖U.symm.toContinuousLinearMap‖ / |z.im|,
    div_nonneg (norm_nonneg _) (abs_nonneg _)⟩
  have hc (i : I) : IsUnit (c i) ∧ ‖Ring.inverse (c i)‖≤L :=
    image_selfadjoint_resolvent_bound U hρ h1 (a i) (haSA i) z hz
  have hleft (i : I) : D i*C i=1 := by
    dsimp only [D,C]
    rw [←map_mul,Ring.inverse_mul_cancel _ (hc i).1,map_one]
  have hright (i : I) : C i*D i=1 := by
    dsimp only [D,C]
    rw [←map_mul,Ring.mul_inverse_cancel _ (hc i).1,map_one]
  have hN (i : I) : ‖D i‖≤L := by
    change ‖universalGNSRepresentation (Ring.inverse (c i))‖≤L
    rw [universalGNSRepresentation_norm]
    exact (hc i).2
  have ht := UniversalSquareZeroExtension.lift_strongStarTendsto U.toContinuousLinearMap
    (fun i => inclusion A (a i)) x haT
  have htU : StrongStarTendsto (fun i : I => π (U (a i))) atTop
      (lift U.toContinuousLinearMap x : Hilbert B →L[ℂ] Hilbert B) := by
    simpa only [π,I,lift_inclusion,inclusion_coe,ContinuousLinearEquiv.coe_coe] using ht
  let b : algebra B := algebraMap ℂ (algebra B) z-lift U.toContinuousLinearMap x
  have hscalar : ((algebraMap ℂ (algebra B) z : algebra B) : Hilbert B →L[ℂ] Hilbert B)=
      algebraMap ℂ (Hilbert B →L[ℂ] Hilbert B) z :=
    (algebra B).toStarSubalgebra.subtype.commutes z
  have hC : StrongStarTendsto C atTop (b : Hilbert B →L[ℂ] Hilbert B) := by
    have hh := strongStar_const_sub htU (algebraMap ℂ (Hilbert B →L[ℂ] Hilbert B) z)
    have hCeq (i : I) : C i=algebraMap ℂ (Hilbert B →L[ℂ] Hilbert B) z-π (U (a i)) := by
      dsimp only [C,c]
      rw [map_sub]
      exact congrArg (fun v : Hilbert B →L[ℂ] Hilbert B => v-π (U (a i))) (π.commutes z)
    have hb : (b : Hilbert B →L[ℂ] Hilbert B)=
        algebraMap ℂ (Hilbert B →L[ℂ] Hilbert B) z-
          (lift U.toContinuousLinearMap x : Hilbert B →L[ℂ] Hilbert B) := by
      change ((algebraMap ℂ (algebra B) z : algebra B) : Hilbert B →L[ℂ] Hilbert B)-
        (lift U.toContinuousLinearMap x : Hilbert B →L[ℂ] Hilbert B)=_
      rw [hscalar]
    have hCfun : C=(fun i : I => algebraMap ℂ (Hilbert B →L[ℂ] Hilbert B) z-π (U (a i))) :=
      funext hCeq
    rw [hCfun,hb]
    exact hh
  have hbOp : IsUnit (b : Hilbert B →L[ℂ] Hilbert B) :=
    BoundedInverseLimit.isUnit_of_strongStar_of_inverse_norm_bound C D _ L hC hleft hright hN
  exact vonNeumann_isUnit_of_coe (algebra B) b hbOp

theorem lift_selfadjoint_real_spectrum (U : A ≃L[ℂ] B)
    (hρ : PreservesRadius U.toLinearEquiv.toLinearMap) (h1 : U 1=1)
    (x : algebra A) (hx : IsSelfAdjoint x) (z : ℂ)
    (hz : z ∈ spectrum ℂ (lift U.toContinuousLinearMap x)) : z.im=0 := by
  by_contra hzim
  exact (spectrum.mem_iff.mp hz) (lift_selfadjoint_resolvent_isUnit U hρ h1 x hx z hzim)

end SpectralIsometry.BidualFoundation.UniversalRealSpectrumExtension

