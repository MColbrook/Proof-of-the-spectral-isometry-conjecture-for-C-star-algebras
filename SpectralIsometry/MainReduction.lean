module

public import SpectralIsometry.Basic
public import SpectralIsometry.Bicommutant
public import SpectralIsometry.TransportKernel
public import SpectralIsometry.SubalgebraRadius
public import SpectralIsometry.TransportExp
public import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.Tactic.NoncommRing

/-!
# Main Reduction

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

namespace SpectralIsometry.MainReduction

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A bounded equivalence is derived from the original ordinary map hypotheses. -/
def radiusEquiv (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) : A ≃L[ℂ] B :=
  (LinearEquiv.ofBijective T ⟨injective_of_preservesRadius T hr,honto⟩).toContinuousLinearEquivOfContinuous
      (AutomaticContinuity.continuous_of_surjective_preservesRadius T honto hr)

@[simp] theorem radiusEquiv_apply (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (hr : PreservesRadius T) (a : A) : radiusEquiv T honto hr a = T a := rfl

/-- Explicit intermediate premise; the entire-group proposition must prove it. -/
def AllTransportedLeibniz (U : A ≃L[ℂ] B) : Prop :=
  ∀ (x : A) (a b : B), TransportExp.transportedCLM U x (a*b) =
    TransportExp.transportedCLM U x a*b+a*TransportExp.transportedCLM U x b

theorem transportedInner_eq_transportedCLM (U : A ≃L[ℂ] B) (x : A) (b : B) :
    MainTransport.transportedInner U.toLinearEquiv x b = TransportExp.transportedCLM U x b := rfl

def imageBicommutantAlgebra (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hder : AllTransportedLeibniz U) (h : selfAdjoint A) : Subalgebra ℂ B :=
  MainTransport.transportedCentralizerAlgebra U.toLinearEquiv h1
    (({(h:A)} : Set A).centralizer) (fun x _ a b => hder x a b)

/-- Exact image definition E_h=T(C_h), with no assumed star closure of E_h. -/
theorem imageBicommutantAlgebra_coe (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hder : AllTransportedLeibniz U) (h : selfAdjoint A) :
    (imageBicommutantAlgebra U h1 hder h : Set B) = U '' (relativeBicommutant h : Set A) := by
  ext b
  constructor
  · intro hb
    refine ⟨U.symm b,?_,U.apply_symm_apply b⟩
    rw [relativeBicommutant_coe]
    exact hb
  · rintro ⟨a,ha,rfl⟩
    change U.symm (U a)∈Subalgebra.centralizer ℂ (({(h:A)}:Set A).centralizer)
    rw [U.symm_apply_apply]
    change a∈({(h:A)}:Set A).centralizer.centralizer
    rwa [←relativeBicommutant_coe]

/-- The source's intersection-of-kernels identity. -/
theorem imageBicommutantAlgebra_eq_common_kernel (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hder : AllTransportedLeibniz U) (h : selfAdjoint A) :
    (imageBicommutantAlgebra U h1 hder h : Set B) =
      {b : B | ∀ x ∈ ({(h:A)} : Set A).centralizer, TransportExp.transportedCLM U x b=0} := by
  rw [imageBicommutantAlgebra_coe,relativeBicommutant_coe]
  simpa only [transportedInner_eq_transportedCLM,ContinuousLinearEquiv.coe_toLinearEquiv] using
    MainTransport.image_centralizer_eq_common_kernel U.toLinearEquiv (({(h:A)}:Set A).centralizer)

theorem imageBicommutantAlgebra_isClosed (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hder : AllTransportedLeibniz U) (h : selfAdjoint A) :
    IsClosed (imageBicommutantAlgebra U h1 hder h : Set B) :=
  MainTransport.transportedCentralizerAlgebra_isClosed U h1
    (({(h:A)} : Set A).centralizer) (fun x _ a b => hder x a b)

private theorem ambient_normal_of_mem_relativeBicommutant (h : selfAdjoint A)
    (a : A) (ha : a ∈ relativeBicommutant h) : IsStarNormal a := by
  let c : relativeBicommutant h := ⟨a,ha⟩
  refine ⟨?_⟩
  exact congrArg (fun d : relativeBicommutant h => (d:A)) (mul_comm (star c) c)

/-- The manuscript's inherited-norm/intrinsic-radius bound, derived for E_h. -/
theorem imageBicommutant_norm_radius_bound (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (hder : AllTransportedLeibniz U)
    (h : selfAdjoint A) (w : imageBicommutantAlgebra U h1 hder h) :
    ‖w‖ ≤ ‖U.toContinuousLinearMap‖*(spectralRadius ℂ w).toReal := by
  let E := imageBicommutantAlgebra U h1 hder h
  have hE : IsClosed (E : Set B) := imageBicommutantAlgebra_isClosed U h1 hder h
  have hw : (w:B) ∈ U '' (relativeBicommutant h : Set A) := by
    rw [←imageBicommutantAlgebra_coe U h1 hder h]
    exact w.property
  obtain ⟨a,ha,haw⟩ := hw
  letI : IsStarNormal a := ambient_normal_of_mem_relativeBicommutant h a ha
  have hn : ‖a‖=(spectralRadius ℂ a).toReal := by
    rw [IsStarNormal.spectralRadius_eq_nnnorm,ENNReal.coe_toReal,coe_nnnorm]
  have hrad : spectralRadius ℂ w = spectralRadius ℂ a := by
    rw [closed_subalgebra_spectralRadius E hE w,←haw]
    exact hr a
  calc
    ‖w‖=‖U a‖ := congrArg norm haw.symm
    _ ≤ ‖U.toContinuousLinearMap‖*‖a‖ := U.toContinuousLinearMap.le_opNorm a
    _ = ‖U.toContinuousLinearMap‖*(spectralRadius ℂ w).toReal := by rw [hn,hrad]

/-- E_h is proved commutative by the derived bound and the checked Liouville lemma. -/
theorem imageBicommutant_mul_comm (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (hder : AllTransportedLeibniz U)
    (h : selfAdjoint A) (y w : imageBicommutantAlgebra U h1 hder h) : y*w=w*y := by
  let E := imageBicommutantAlgebra U h1 hder h
  letI : CompleteSpace E := (imageBicommutantAlgebra_isClosed U h1 hder h).completeSpace_coe
  exact mul_comm_of_norm_le_spectralRadius ‖U.toContinuousLinearMap‖
    (imageBicommutant_norm_radius_bound U h1 hr hder h) y w

section Jacobson

variable {E : Type*} [NormedCommRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

/-- Literal radical-zero conclusion, using maximal character kernels and the
generic commutative Banach spectrum theorem. This means Banach semiprimitivity,
not Artinian semisimplicity. Mathlib Jacobson.Radical and GelfandDuality reused. -/
theorem jacobson_eq_bot_of_norm_radius_bound (K : ℝ)
    (hK : ∀ a:E, ‖a‖≤K*(spectralRadius ℂ a).toReal) : Ring.jacobson E=⊥ := by
  apply le_bot_iff.mp
  intro a ha
  change a=0
  have hchar (φ : WeakDual.characterSpace ℂ E) : φ a=0 :=
    RingHom.mem_ker.mp ((Ring.jacobson_le_of_isMaximal (RingHom.ker φ)) ha)
  have hrad : spectralRadius ℂ a=0 := by
    apply le_antisymm ?_ bot_le
    rw [spectralRadius_eq_of_unital]
    apply iSup₂_le
    intro z hz
    obtain ⟨φ,rfl⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
    simp [hchar]
  exact eq_zero_of_norm_radius_bound K hK a hrad

end Jacobson

theorem imageBicommutant_jacobson_eq_bot (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (hder : AllTransportedLeibniz U)
    (h : selfAdjoint A) : Ring.jacobson (imageBicommutantAlgebra U h1 hder h)=⊥ := by
  let E := imageBicommutantAlgebra U h1 hder h
  letI : CompleteSpace E := (imageBicommutantAlgebra_isClosed U h1 hder h).completeSpace_coe
  letI : NormedCommRing E :=
    { (inferInstance : NormedRing E) with mul_comm:=imageBicommutant_mul_comm U h1 hr hder h }
  exact jacobson_eq_bot_of_norm_radius_bound ‖U.toContinuousLinearMap‖
    (imageBicommutant_norm_radius_bound U h1 hr hder h)

end SpectralIsometry.MainReduction

