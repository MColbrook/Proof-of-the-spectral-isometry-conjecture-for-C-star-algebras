module

public import SpectralIsometry.BidualDuality
public import SpectralIsometry.BidualNormality
public import SpectralIsometry.GenericTransposeCore

/-!
# Bidual Operator Core

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.OperatorExtension

open scoped InnerProductSpace

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf

universe u v w

open UniversalWeakClosure

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] predualNormedGroup predualNormedSpace

/-- The unique predual action induced by the original bounded map. -/
def preadjoint (T : A →L[ℂ] B) : predual B →L[ℂ] predual A :=
  (canonicalPredualEquiv A).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((transpose T).comp (canonicalPredualEquiv B).toContinuousLinearEquiv.toContinuousLinearMap)

theorem preadjoint_restriction (T : A →L[ℂ] B) (Φ : predual B) :
    restriction A (preadjoint T Φ) = (restriction B Φ).comp T :=
  canonicalPredualEquiv_restrict A ((restriction B Φ).comp T)

/-- The second transpose, transported through the proved canonical linear
isometries. Its normality is proved from the pairing below. -/
def lift (T : A →L[ℂ] B) : algebra A →L[ℂ] algebra B :=
  (canonicalBidualIsometry B).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((secondTranspose T).comp
      (canonicalBidualIsometry A).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem lift_pairing (T : A →L[ℂ] B) (m : algebra A) (Φ : predual B) :
    (Φ : StrongDual ℂ (algebra B)) (lift T m) =
      ((preadjoint T Φ : predual A) : StrongDual ℂ (algebra A)) m := by
  change (Φ : StrongDual ℂ (algebra B))
    (canonicalBidualIsometry B
      (secondTranspose T ((canonicalBidualIsometry A).symm m))) = _
  calc
    (Φ : StrongDual ℂ (algebra B))
        (canonicalBidualIsometry B
          (secondTranspose T ((canonicalBidualIsometry A).symm m))) =
        secondTranspose T ((canonicalBidualIsometry A).symm m) (restriction B Φ) :=
      canonicalBidualIsometry_pairing B
        (secondTranspose T ((canonicalBidualIsometry A).symm m)) Φ
    _ = (canonicalBidualIsometry A).symm m ((restriction B Φ).comp T) := rfl
    _ = ((preadjoint T Φ : predual A) : StrongDual ℂ (algebra A)) m :=
      canonicalBidualIsometry_symm_pairing A m ((restriction B Φ).comp T)

theorem lift_inclusion (T : A →L[ℂ] B) (a : A) :
    lift T (inclusion A a) = inclusion B (T a) := by
  apply (CoefficientPredual.predualEvaluationEquiv (algebra B)).injective
  apply ContinuousLinearMap.ext
  intro Φ
  change (Φ : StrongDual ℂ (algebra B)) (lift T (inclusion A a)) =
    (Φ : StrongDual ℂ (algebra B)) (inclusion B (T a))
  calc
    (Φ : StrongDual ℂ (algebra B)) (lift T (inclusion A a)) =
        ((preadjoint T Φ : predual A) : StrongDual ℂ (algebra A)) (inclusion A a) :=
      lift_pairing T (inclusion A a) Φ
    _ = restriction A (preadjoint T Φ) a := rfl
    _ = ((restriction B Φ).comp T) a :=
      congrArg (fun f : StrongDual ℂ A => f a) (preadjoint_restriction T Φ)
    _ = (Φ : StrongDual ℂ (algebra B)) (inclusion B (T a)) := rfl

/-- Weak-star convergence expressed by every concrete predual functional. -/
def CoefficientTendsto {I : Type*} (m : I → algebra A) (l : Filter I)
    (n : algebra A) : Prop :=
  ∀ Φ : predual A, Filter.Tendsto
    (fun i => (Φ : StrongDual ℂ (algebra A)) (m i)) l
    (nhds ((Φ : StrongDual ℂ (algebra A)) n))

theorem lift_coefficientTendsto (T : A →L[ℂ] B) {I : Type*}
    {m : I → algebra A} {l : Filter I} {n : algebra A}
    (h : CoefficientTendsto m l n) :
    CoefficientTendsto (fun i => lift T (m i)) l (lift T n) := by
  intro Φ
  simpa only [lift_pairing T] using h (preadjoint T Φ)

/-- Exact normality of each represented target-vector coefficient. No abstract
normality or continuity hypothesis on the lifted operator is supplied. -/
theorem lift_vector_pairing (T : A →L[ℂ] B) (ξ η : Hilbert B) :
    ∃ Φ : predual A, ∀ m : algebra A,
      (Φ : StrongDual ℂ (algebra A)) m =
        ⟪η, (lift T m : Hilbert B →L[ℂ] Hilbert B) ξ⟫_ℂ := by
  let Ψ := CoefficientPredual.coefficientVector (algebra B) η ξ
  refine ⟨preadjoint T Ψ, fun m => ?_⟩
  exact (lift_pairing T m Ψ).symm

end SpectralIsometry.BidualFoundation.OperatorExtension

