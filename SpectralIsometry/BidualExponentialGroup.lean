module

public import SpectralIsometry.BidualOperatorFunctor
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Bidual Exponential Group

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.OperatorExtension
universe u v
open UniversalWeakClosure
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf

local instance rationalEndNormedAlgebra {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] : NormedAlgebra ℚ (E →L[ℂ] E) :=
  .restrictScalars ℚ ℂ (E →L[ℂ] E)

attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] predualNormedGroup predualNormedSpace

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- Lifting is a continuous unital ring homomorphism on operator algebras. -/
def liftRingHom : (A →L[ℂ] A) →+* (algebra A →L[ℂ] algebra A) where
  toFun := lift
  map_zero' := (liftLinearIsometry (A := A) (B := A)).map_zero
  map_add' := lift_add
  map_one' := lift_id
  map_mul' := fun T S => lift_comp S T

theorem lift_exp (T : A →L[ℂ] A) :
    lift (NormedSpace.exp T : A →L[ℂ] A) =
      (NormedSpace.exp (lift T) : algebra A →L[ℂ] algebra A) :=
  NormedSpace.map_exp (liftRingHom (A := A))
    (liftOperator (A := A) (B := A)).continuous T

theorem lift_exp_smul (δ : A →L[ℂ] A) (z : ℂ) :
    lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) =
      (NormedSpace.exp (z • lift δ) : algebra A →L[ℂ] algebra A) :=
  (lift_exp (z • δ)).trans (congrArg
    (fun T : algebra A →L[ℂ] algebra A => NormedSpace.exp T) (lift_smul z δ))

theorem lift_inverse_apply (U : A ≃L[ℂ] B) (m : algebra A) :
    lift U.symm.toContinuousLinearMap (lift U.toContinuousLinearMap m) = m := by
  have hU : U.symm.toContinuousLinearMap.comp U.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ A := by
    apply ContinuousLinearMap.ext
    intro a
    exact U.symm_apply_apply a
  calc
    lift U.symm.toContinuousLinearMap (lift U.toContinuousLinearMap m) =
        lift (U.symm.toContinuousLinearMap.comp U.toContinuousLinearMap) m :=
      (congrArg (fun L : algebra A →L[ℂ] algebra A => L m)
        (lift_comp U.toContinuousLinearMap U.symm.toContinuousLinearMap)).symm
    _ = lift (ContinuousLinearMap.id ℂ A) m :=
      congrArg (fun T : A →L[ℂ] A => lift T m) hU
    _ = m := congrArg (fun L : algebra A →L[ℂ] algebra A => L m) (lift_id (A := A))

/-- The inverse is the lift of the original inverse; no new bijectivity
hypothesis on the bidual is required. -/
def liftEquiv (U : A ≃L[ℂ] B) : algebra A ≃L[ℂ] algebra B where
  __ := lift U.toContinuousLinearMap
  invFun := lift U.symm.toContinuousLinearMap
  left_inv := lift_inverse_apply U
  right_inv := lift_inverse_apply U.symm
  continuous_toFun := (lift U.toContinuousLinearMap).continuous
  continuous_invFun := (lift U.symm.toContinuousLinearMap).continuous

theorem lift_bijective (U : A ≃L[ℂ] B) :
    Function.Bijective (lift U.toContinuousLinearMap) := (liftEquiv U).bijective

theorem exp_operator_group (δ : A →L[ℂ] A) (z w : ℂ) :
    (NormedSpace.exp ((z + w) • δ) : A →L[ℂ] A) =
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).comp
        (NormedSpace.exp (w • δ) : A →L[ℂ] A) := by
  calc
    (NormedSpace.exp ((z + w) • δ) : A →L[ℂ] A) =
        NormedSpace.exp (z • δ + w • δ) := congrArg NormedSpace.exp (add_smul z w δ)
    _ = NormedSpace.exp (z • δ) * NormedSpace.exp (w • δ) :=
      NormedSpace.exp_add_of_commute (by
        change (z • δ) * (w • δ) = (w • δ) * (z • δ)
        apply ContinuousLinearMap.ext
        intro a
        change z • δ (w • δ a) = w • δ (z • δ a)
        rw [δ.map_smul, δ.map_smul, smul_smul, smul_smul, mul_comm z w])

theorem lift_exp_group (δ : A →L[ℂ] A) (z w : ℂ) :
    lift (NormedSpace.exp ((z + w) • δ) : A →L[ℂ] A) =
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)).comp
        (lift (NormedSpace.exp (w • δ) : A →L[ℂ] A)) :=
  (congrArg (fun T : A →L[ℂ] A => lift T) (exp_operator_group δ z w)).trans
    (lift_comp (NormedSpace.exp (w • δ)) (NormedSpace.exp (z • δ)))

theorem exp_operator_neg_mul (δ : A →L[ℂ] A) (z : ℂ) :
    (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A).comp
      (NormedSpace.exp (z • δ) : A →L[ℂ] A) = ContinuousLinearMap.id ℂ A := by
  apply ContinuousLinearMap.ext
  intro a
  have h := congrArg (fun T : A →L[ℂ] A => T a) (exp_operator_group δ (-z) z).symm
  simpa only [neg_add_cancel, zero_smul ℂ δ, NormedSpace.exp_zero,
    one_apply_eq_self, ContinuousLinearMap.id_apply] using h

theorem exp_operator_mul_neg (δ : A →L[ℂ] A) (z : ℂ) :
    (NormedSpace.exp (z • δ) : A →L[ℂ] A).comp
      (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A) = ContinuousLinearMap.id ℂ A := by
  apply ContinuousLinearMap.ext
  intro a
  have h := congrArg (fun T : A →L[ℂ] A => T a) (exp_operator_group δ z (-z)).symm
  simpa only [add_neg_cancel, zero_smul ℂ δ, NormedSpace.exp_zero,
    one_apply_eq_self, ContinuousLinearMap.id_apply] using h

/-- The original exponential is a bounded complex-linear bijection for every
parameter, independently of the spectral-isometry hypotheses. -/
def expOperatorEquiv (δ : A →L[ℂ] A) (z : ℂ) : A ≃L[ℂ] A where
  __ := (NormedSpace.exp (z • δ) : A →L[ℂ] A)
  invFun := (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A)
  left_inv := fun a => congrArg (fun T : A →L[ℂ] A => T a) (exp_operator_neg_mul δ z)
  right_inv := fun a => congrArg (fun T : A →L[ℂ] A => T a) (exp_operator_mul_neg δ z)
  continuous_toFun := (NormedSpace.exp (z • δ) : A →L[ℂ] A).continuous
  continuous_invFun := (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A).continuous

theorem lift_exp_bijective (δ : A →L[ℂ] A) (z : ℂ) :
    Function.Bijective (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) :=
  lift_bijective (expOperatorEquiv δ z)

theorem differentiable_lift_exp (δ : A →L[ℂ] A) :
    Differentiable ℂ (fun z : ℂ => lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) :=
  differentiable_lift (differentiable_exp_smul_const ℂ δ)

theorem differentiable_lift_exp_apply (δ : A →L[ℂ] A) (m : algebra A) :
    Differentiable ℂ (fun z : ℂ => lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) m) :=
  differentiable_lift_apply (differentiable_exp_smul_const ℂ δ) m

theorem lift_exp_unital (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1 = 1) (z : ℂ) :
    lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1 = 1 :=
  lift_one _ (h1 z)

end SpectralIsometry.BidualFoundation.OperatorExtension

