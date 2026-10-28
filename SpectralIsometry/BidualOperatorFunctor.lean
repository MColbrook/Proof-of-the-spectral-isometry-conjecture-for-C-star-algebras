module

public import SpectralIsometry.BidualOperatorCore
public import SpectralIsometry.GenericTranspose

/-!
# Bidual Operator Functor

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.OperatorExtension
universe u v w
open UniversalWeakClosure
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] predualNormedGroup predualNormedSpace
attribute [local instance] dualGroup dualSpace bidualGroup bidualSpace

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

theorem lift_id :
    lift (ContinuousLinearMap.id ℂ A) = ContinuousLinearMap.id ℂ (algebra A) := by
  apply ContinuousLinearMap.ext
  intro m
  change canonicalBidualIsometry A
    (secondTranspose (ContinuousLinearMap.id ℂ A) ((canonicalBidualIsometry A).symm m)) = m
  have h := congrArg
    (fun F : StrongDual ℂ (StrongDual ℂ A) →L[ℂ] StrongDual ℂ (StrongDual ℂ A) =>
      F ((canonicalBidualIsometry A).symm m)) (secondTranspose_id (E := A))
  exact (congrArg (canonicalBidualIsometry A) h).trans
    ((canonicalBidualIsometry A).apply_symm_apply m)

theorem lift_comp {C : Type w} [CStarAlgebra C]
    (T : A →L[ℂ] B) (S : B →L[ℂ] C) :
    lift (S.comp T) = (lift S).comp (lift T) := by
  apply ContinuousLinearMap.ext
  intro m
  change canonicalBidualIsometry C
    (secondTranspose (S.comp T) ((canonicalBidualIsometry A).symm m)) =
      canonicalBidualIsometry C (secondTranspose S
        ((canonicalBidualIsometry B).symm (canonicalBidualIsometry B
          (secondTranspose T ((canonicalBidualIsometry A).symm m)))))
  have hcomp := congrArg
    (fun F : StrongDual ℂ (StrongDual ℂ A) →L[ℂ] StrongDual ℂ (StrongDual ℂ C) =>
      F ((canonicalBidualIsometry A).symm m)) (secondTranspose_comp T S)
  have hcancel := congrArg (secondTranspose S)
    ((canonicalBidualIsometry B).symm_apply_apply
      (secondTranspose T ((canonicalBidualIsometry A).symm m)))
  exact (congrArg (canonicalBidualIsometry C) hcomp).trans
    (congrArg (canonicalBidualIsometry C) hcancel.symm)

theorem lift_one (T : A →L[ℂ] B) (hT : T 1 = 1) : lift T 1 = 1 := by
  calc
    lift T 1 = lift T (inclusion A 1) := congrArg (lift T) (inclusion A).map_one.symm
    _ = inclusion B (T 1) := lift_inclusion T 1
    _ = inclusion B 1 := congrArg (inclusion B) hT
    _ = 1 := (inclusion B).map_one

theorem lift_norm_le (T : A →L[ℂ] B) : ‖lift T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro m
  calc
    ‖lift T m‖ = ‖secondTranspose T ((canonicalBidualIsometry A).symm m)‖ :=
      (canonicalBidualIsometry B).norm_map _
    _ ≤ ‖secondTranspose T‖ * ‖(canonicalBidualIsometry A).symm m‖ :=
      (secondTranspose T).le_opNorm _
    _ ≤ ‖T‖ * ‖(canonicalBidualIsometry A).symm m‖ :=
      mul_le_mul_of_nonneg_right (secondTranspose_norm_le T) (norm_nonneg _)
    _ = ‖T‖ * ‖m‖ := congrArg (fun r : ℝ => ‖T‖ * r)
      ((canonicalBidualIsometry A).symm.norm_map m)

theorem lift_norm_eq (T : A →L[ℂ] B) : ‖lift T‖ = ‖T‖ := by
  apply le_antisymm (lift_norm_le T)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (lift T))
  intro a
  calc
    ‖T a‖ = ‖inclusion B (T a)‖ := (inclusion_norm B (T a)).symm
    _ = ‖lift T (inclusion A a)‖ := congrArg norm (lift_inclusion T a).symm
    _ ≤ ‖lift T‖ * ‖inclusion A a‖ := (lift T).le_opNorm _
    _ = ‖lift T‖ * ‖a‖ := congrArg (fun r : ℝ => ‖lift T‖ * r) (inclusion_norm A a)

theorem lift_add (T S : A →L[ℂ] B) : lift (T + S) = lift T + lift S := by
  apply ContinuousLinearMap.ext
  intro m
  change canonicalBidualIsometry B
    (secondTranspose (T + S) ((canonicalBidualIsometry A).symm m)) =
      canonicalBidualIsometry B (secondTranspose T ((canonicalBidualIsometry A).symm m)) +
        canonicalBidualIsometry B (secondTranspose S ((canonicalBidualIsometry A).symm m))
  have h := congrArg
    (fun F : StrongDual ℂ (StrongDual ℂ A) →L[ℂ] StrongDual ℂ (StrongDual ℂ B) =>
      F ((canonicalBidualIsometry A).symm m)) (secondTranspose_add T S)
  exact (congrArg (canonicalBidualIsometry B) h).trans
    ((canonicalBidualIsometry B).map_add _ _)

theorem lift_smul (z : ℂ) (T : A →L[ℂ] B) : lift (z • T) = z • lift T := by
  apply ContinuousLinearMap.ext
  intro m
  change canonicalBidualIsometry B
    (secondTranspose (z • T) ((canonicalBidualIsometry A).symm m)) =
      z • canonicalBidualIsometry B (secondTranspose T ((canonicalBidualIsometry A).symm m))
  have h := congrArg
    (fun F : StrongDual ℂ (StrongDual ℂ A) →L[ℂ] StrongDual ℂ (StrongDual ℂ B) =>
      F ((canonicalBidualIsometry A).symm m)) (secondTranspose_smul z T)
  exact (congrArg (canonicalBidualIsometry B) h).trans
    ((canonicalBidualIsometry B).map_smul z _)

/-- The operator lift preserves norms and complex linear combinations. -/
def liftLinearIsometry : (A →L[ℂ] B) →ₗᵢ[ℂ] (algebra A →L[ℂ] algebra B) where
  toFun := fun T => lift T
  map_add' := lift_add
  map_smul' := lift_smul
  norm_map' := lift_norm_eq

def liftOperator : (A →L[ℂ] B) →L[ℂ] (algebra A →L[ℂ] algebra B) :=
  (liftLinearIsometry (A := A) (B := B)).toContinuousLinearMap

theorem differentiable_lift {f : ℂ → (A →L[ℂ] B)} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => lift (f z)) :=
  (liftOperator (A := A) (B := B)).differentiable.comp hf

theorem differentiable_lift_apply {f : ℂ → (A →L[ℂ] B)}
    (hf : Differentiable ℂ f) (m : algebra A) :
    Differentiable ℂ (fun z => lift (f z) m) :=
  ((ContinuousLinearMap.apply ℂ (algebra B)) m).differentiable.comp (differentiable_lift hf)

end SpectralIsometry.BidualFoundation.OperatorExtension

