module
public import SpectralIsometry.FiniteQuotientAssembly
public import SpectralIsometry.ExponentialCoercion

/-!
# Finite Quotient Inverse

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open OAI.HochschildCorners OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.FiniteQuotientInverse
open FiniteQuotientAssembly

def NegativeInverseFamily {E : Type*} [AddCommGroup E] [Module ℂ E]
    (K : ℂ → E →ₗ[ℂ] E) : Prop :=
  ∀ (z : ℂ) (a : E), K (-z) (K z a)=a

theorem negativeInverseFamily_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (K : ℂ → E →ₗ[ℂ] E) (hK : NegativeInverseFamily K) (z : ℂ) (a : E) :
    K z (K (-z) a)=a := by
  simpa only [neg_neg] using hK (-z) a

theorem finiteBlock_id {M : Type*} [CStarAlgebra M]
    (q : M) (hq : IsStarProjection q) (hqc : ∀ a : M, q*a=a*q) :
    finiteBlock q hq hqc (LinearMap.id : M →ₗ[ℂ] M)=LinearMap.id := by
  apply LinearMap.ext
  intro a
  exact centralCompressionHom_include q hq hqc a

theorem finiteBlock_negative_family {M : Type*} [CStarAlgebra M]
    (q : M) (hq : IsStarProjection q) (hqc : ∀ a : M, q*a=a*q)
    (V : ℂ → M →ₗ[ℂ] M)
    (hinv : ∀ (z : ℂ) (x : M), centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (V z x)=0)
    (hnegative : ∀ (z : ℂ) (x : M), V (-z) (V z x)=x) :
    NegativeInverseFamily (fun z => finiteBlock q hq hqc (V z)) := by
  intro z a
  have hc : (V (-z)).comp (V z)=LinearMap.id := by
    apply LinearMap.ext
    exact hnegative z
  calc
    finiteBlock q hq hqc (V (-z)) (finiteBlock q hq hqc (V z) a)=
        finiteBlock q hq hqc ((V (-z)).comp (V z)) a :=
      congrArg (fun L : Corner q hq →ₗ[ℂ] Corner q hq => L a)
        (finiteBlock_comp q hq hqc (V (-z)) (V z) (hinv (-z))).symm
    _=a := by rw [hc,finiteBlock_id]; rfl

open BidualFoundation UniversalWeakClosure CoefficientPredual OperatorExtension
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] predualNormedGroup predualNormedSpace orderedA starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder

variable {A : Type*} [CStarAlgebra A]

local instance modelOrder : PartialOrder (algebra A) :=
  CStarAlgebra.spectralOrder (algebra A)
local instance modelStarOrder : StarOrderedRing (algebra A) :=
  CStarAlgebra.spectralOrderedRing (algebra A)

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem lift_exp_negative_apply (δ : A →L[ℂ] A) (z : ℂ) (x : algebra A) :
    lift (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A)
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) x)=x := by
  have hh := congrArg (fun T : algebra A →L[ℂ] algebra A => T x)
    (lift_exp_group δ (-z) z)
  have h0 : lift (NormedSpace.exp (((-z)+z) • δ) : A →L[ℂ] A) x=x := by
    rw [neg_add_cancel]
    exact EntireAssembly.lift_exp_zero_apply_fast δ x
  exact hh.symm.trans h0

theorem universal_finiteBlock_negative_family
    (q : algebra A) (hq : IsStarProjection q)
    (hqc : ∀ a : algebra A, q*a=a*q) (hfinite : FiniteAlgebra (Corner q hq))
    (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) :
    NegativeInverseFamily (fun z => finiteBlock q hq hqc
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)).toLinearMap) :=
  finiteBlock_negative_family q hq hqc
    (fun z => (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)).toLinearMap)
    (universal_compression_kernel_invariant q hq hqc hfinite δ hRad)
    (lift_exp_negative_apply δ)

theorem universal_finiteBlock_negative_inverse
    (q : algebra A) (hq : IsStarProjection q)
    (hqc : ∀ a : algebra A, q*a=a*q) (hfinite : FiniteAlgebra (Corner q hq))
    (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z : ℂ) (a : Corner q hq) :
    finiteBlock q hq hqc (lift (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A)).toLinearMap
      (finiteBlock q hq hqc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)).toLinearMap a)=a ∧
    finiteBlock q hq hqc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)).toLinearMap
      (finiteBlock q hq hqc (lift (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A)).toLinearMap a)=a := by
  have hK := universal_finiteBlock_negative_family q hq hqc hfinite δ hRad
  exact ⟨hK z a,negativeInverseFamily_right _ hK z a⟩

end SpectralIsometry.FiniteQuotientInverse

