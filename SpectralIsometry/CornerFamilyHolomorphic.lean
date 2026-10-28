module

public import SpectralIsometry.FiniteQuotientAssembly
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Corner Family Holomorphic

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.CornerFamilyHolomorphic

section GenericSandwich
variable {𝕜 D E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

def sandwichL (C : F →L[𝕜] G) (I : E →L[𝕜] D) :
    (D →L[𝕜] F) →L[𝕜] (E →L[𝕜] G) :=
  (ContinuousLinearMap.compL 𝕜 E F G C).comp
    ((ContinuousLinearMap.compL 𝕜 E D F).flip I)

@[simp] theorem sandwichL_apply (C : F →L[𝕜] G) (I : E →L[𝕜] D)
    (V : D →L[𝕜] F) : sandwichL C I V=C.comp (V.comp I) := rfl

theorem differentiable_sandwich (C : F →L[𝕜] G) (I : E →L[𝕜] D)
    {V : 𝕜 → (D →L[𝕜] F)} (hV : Differentiable 𝕜 V) :
    Differentiable 𝕜 (fun z => C.comp ((V z).comp I)) :=
  (sandwichL C I).differentiable.comp hV
end GenericSandwich

open OAI.HochschildCorners
open SpectralIsometry.FiniteQuotientAssembly

section AbstractCorners
variable {M : Type*} [CStarAlgebra M]

def crossBlockCLM (p : M) (hp : IsStarProjection p) (hpc : ∀ a : M, p*a=a*p)
    (q : M) (hq : IsStarProjection q) (V : M →L[ℂ] M) :
    Corner q hq →L[ℂ] Corner p hp :=
  (OAI.BoundedHochschild.CentralCorner.compressMap p hp hpc).comp
    (V.comp (OAI.BoundedHochschild.CentralCorner.includeMap q hq))

@[simp] theorem crossBlockCLM_coe (p : M) (hp : IsStarProjection p)
    (hpc : ∀ a : M, p*a=a*p) (q : M) (hq : IsStarProjection q)
    (V : M →L[ℂ] M) (a : Corner q hq) :
    (crossBlockCLM p hp hpc q hq V a : M)=p*V (a:M) := rfl

theorem centralBlockCLM_differentiable (p : M) (hp : IsStarProjection p)
    (hpc : ∀ a : M, p*a=a*p) {V : ℂ → (M →L[ℂ] M)}
    (hV : Differentiable ℂ V) :
    Differentiable ℂ (fun z => centralBlockCLM p hp hpc (V z)) :=
  differentiable_sandwich (OAI.BoundedHochschild.CentralCorner.compressMap p hp hpc)
    (OAI.BoundedHochschild.CentralCorner.includeMap p hp) hV

theorem crossBlockCLM_differentiable (p : M) (hp : IsStarProjection p)
    (hpc : ∀ a : M, p*a=a*p) (q : M) (hq : IsStarProjection q)
    {V : ℂ → (M →L[ℂ] M)} (hV : Differentiable ℂ V) :
    Differentiable ℂ (fun z => crossBlockCLM p hp hpc q hq (V z)) :=
  differentiable_sandwich (OAI.BoundedHochschild.CentralCorner.compressMap p hp hpc)
    (OAI.BoundedHochschild.CentralCorner.includeMap q hq) hV
end AbstractCorners

section ActualUniversalModel
open SpectralIsometry.BidualFoundation
open UniversalWeakClosure OperatorExtension
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] predualNormedGroup predualNormedSpace
variable {A : Type*} [CStarAlgebra A]

/-- Full operator-norm holomorphy of the actual R family; the restriction
interpretation needs the separately proved finite-complement invariance. -/
theorem universal_complementBlock_operator_differentiable
    (p : algebra A) (hp : IsStarProjection p)
    (hpc : ∀ a : algebra A, p*a=a*p) (δ : A →L[ℂ] A) :
    Differentiable ℂ (fun z : ℂ => centralBlockCLM p hp hpc
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))) :=
  centralBlockCLM_differentiable p hp hpc (differentiable_lift_exp δ)

/-- Full operator-norm holomorphy of the literal finite-to-infinite L block. -/
theorem universal_crossBlock_operator_differentiable
    (p : algebra A) (hp : IsStarProjection p)
    (hpc : ∀ a : algebra A, p*a=a*p) (q : algebra A) (hq : IsStarProjection q)
    (δ : A →L[ℂ] A) :
    Differentiable ℂ (fun z : ℂ => crossBlockCLM p hp hpc q hq
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))) :=
  crossBlockCLM_differentiable p hp hpc q hq (differentiable_lift_exp δ)
end ActualUniversalModel

end SpectralIsometry.CornerFamilyHolomorphic

