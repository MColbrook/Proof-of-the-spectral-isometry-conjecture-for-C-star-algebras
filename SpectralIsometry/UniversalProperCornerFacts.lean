module
public import SpectralIsometry.UniversalExponentialProperties
public import SpectralIsometry.GenericCornerLift
public import SpectralIsometry.GenericCentralBlockIdentities
public import SpectralIsometry.FiniteQuotientAssembly

/-!
# Universal Proper Corner Facts

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology OAI.HochschildCorners OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.EntireAssembly
open BidualFoundation UniversalWeakClosure CoefficientPredual OperatorExtension
open FiniteQuotientAssembly StrongStarApproximation
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA predualNormedGroup predualNormedSpace
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder
variable {A : Type*} [CStarAlgebra A]
local instance (priority := 3000) factsModelOrder : PartialOrder (algebra A) :=
  CStarAlgebra.spectralOrder (algebra A)
local instance (priority := 3000) factsModelLE : LE (algebra A) :=
  (factsModelOrder (A:=A)).toLE
local instance (priority := 3000) factsModelStarOrder : StarOrderedRing (algebra A) :=
  CStarAlgebra.spectralOrderedRing (algebra A)
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

theorem universal_complement_squareZero
    (p q : algebra A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : algebra A, p*a=a*p) (hqc : ∀ a : algebra A, q*a=a*q)
    (hsum : p+q=1) (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hRad : ∀ z : ℂ, PreservesRadius (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z : ℂ) : SquareZeroPreserver.PreservesSquareZero
      (centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))).toLinearMap := by
  exact GenericCentralBlockIdentities.corner_square_zero_of_coe p hp
    (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))
    (centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)))
    (universal_complementBlock_coe p q hp hq hpc hqc hsum hfinite δ hRad z)
    (lift_exp_squareZero δ h1 hRad z)

theorem universal_complement_surjective
    (p q : algebra A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : algebra A, p*a=a*p) (hqc : ∀ a : algebra A, q*a=a*q)
    (hsum : p+q=1) (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z : ℂ) : Function.Surjective
      (centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))) := by
  intro a
  refine ⟨centralBlockCLM p hp hpc (lift (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A)) a,?_⟩
  have hh := universal_complementBlock_inverse p q hp hq hpc hqc hsum hfinite δ hRad (-z) a
  simpa only [neg_neg] using hh

theorem universal_complement_strongStar
    (p q : algebra A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : algebra A, p*a=a*p) (hqc : ∀ a : algebra A, q*a=a*q)
    (hsum : p+q=1) (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z : ℂ) (a : ℕ → Corner p hp) (b : Corner p hp)
    (ha : StrongStarTendsto (fun n => ((a n:algebra A):Hilbert A →L[ℂ] Hilbert A))
      atTop ((b:algebra A):Hilbert A →L[ℂ] Hilbert A)) :
    StrongStarTendsto (fun n => ((centralBlockCLM p hp hpc
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) (a n):algebra A):Hilbert A →L[ℂ] Hilbert A))
      atTop ((centralBlockCLM p hp hpc
        (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) b:algebra A):Hilbert A →L[ℂ] Hilbert A) := by
  exact EntireAssemblyGeneric.restriction_strongStarTendsto (H:=Hilbert A) (algebra A) p hp
    (centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)))
    (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))
    (universal_complementBlock_coe p q hp hq hpc hqc hsum hfinite δ hRad z) a b
    (UniversalSquareZeroExtension.lift_strongStarTendsto
      (NormedSpace.exp (z • δ) : A →L[ℂ] A) (fun n => (a n:algebra A)) (b:algebra A) ha)

theorem universal_complement_weight_real
    (p q : algebra A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : algebra A, p*a=a*p) (hqc : ∀ a : algebra A, q*a=a*q)
    (hsum : p+q=1) (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hRad : ∀ z : ℂ, PreservesRadius (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z ζ : ℂ) (hζ : ζ∈spectrum ℂ (centralBlockCLM p hp hpc
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) 1:algebra A)) : ζ.im=0 := by
  rw [universal_complementBlock_weight p q hp hq hpc hqc hsum hfinite δ hRad] at hζ
  exact lift_exp_real_spectrum δ h1 hRad z p hp.isSelfAdjoint ζ hζ

theorem universal_complement_weight_zero
    (p q : algebra A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : algebra A, p*a=a*p) (hqc : ∀ a : algebra A, q*a=a*q)
    (hsum : p+q=1) (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) :
    centralBlockCLM p hp hpc (lift (NormedSpace.exp ((0:ℂ) • δ) : A →L[ℂ] A)) 1=1 := by
  apply Subtype.ext
  exact (universal_complementBlock_weight p q hp hq hpc hqc hsum hfinite δ hRad 0).trans
    (lift_exp_zero_apply_fast δ p)

end SpectralIsometry.EntireAssembly

