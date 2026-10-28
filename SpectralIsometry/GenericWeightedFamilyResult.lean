module
public import SpectralIsometry.NormalCornerFamilyJordan
public import SpectralIsometry.OffDiagonalFamily

/-!
# Generic Weighted Family Result

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology OAI.HochschildCorners

namespace SpectralIsometry.WeightedFamilyResult
open StrongStarApproximation

def UnitalSquares {E : Type*} [CStarAlgebra E] (R : ℂ → E →L[ℂ] E) : Prop :=
  (∀ z : ℂ, R z 1=1) ∧ ∀ (z : ℂ) (a : E), R z (a^2)=(R z a)^2

section NormalCorner
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem corner_family_result (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : ℂ → Corner p hp →L[ℂ] Corner p hp)
    (hR : ∀ z : ℂ, SquareZeroPreserver.PreservesSquareZero (R z).toLinearMap)
    (honto : ∀ z : ℂ, Function.Surjective (R z))
    (r s : Corner p hp) (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0)
    (hseq : ∀ (z : ℂ) (a : ℕ → Corner p hp) (b : Corner p hp), (∀ n, ‖a n‖≤1) →
      StrongStarTendsto (fun n => ((a n:M):H →L[ℂ] H)) atTop ((b:M):H →L[ℂ] H) →
      StrongStarTendsto (fun n => ((R z (a n):M):H →L[ℂ] H)) atTop ((R z b:M):H →L[ℂ] H))
    (hhol : Differentiable ℂ (fun z : ℂ => R z 1))
    (hreal : ∀ z : ℂ, ∀ ζ∈spectrum ℂ (R z 1:M), ζ.im=0)
    (hzero : R 0 1=1) : UnitalSquares R :=
  SquareZeroPreserver.corner_family_preserves_squares M p hp R hR honto
    r s hr hs hrs hseq hhol hreal hzero
end NormalCorner

theorem offDiagonal_zero {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    (R : ℂ → E ≃L[ℂ] E) (L : ℂ → F →L[ℂ] E)
    (hR : UnitalSquares (fun z => (R z).toContinuousLinearMap))
    (hinv : ∀ (z : ℂ) (a : E), R z (R (-z) a)=a)
    (hRh : Differentiable ℂ (fun z => (R z).toContinuousLinearMap))
    (hLh : Differentiable ℂ L)
    (hreal : ∀ (z : ℂ) (a : E), IsSelfAdjoint a → ∀ f : F, IsSelfAdjoint f →
      ∀ ζ∈spectrum ℂ (R z a+L z f), ζ.im=0)
    (hzero : L 0=0) : ∀ z : ℂ, L z=0 :=
  OffDiagonalFamily.offDiagonal_family_eq_zero R L hR.1 hR.2 hinv hRh hLh hreal hzero

end SpectralIsometry.WeightedFamilyResult

