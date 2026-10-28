module

public import SpectralIsometry.CentralBlocksSquareAssembly
public import SpectralIsometry.GenericWeightedFamilyResult

/-!
# Square Family Assembly

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open OAI.HochschildCorners

namespace SpectralIsometry.SquareFamilyAssembly

open FiniteQuotientAssembly CornerFamilyHolomorphic

def SquaresFamily {E : Type*} [CStarAlgebra E]
    (V : ℂ → E →L[ℂ] E) : Prop :=
  ∀ (z : ℂ) (a : E), V z (a ^ 2) = (V z a) ^ 2

theorem unitalSquares_squares {E : Type*} [CStarAlgebra E]
    (R : ℂ → E →L[ℂ] E) (hR : WeightedFamilyResult.UnitalSquares R) :
    SquaresFamily R := hR.2

theorem central_family_squares {M : Type*} [CStarAlgebra M]
    (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : M, p*a=a*p) (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1)
    (V : ℂ → M →L[ℂ] M)
    (hqinv : ∀ (z : ℂ) (x : M), centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (V z x)=0)
    (hR : WeightedFamilyResult.UnitalSquares
      (fun z => centralBlockCLM p hp hpc (V z)))
    (hL : ∀ z : ℂ, crossBlockCLM p hp hpc q hq (V z)=0)
    (hK : ∀ z : ℂ, IsJordanIsomorphism
      (finiteBlock q hq hqc (V z).toLinearMap)) :
    SquaresFamily V := by
  intro z x
  exact CentralBlocksSquareAssembly.preserves_squares p q hp hq hpc hqc hsum
    (V z) (hqinv z) (hR.2 z) (hL z) (hK z).2 x

theorem faithful_algHom_descent {A M : Type*} [CStarAlgebra A] [CStarAlgebra M]
    (j : A →ₐ[ℂ] M) (hj : Function.Injective j)
    (U : ℂ → A →L[ℂ] A) (V : ℂ → M →L[ℂ] M)
    (hV : SquaresFamily V)
    (hcompat : ∀ (z : ℂ) (a : A), V z (j a)=j (U z a)) :
    SquaresFamily U := by
  intro z a
  apply hj
  calc
    j (U z (a^2)) = V z (j (a^2)) := (hcompat z (a^2)).symm
    _ = V z ((j a)^2) := by rw [map_pow]
    _ = (V z (j a))^2 := hV z (j a)
    _ = (j (U z a))^2 := by rw [hcompat]
    _ = j ((U z a)^2) := (map_pow j (U z a) 2).symm

theorem exp_derivation_of_squaresFamily {A : Type*} [CStarAlgebra A]
    (δ : A →L[ℂ] A)
    (hδ : SquaresFamily (fun z => (NormedSpace.exp (z • δ) : A →L[ℂ] A))) :
    ∀ a b : A, δ (a*b)=δ a*b+a*δ b :=
  (exp_squares_iff_derivation δ).mp hδ

end SpectralIsometry.SquareFamilyAssembly

