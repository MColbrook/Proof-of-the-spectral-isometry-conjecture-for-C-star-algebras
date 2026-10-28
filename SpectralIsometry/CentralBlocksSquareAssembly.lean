module

public import SpectralIsometry.CornerFamilyHolomorphic

/-!
# Central Blocks Square Assembly

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open OAI.HochschildCorners

namespace SpectralIsometry.CentralBlocksSquareAssembly

open FiniteQuotientAssembly CornerFamilyHolomorphic
variable {M : Type*} [CStarAlgebra M]

theorem complementary_compressions_separate (p q : M)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : M, p*a=a*p) (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1)
    (x y : M) (hx : centralCompressionHom p hp hpc x=centralCompressionHom p hp hpc y)
    (hy : centralCompressionHom q hq hqc x=centralCompressionHom q hq hqc y) : x=y := by
  have hpx : p*x=p*y := congrArg Subtype.val hx
  have hqx : q*x=q*y := congrArg Subtype.val hy
  calc
    x=(p+q)*x := by rw [hsum,one_mul]
    _=(p+q)*y := by rw [add_mul,add_mul,hpx,hqx]
    _=y := by rw [hsum,one_mul]

theorem first_compression_kernel_invariant (p q : M)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : M, p*a=a*p) (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1)
    (V : M →L[ℂ] M) (hL : crossBlockCLM p hp hpc q hq V=0)
    (x : M) (hx : centralCompressionHom p hp hpc x=0) :
    centralCompressionHom p hp hpc (V x)=0 := by
  have hsum' : q+p=1 := (add_comm q p).trans hsum
  have hqx : q*x=x := complement_projection_mul_of_kernel q p hp hpc hsum' x hx
  let a : Corner q hq := ⟨x,hqx,by rw [←hqc x,hqx]⟩
  have ha := congrArg (fun F : Corner q hq →L[ℂ] Corner p hp => F a) hL
  exact ha

theorem preserves_squares (p q : M)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : M, p*a=a*p) (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1)
    (V : M →L[ℂ] M)
    (hqinv : ∀ x : M, centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (V x)=0)
    (hR : ∀ a : Corner p hp, centralBlockCLM p hp hpc V (a^2)=
      (centralBlockCLM p hp hpc V a)^2)
    (hL : crossBlockCLM p hp hpc q hq V=0)
    (hK : ∀ a : Corner q hq, finiteBlock q hq hqc V.toLinearMap (a^2)=
      (finiteBlock q hq hqc V.toLinearMap a)^2) :
    ∀ x : M, V (x^2)=(V x)^2 := by
  have hpinv := first_compression_kernel_invariant p q hp hq hpc hqc hsum V hL
  have hRp (a : Corner p hp) : finiteBlock p hp hpc V.toLinearMap (a^2)=
      (finiteBlock p hp hpc V.toLinearMap a)^2 := hR a
  intro x
  apply complementary_compressions_separate p q hp hq hpc hqc hsum
  · calc
      centralCompressionHom p hp hpc (V (x^2))=
          finiteBlock p hp hpc V.toLinearMap (centralCompressionHom p hp hpc (x^2)) :=
        (finiteBlock_compression p hp hpc V.toLinearMap hpinv (x^2)).symm
      _=finiteBlock p hp hpc V.toLinearMap ((centralCompressionHom p hp hpc x)^2) := by rw [map_pow]
      _=(finiteBlock p hp hpc V.toLinearMap (centralCompressionHom p hp hpc x))^2 := hRp _
      _=(centralCompressionHom p hp hpc (V x))^2 := by
        rw [finiteBlock_compression p hp hpc V.toLinearMap hpinv]
        rfl
      _=centralCompressionHom p hp hpc ((V x)^2) := (map_pow _ _ _).symm
  · calc
      centralCompressionHom q hq hqc (V (x^2))=
          finiteBlock q hq hqc V.toLinearMap (centralCompressionHom q hq hqc (x^2)) :=
        (finiteBlock_compression q hq hqc V.toLinearMap hqinv (x^2)).symm
      _=finiteBlock q hq hqc V.toLinearMap ((centralCompressionHom q hq hqc x)^2) := by rw [map_pow]
      _=(finiteBlock q hq hqc V.toLinearMap (centralCompressionHom q hq hqc x))^2 := hK _
      _=(centralCompressionHom q hq hqc (V x))^2 := by
        rw [finiteBlock_compression q hq hqc V.toLinearMap hqinv]
        rfl
      _=centralCompressionHom q hq hqc ((V x)^2) := (map_pow _ _ _).symm

end SpectralIsometry.CentralBlocksSquareAssembly

